module

public import SteinerUpperBound.Matching.Padded.CausalSampler
public import SteinerUpperBound.Matching.Padded.Oracle

@[expose] public section

/-!
# Causal runtime with oracle-independent identifiers

`Label` is an ambient identifier type, not a subtype asserting that a copy is
present in the unknown graph. Consequently a metric/retention callback can be
defined causally on counterfactual replies as well. The true-copy embedding
occurs only in `Primitives.Correct`, never in the runtime.
-/

namespace SteinerUpperBound.Matching.Padded.RawCausal

open SteinerLowerBound
open scoped Classical

abbrev Code := SteinerUpperBound.QueryProgram.Code

variable {V E Label M T : Type*} {G : Graph V E}

structure Entry (length : V → ℕ) (Label : Type*) (Q : ℕ) where
  source : Slot length
  reverse : Slot length
  label : Label
  rank : Fin Q

structure Cache (length : V → ℕ) (Label : Type*) (Q : ℕ) (Memory : Type*) where
  level : V → ℕ
  assigned : Label → Option (Fin Q)
  stored : Slot length → Option (Fin Q)
  known : V → List (Entry length Label Q)
  ready : V → Array (Entry length Label Q)
  prepared : V → Bool
  requests : V → ℕ
  memory : Memory

structure Invocation (Label V : Type*) where
  state : Label × V
  ancestors : List (Label × V)
  cached : Bool

structure Run (length : V → ℕ) (Label : Type*) (Q : ℕ) (Memory A : Type*) where
  value : A
  memo : Label × V → Option Bool
  cache : Cache length Label Q Memory
  calls : List (Invocation Label V)

structure Primitives (length : V → ℕ) (Label M T : Type*) where
  Memory : Type*
  initial : Memory
  slot : Slot length → Memory → Code M T (Option (Label × Slot length) × Memory)
  prepare : V → Memory → Code M T Memory

def Primitives.Correct (S : Slots G) (encode : E ↪ Label)
    (I : Primitives S.length Label M T) (m : M → ℝ) (b : T → Bool)
    (usable : I.Memory → V → Prop) : Prop :=
  ∀ s memory, usable memory s.1 → ∀ (f : Option (Label × Slot S.length) → ℝ),
    Causal.expect m b (I.slot s memory) (fun answer => f answer.1) =
    f ((S.test s).map fun hit => (encode hit.1, hit.2))

variable (S : Slots G) [Fintype V] (P : Parameters S)
variable (I : Primitives S.length Label M T)

abbrev State := Cache S.length Label P.rankCard I.Memory
abbrev Copy := Entry S.length Label P.rankCard

def empty : State S P I :=
  ⟨fun _ => 0, fun _ => none, fun _ => none, fun _ => [], fun _ => #[],
    fun _ => false, fun _ => 0, I.initial⟩

def boundary (s : State S P I) (v : V) : ℕ := Buckets.bound (s.level v)

noncomputable def assign (s : State S P I) (x : Copy S P (Label := Label)) : State S P I :=
  { s with
    assigned := Function.update s.assigned x.label (some x.rank)
    stored := Function.update (Function.update s.stored x.source (some x.rank)) x.reverse (some x.rank)
    known := Function.update
      (Function.update s.known x.source.1 (x :: s.known x.source.1))
      x.reverse.1 (⟨x.reverse, x.source, x.label, x.rank⟩ :: s.known x.reverse.1) }

noncomputable def selectedStep (a b : ℕ) (v : V) (i : ℕ) (s : State S P I) (memory : I.Memory) :
    Code M T (Option (Copy S P (Label := Label)) × I.Memory) :=
  if hi : i < S.length v then
    let source : Slot S.length := ⟨v, ⟨i, hi⟩⟩
    (I.slot source memory).bind fun answer =>
      match answer.1 with
      | none => .pure (none, answer.2)
      | some (e, reverse) =>
        Causal.spend 12
          (if s.assigned e = none ∧ boundary S P I s reverse.1 ≤ a then
            (Causal.compile (Range.sample P.rankCard P.rankCard_pos a b)).bind fun r =>
              .pure (some ⟨source, reverse, e, r⟩, answer.2)
          else .pure (none, answer.2))
  else .pure (none, memory)

noncomputable def forEach {A B : Type*} (step : A → B → Code M T B) :
    List A → B → Code M T B
  | [], s => .pure s
  | a :: xs, s => (step a s).bind fun s' => forEach step xs s'

noncomputable def extend (v : V) (s : State S P I) : Code M T (State S P I) :=
  let a := boundary S P I s v
  let b := Buckets.bound (s.level v + 1)
  if b ≤ P.rankCard then
    (Causal.compile (Sparse.sample (1 - Range.probability P.rankCard a b) (S.length v) 0)).bind
      fun selected =>
        (forEach
          (fun i acc => (selectedStep S P I a b v i s acc.2).bind fun answer =>
            Causal.spend 2 (.pure (Padded.Cache.addEntry acc.1 answer.1, answer.2)))
          selected ([], s.memory)).bind fun result =>
            let entries := result.1
            let s' := entries.foldl (assign S P I) { s with memory := result.2 }
            let sorted := Sort.array (fun x y : Copy S P (Label := Label) =>
              decide (x.rank.val ≤ y.rank.val)) P.sortHeight (s'.known v)
            Causal.spend (32 * entries.length + sorted.operations + 4)
              (.pure { s' with level := Function.update s'.level v (s.level v + 1),
                                ready := Function.update s'.ready v sorted.value })
  else .pure s

noncomputable def nextLoop (S : Slots G) (P : Parameters S) (I : Primitives S.length Label M T)
    (v : V) (cursor : ℕ) :
    ℕ → State S P I → Code M T (Option (Copy S P (Label := Label)) × State S P I)
  | 0, s => .pure (none, s)
  | fuel + 1, s =>
    Causal.spend 6
      (match ((s.ready v)[cursor]?).bind
          (fun x => if x.rank.val < boundary S P I s v then some x else none) with
      | some x => .pure (some x, s)
      | none =>
        if boundary S P I s v < P.rankCard then
          (extend S P I v s).bind fun s' => nextLoop S P I v cursor fuel s'
        else .pure (none, s))

noncomputable def next (v : V) (cursor : ℕ) (s : State S P I) :
    Code M T (Option (Copy S P (Label := Label)) × State S P I) :=
  let s' := { s with requests := Function.update s.requests v (s.requests v + 1) }
  if s.prepared v then nextLoop S P I v cursor (P.rankExponent + 2) s'
  else (I.prepare v s.memory).bind fun memory =>
    nextLoop S P I v cursor (P.rankExponent + 2)
      { s' with prepared := Function.update s'.prepared v true, memory := memory }

noncomputable def scan (S : Slots G) (P : Parameters S) (I : Primitives S.length Label M T)
    (call : Copy S P (Label := Label) → State S P I →
      (Label × V → Option Bool) → Code M T (Run S.length Label P.rankCard I.Memory Bool))
    (v : V) (cutoff cursor : ℕ) :
    ℕ → State S P I → (Label × V → Option Bool) →
      Code M T (Run S.length Label P.rankCard I.Memory (Option (Copy S P (Label := Label))))
  | 0, s, μ => .pure ⟨none, μ, s, []⟩
  | fuel + 1, s, μ =>
    (next S P I v cursor s).bind fun answer =>
      match answer.1 with
      | none => .pure ⟨none, μ, answer.2, []⟩
      | some x =>
        if x.rank.val < cutoff then
          (call x answer.2 μ).bind fun r =>
            if r.value then .pure ⟨some x, r.memo, r.cache, r.calls⟩ else
              (scan S P I call v cutoff (cursor + 1) fuel r.cache r.memo).bind fun t =>
                Causal.spend (r.calls.length + 4)
                  (.pure ⟨t.value, t.memo, t.cache, r.calls ++ t.calls⟩)
        else .pure ⟨none, μ, answer.2, []⟩

noncomputable def edge (S : Slots G) (P : Parameters S) (I : Primitives S.length Label M T)
    (e : Label) (head : V) (rank : Fin P.rankCard) (ancestors : List (Label × V))
    (s : State S P I) (μ : Label × V → Option Bool) :
    Code M T (Run S.length Label P.rankCard I.Memory Bool) :=
  Causal.spend 3
    (match μ (e, head) with
    | some b => .pure ⟨b, μ, s, [⟨(e, head), ancestors, true⟩]⟩
    | none =>
      (scan S P I (fun x t ν =>
        if _hr : x.rank.val < rank.val then
          edge S P I x.label x.reverse.1 x.rank ((e, head) :: ancestors) t ν
        else .pure ⟨false, ν, t, []⟩)
        head rank.val 0 (P.Nstar + 1) s μ).bind fun r =>
          Causal.spend 3
            (.pure ⟨r.value.isNone, Function.update r.memo (e, head) (some r.value.isNone), r.cache,
              ⟨(e, head), ancestors, false⟩ :: r.calls⟩))
termination_by rank.val
decreasing_by exact _hr

noncomputable def vertex (v : V) : Code M T (Run S.length Label P.rankCard I.Memory (Option Label)) :=
  Causal.spend (P.rankExponent + P.sortHeight + 12)
    ((scan S P I (fun x s μ => edge S P I x.label x.reverse.1 x.rank [] s μ)
      v P.rankCard 0 (P.Nstar + 1) (empty S P I) (fun _ => none)).bind fun r =>
        .pure ⟨r.value.map Entry.label, r.memo, r.cache, r.calls⟩)

end SteinerUpperBound.Matching.Padded.RawCausal
