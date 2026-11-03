module

public import SteinerUpperBound.Matching.Padded.RawCausal

@[expose] public section

/-!
# Ambient-identifier causal runtime

Neither vertex identifiers nor copy identifiers assert membership in the
unknown graph. In particular, counterfactual metric replies never have to
construct a proof that a returned component root belongs to the true graph.
-/

namespace SteinerUpperBound.Matching.Padded.Runtime

open scoped Classical

abbrev Code := SteinerUpperBound.QueryProgram.Code

variable {Vertex Label M T : Type*}

structure Config (Vertex : Type*) where
  length : Vertex → ℕ
  Nstar : ℕ

namespace Config

def logarithm (C : Config Vertex) : ℕ := Nat.log 2 C.Nstar + 1
def rankExponent (C : Config Vertex) : ℕ := 32 * C.logarithm
def rankCard (C : Config Vertex) : ℕ := 2 ^ C.rankExponent
def sortHeight (C : Config Vertex) : ℕ := C.logarithm

theorem rankCard_pos (C : Config Vertex) : 0 < C.rankCard := pow_pos (by decide) _

end Config

abbrev Primitives (length : Vertex → ℕ) (Label M T : Type*) :=
  RawCausal.Primitives length Label M T

variable (C : Config Vertex) (I : Primitives C.length Label M T)

abbrev State := RawCausal.Cache C.length Label C.rankCard I.Memory
abbrev Copy := RawCausal.Entry C.length Label C.rankCard
abbrev Result (A : Type*) := RawCausal.Run C.length Label C.rankCard I.Memory A

def empty : State C I :=
  ⟨fun _ => 0, fun _ => none, fun _ => none, fun _ => [], fun _ => #[],
    fun _ => false, fun _ => 0, I.initial⟩

def boundary (s : State C I) (v : Vertex) : ℕ := Buckets.bound (s.level v)

noncomputable def assign (s : State C I) (x : Copy C (Label := Label)) : State C I :=
  { s with
    assigned := Function.update s.assigned x.label (some x.rank)
    stored := Function.update (Function.update s.stored x.source (some x.rank)) x.reverse (some x.rank)
    known := Function.update
      (Function.update s.known x.source.1 (x :: s.known x.source.1))
      x.reverse.1 (⟨x.reverse, x.source, x.label, x.rank⟩ :: s.known x.reverse.1) }

noncomputable def selectedStep (a b : ℕ) (v : Vertex) (i : ℕ) (s : State C I) (memory : I.Memory) :
    Code M T (Option (Copy C (Label := Label)) × I.Memory) :=
  if hi : i < C.length v then
    let source : Slot C.length := ⟨v, ⟨i, hi⟩⟩
    (I.slot source memory).bind fun answer =>
      match answer.1 with
      | none => .pure (none, answer.2)
      | some (e, reverse) =>
        Causal.spend 12
          (if s.assigned e = none ∧ boundary C I s reverse.1 ≤ a then
            (Causal.compile (Range.sample C.rankCard C.rankCard_pos a b)).bind fun r =>
              .pure (some ⟨source, reverse, e, r⟩, answer.2)
          else .pure (none, answer.2))
  else .pure (none, memory)

noncomputable def collectStep (a b : ℕ) (v : Vertex) (s : State C I)
    (i : ℕ) (acc : List (Copy C (Label := Label)) × I.Memory) :
    Code M T (List (Copy C (Label := Label)) × I.Memory) :=
  (selectedStep C I a b v i s acc.2).bind fun answer =>
    Causal.spend 2 (.pure (Cache.addEntry acc.1 answer.1, answer.2))

noncomputable def collect (a b : ℕ) (v : Vertex) (s : State C I) :
    Code M T (List (Copy C (Label := Label)) × I.Memory) :=
  (Causal.compile (Sparse.sample (1 - Range.probability C.rankCard a b) (C.length v) 0)).bind
    (fun selected => RawCausal.forEach (collectStep C I a b v s) selected ([], s.memory))

noncomputable def finish (v : Vertex) (s : State C I) (memory : I.Memory)
    (entries : List (Copy C (Label := Label))) : Arithmetic (State C I) :=
  let t := entries.foldl (assign C I) { s with memory := memory }
  let sorted := Sort.array (fun x y : Copy C (Label := Label) =>
    decide (x.rank.val ≤ y.rank.val)) C.sortHeight (t.known v)
  ⟨{ t with level := Function.update t.level v (s.level v + 1),
            ready := Function.update t.ready v sorted.value },
    32 * entries.length + sorted.operations + 4⟩

noncomputable def extend (v : Vertex) (s : State C I) : Code M T (State C I) :=
  let a := boundary C I s v
  let b := Buckets.bound (s.level v + 1)
  if b ≤ C.rankCard then
    (collect C I a b v s).bind fun result =>
      let completed := finish C I v s result.2 result.1
      Causal.spend completed.operations (.pure completed.value)
  else .pure s

noncomputable def available (v : Vertex) (cursor : ℕ) (s : State C I) :
    Option (Copy C (Label := Label)) :=
  ((s.ready v)[cursor]?).bind
    (fun x => if x.rank.val < boundary C I s v then some x else none)

noncomputable def nextLoop (C : Config Vertex) (I : Primitives C.length Label M T)
    (v : Vertex) (cursor : ℕ) :
    ℕ → State C I → Code M T (Option (Copy C (Label := Label)) × State C I)
  | 0, s => .pure (none, s)
  | fuel + 1, s =>
    Causal.spend 6
      (match available C I v cursor s with
      | some x => .pure (some x, s)
      | none =>
        if boundary C I s v < C.rankCard then
          (extend C I v s).bind fun s' => nextLoop C I v cursor fuel s'
        else .pure (none, s))

noncomputable def next (v : Vertex) (cursor : ℕ) (s : State C I) :
    Code M T (Option (Copy C (Label := Label)) × State C I) :=
  let s' := { s with requests := Function.update s.requests v (s.requests v + 1) }
  if s.prepared v then nextLoop C I v cursor (C.rankExponent + 2) s'
  else (I.prepare v s.memory).bind fun memory =>
    nextLoop C I v cursor (C.rankExponent + 2)
      { s' with prepared := Function.update s'.prepared v true, memory := memory }

noncomputable def scan (C : Config Vertex) (I : Primitives C.length Label M T)
    (call : Copy C (Label := Label) → State C I →
      (Label × Vertex → Option Bool) → Code M T (Result C I Bool))
    (v : Vertex) (cutoff cursor : ℕ) :
    ℕ → State C I → (Label × Vertex → Option Bool) →
      Code M T (Result C I (Option (Copy C (Label := Label))))
  | 0, s, μ => .pure ⟨none, μ, s, []⟩
  | fuel + 1, s, μ =>
    (next C I v cursor s).bind fun answer =>
      match answer.1 with
      | none => .pure ⟨none, μ, answer.2, []⟩
      | some x =>
        if x.rank.val < cutoff then
          (call x answer.2 μ).bind fun r =>
            if r.value then .pure ⟨some x, r.memo, r.cache, r.calls⟩ else
              (scan C I call v cutoff (cursor + 1) fuel r.cache r.memo).bind fun t =>
                Causal.spend (r.calls.length + 4)
                  (.pure ⟨t.value, t.memo, t.cache, r.calls ++ t.calls⟩)
        else .pure ⟨none, μ, answer.2, []⟩

noncomputable def edge (C : Config Vertex) (I : Primitives C.length Label M T)
    (e : Label) (head : Vertex) (rank : Fin C.rankCard) (ancestors : List (Label × Vertex))
    (s : State C I) (μ : Label × Vertex → Option Bool) : Code M T (Result C I Bool) :=
  Causal.spend 3
    (match μ (e, head) with
    | some b => .pure ⟨b, μ, s, [⟨(e, head), ancestors, true⟩]⟩
    | none =>
      (scan C I (fun x t ν =>
        if _hr : x.rank.val < rank.val then
          edge C I x.label x.reverse.1 x.rank ((e, head) :: ancestors) t ν
        else .pure ⟨false, ν, t, []⟩)
        head rank.val 0 (C.Nstar + 1) s μ).bind fun r =>
          Causal.spend 3
            (.pure ⟨r.value.isNone, Function.update r.memo (e, head) (some r.value.isNone), r.cache,
              ⟨(e, head), ancestors, false⟩ :: r.calls⟩))
termination_by rank.val
decreasing_by exact _hr

noncomputable def vertex (root : Vertex) : Code M T (Result C I (Option Label)) :=
  Causal.spend (C.rankExponent + C.sortHeight + 12)
    ((scan C I (fun x s μ => edge C I x.label x.reverse.1 x.rank [] s μ)
      root C.rankCard 0 (C.Nstar + 1) (empty C I) (fun _ => none)).bind fun r =>
        .pure ⟨r.value.map RawCausal.Entry.label, r.memo, r.cache, r.calls⟩)

noncomputable def answer (root : Vertex) : Code M T (Bool × I.Memory) :=
  (vertex C I root).map (fun r => (r.value.isSome, r.cache.memory))

end SteinerUpperBound.Matching.Padded.Runtime
