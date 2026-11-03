module

public import SteinerUpperBound.Matching.Padded.CausalSampler
public import SteinerUpperBound.Matching.Padded.Oracle

@[expose] public section

/-!
# Causal metric/retention frontend

Slot replies are obtained from the supplied `Code` callbacks and are used
directly by the continuation. No runtime expression in this module evaluates
`Slots.test`; that function occurs only in the refinement contract.
-/

namespace SteinerUpperBound.Matching.Padded.CausalAccess

open SteinerLowerBound
open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical

abbrev Code := SteinerUpperBound.QueryProgram.Code

variable {V E M T : Type*} {G : Graph V E}

structure Primitives (S : Slots G) where
  slot : Slot S.length → Code M T (Option (E × Slot S.length))
  prepare : V → Code M T Unit

namespace Primitives

variable {S : Slots G}

def Correct (I : Primitives (M := M) (T := T) S) (m : M → ℝ) (b : T → Bool) : Prop :=
  ∀ s f, Causal.expect m b (I.slot s) f = f (S.test s)

end Primitives

variable (S : Slots G) (Q : ℕ) (hQ : 0 < Q) (I : Primitives (M := M) (T := T) S)

noncomputable def selectedStep (a b : ℕ) (v : V) (i : ℕ) (s : Cache S Q) :
    Code M T (Option (Entry S Q)) :=
  if hi : i < S.length v then
    let source : Slot S.length := ⟨v, ⟨i, hi⟩⟩
    (I.slot source).bind fun hit =>
      match hit with
      | none => .pure none
      | some (e, reverse) =>
        Causal.spend 12
          (if s.assigned e = none ∧ Cache.boundary S Q s reverse.1 ≤ a then
            (Causal.compile (Range.sample Q hQ a b)).bind fun r =>
              .pure (some ⟨source, reverse, e, r⟩)
          else .pure none)
  else .pure none

noncomputable def collectStep (a b : ℕ) (v : V) (s : Cache S Q)
    (i : ℕ) (entries : List (Entry S Q)) : Code M T (List (Entry S Q)) :=
  (selectedStep S Q hQ I a b v i s).bind fun hit =>
    Causal.spend 2 (.pure (Cache.addEntry entries hit))

noncomputable def forEach {A B : Type*} (step : A → B → Code M T B) :
    List A → B → Code M T B
  | [], s => .pure s
  | x :: xs, s => (step x s).bind fun s' => forEach step xs s'

noncomputable def collect (a b : ℕ) (v : V) (s : Cache S Q) :
    Code M T (List (Entry S Q)) :=
  (Causal.compile (Sparse.sample (1 - Range.probability Q a b) (S.length v) 0)).bind fun selected =>
    forEach (collectStep S Q hQ I a b v s) selected []

noncomputable def extend (sortHeight : ℕ) (v : V) (s : Cache S Q) : Code M T (Cache S Q) :=
  let a := Cache.boundary S Q s v
  let b := Buckets.bound (s.level v + 1)
  if b ≤ Q then
    (collect S Q hQ I a b v s).bind fun entries =>
      let r := Cache.finish S Q sortHeight v s entries
      Causal.spend r.operations (.pure r.value)
  else .pure s

noncomputable def nextLoop (S : Slots G) (Q : ℕ) (hQ : 0 < Q)
    (I : Primitives (M := M) (T := T) S) (sortHeight : ℕ) (v : V) (cursor : ℕ) :
    ℕ → Cache S Q → Code M T (Option (Entry S Q) × Cache S Q)
  | 0, s => .pure (none, s)
  | fuel + 1, s =>
    Causal.spend 6
      (match (s.ready v)[cursor]? with
      | some x =>
        if x.rank.val < Cache.boundary S Q s v then .pure (some x, s) else
          if Cache.boundary S Q s v < Q then
            (extend S Q hQ I sortHeight v s).bind fun s' =>
              nextLoop S Q hQ I sortHeight v cursor fuel s'
          else .pure (none, s)
      | none =>
        if Cache.boundary S Q s v < Q then
          (extend S Q hQ I sortHeight v s).bind fun s' =>
            nextLoop S Q hQ I sortHeight v cursor fuel s'
        else .pure (none, s))

noncomputable def next (sortHeight maxLevel : ℕ) (v : V) (cursor : ℕ) (s : Cache S Q) :
    Code M T (Option (Entry S Q) × Cache S Q) :=
  let s' := { s with requests := Function.update s.requests v (s.requests v + 1) }
  if s.prepared v then nextLoop S Q hQ I sortHeight v cursor (maxLevel + 1) s'
  else (I.prepare v).bind fun _ =>
    nextLoop S Q hQ I sortHeight v cursor (maxLevel + 1)
      { s' with prepared := Function.update s'.prepared v true }

variable [Fintype V] (P : Parameters S)

noncomputable def scan (S : Slots G) (P : Parameters S)
    (I : Primitives (M := M) (T := T) S)
    (call : Entry S P.rankCard → Cache S P.rankCard → Memo E →
      Code M T (LocalRun S P.rankCard Bool))
    (v : V) (cutoff cursor : ℕ) :
    ℕ → Cache S P.rankCard → Memo E →
      Code M T (LocalRun S P.rankCard (Option (Entry S P.rankCard)))
  | 0, s, μ => .pure ⟨none, μ, s, []⟩
  | fuel + 1, s, μ =>
    (next S P.rankCard P.rankCard_pos I P.sortHeight (P.rankExponent + 1) v cursor s).bind
      fun answer =>
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

noncomputable def edge (S : Slots G) (P : Parameters S)
    (I : Primitives (M := M) (T := T) S)
    (d : Directed E) (rank : Fin P.rankCard) (ancestors : List (Directed E))
    (s : Cache S P.rankCard) (μ : Memo E) : Code M T (LocalRun S P.rankCard Bool) :=
  Causal.spend 3
    (match μ d with
    | some b => .pure ⟨b, μ, s, [⟨d, ancestors, true⟩]⟩
    | none =>
      (scan S P I
        (fun x t ν =>
          if _hr : x.rank.val < rank.val then
            edge S P I (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν
          else .pure ⟨false, ν, t, []⟩)
        (G.head d) rank.val 0 (P.Nstar + 1) s μ).bind fun r =>
          Causal.spend 3
            (.pure ⟨r.value.isNone, Function.update r.memo d (some r.value.isNone), r.cache,
              ⟨d, ancestors, false⟩ :: r.calls⟩))
termination_by rank.val
decreasing_by exact _hr

noncomputable def vertex (v : V) : Code M T (LocalRun S P.rankCard (Option E)) :=
  Causal.spend (P.rankExponent + P.sortHeight + 12)
    ((scan S P I (fun x s μ => edge S P I (G.away v x.edge) x.rank [] s μ)
      v P.rankCard 0 (P.Nstar + 1) (Cache.empty S P.rankCard) (fun _ => none)).bind fun r =>
        .pure ⟨r.value.map Entry.edge, r.memo, r.cache, r.calls⟩)

end SteinerUpperBound.Matching.Padded.CausalAccess
