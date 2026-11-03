module

public import SteinerUpperBound.Matching.Padded.Plan

@[expose] public section

/-!
# Padded local oracle implementation

No whole-graph edge enumeration or slot-list scan occurs in this program.
`nextLoop` reads a random-access cache and, if necessary, opens a bucket through
the sparse selected-index sampler. The oracle itself uses only these replies.
-/

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E}

structure Parameters (S : Slots G) [Fintype V] where
  Nstar : ℕ
  two_le : 2 ≤ Nstar
  size_le : Fintype.card V + S.totalSlots + 2 ≤ Nstar

namespace Parameters

variable {S : Slots G} [Fintype V]

def logarithm (P : Parameters S) : ℕ := Nat.log 2 P.Nstar + 1
def rankExponent (P : Parameters S) : ℕ := 32 * P.logarithm
def rankCard (P : Parameters S) : ℕ := 2 ^ P.rankExponent
def sortHeight (P : Parameters S) : ℕ := P.logarithm

theorem rankCard_pos (P : Parameters S) : 0 < P.rankCard := pow_pos (by decide) _

end Parameters

namespace Cache

variable (S : Slots G) (Q : ℕ) (hQ : 0 < Q)

noncomputable def available (v : V) (cursor : ℕ) (s : Cache S Q) : Option (Entry S Q) :=
  ((s.ready v)[cursor]?).bind
    (fun x => if x.rank.val < boundary S Q s v then some x else none)

noncomputable def nextLoop (S : Slots G) (Q : ℕ) (hQ : 0 < Q)
    (sortHeight : ℕ) (v : V) (cursor : ℕ) :
    ℕ → Cache S Q → Program (Command S) (Option (Entry S Q) × Cache S Q)
  | 0, s => .ret (none, s)
  | fuel + 1, s =>
    .tick (.oracle 6)
      (match available S Q v cursor s with
      | some x => .ret (some x, s)
      | none =>
        if boundary S Q s v < Q then
          (extend S Q hQ sortHeight v s).bind fun s' =>
            nextLoop S Q hQ sortHeight v cursor fuel s'
        else .ret (none, s))

noncomputable def next (sortHeight maxLevel : ℕ) (v : V) (cursor : ℕ) (s : Cache S Q) :
    Program (Command S) (Option (Entry S Q) × Cache S Q) :=
  let s' := { s with requests := Function.update s.requests v (s.requests v + 1) }
  if s.prepared v then nextLoop S Q hQ sortHeight v cursor (maxLevel + 1) s'
  else .tick (.prepare v)
    (nextLoop S Q hQ sortHeight v cursor (maxLevel + 1)
      { s' with prepared := Function.update s'.prepared v true })

end Cache

structure LocalRun (S : Slots G) (Q : ℕ) (A : Type*) where
  value : A
  memo : Memo E
  cache : Cache S Q
  calls : List (Invocation E)

def LocalRun.mapValue {S : Slots G} {Q : ℕ} {A B : Type*}
    (f : A → B) (r : LocalRun S Q A) : LocalRun S Q B :=
  ⟨f r.value, r.memo, r.cache, r.calls⟩

theorem LocalRun.mapValue_cache {S : Slots G} {Q : ℕ} {A B : Type*}
    (f : A → B) (r : LocalRun S Q A) : (r.mapValue f).cache = r.cache := rfl

namespace Oracle

variable (S : Slots G) [Fintype V] (P : Parameters S)

noncomputable def scan (S : Slots G) (P : Parameters S)
    (call : Entry S P.rankCard → Cache S P.rankCard → Memo E →
      Program (Command S) (LocalRun S P.rankCard Bool))
    (v : V) (cutoff cursor : ℕ) :
    ℕ → Cache S P.rankCard → Memo E →
      Program (Command S) (LocalRun S P.rankCard (Option (Entry S P.rankCard)))
  | 0, s, μ => .ret ⟨none, μ, s, []⟩
  | fuel + 1, s, μ =>
    (Cache.next S P.rankCard P.rankCard_pos P.sortHeight (P.rankExponent + 1) v cursor s).bind
      fun answer =>
        match answer.1 with
        | none => .ret ⟨none, μ, answer.2, []⟩
        | some x =>
          if x.rank.val < cutoff then
            (call x answer.2 μ).bind fun r =>
              if r.value then .ret ⟨some x, r.memo, r.cache, r.calls⟩ else
                (scan S P call v cutoff (cursor + 1) fuel r.cache r.memo).bind fun t =>
                  .tick (.oracle (r.calls.length + 4))
                    (.ret ⟨t.value, t.memo, t.cache, r.calls ++ t.calls⟩)
          else .ret ⟨none, μ, answer.2, []⟩

noncomputable def edge (S : Slots G) (P : Parameters S) (d : Directed E) (rank : Fin P.rankCard)
    (ancestors : List (Directed E)) (s : Cache S P.rankCard) (μ : Memo E) :
    Program (Command S) (LocalRun S P.rankCard Bool) :=
  .tick (.oracle 3)
    (match μ d with
    | some b => .ret ⟨b, μ, s, [⟨d, ancestors, true⟩]⟩
    | none =>
      (scan S P
        (fun x t ν =>
          if _hr : x.rank.val < rank.val then
            edge S P (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν
          else .ret ⟨false, ν, t, []⟩)
        (G.head d) rank.val 0 (P.Nstar + 1) s μ).bind fun r =>
          .tick (.oracle 3)
            (.ret ⟨r.value.isNone, Function.update r.memo d (some r.value.isNone), r.cache,
              ⟨d, ancestors, false⟩ :: r.calls⟩))
termination_by rank.val
decreasing_by exact _hr

noncomputable def rootCall (v : V) (x : Entry S P.rankCard) (s : Cache S P.rankCard) (μ : Memo E) :
    Program (Command S) (LocalRun S P.rankCard Bool) :=
  edge S P (G.away v x.edge) x.rank [] s μ

@[irreducible] noncomputable def vertex (v : V) :
    Program (Command S) (LocalRun S P.rankCard (Option E)) :=
  .tick (.oracle (P.rankExponent + P.sortHeight + 12))
    ((scan S P (rootCall S P v)
      v P.rankCard 0 (P.Nstar + 1) (Cache.empty S P.rankCard) (fun _ => none)).bind fun r =>
        .ret ⟨r.value.map Entry.edge, r.memo, r.cache, r.calls⟩)

end Oracle

end SteinerUpperBound.Matching.Padded
