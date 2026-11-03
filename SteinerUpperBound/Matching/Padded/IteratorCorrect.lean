module

public import SteinerUpperBound.Matching.Padded.NextFacts

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Cache

open scoped Classical

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ)

theorem level_le_power (H : ℕ) (s : Cache S (2 ^ H)) (v : V)
    (hs : Legal S (2 ^ H) s) : s.level v ≤ H + 1 := by
  by_contra hn
  have hl : H + 1 < s.level v := Nat.lt_of_not_ge hn
  have hb := Buckets.bound_strictMono hl
  have hQ : Buckets.bound (H + 1) = 2 ^ H := rfl
  have hsbound := hs.1 v
  change Buckets.bound (s.level v) ≤ 2 ^ H at hsbound
  omega

structure IteratorCorrect [Fintype E] (ranks : E → Fin Q) (v : V) (cursor : ℕ)
    (answer : Option (Entry S Q) × Cache S Q) : Prop where
  invariant : Invariant S Q answer.2
  consistent : Consistent S Q answer.2 ranks
  value : answer.1.map Entry.edge =
    (G.candidates (UniformOrder.order ranks) (Fintype.card E) v)[cursor]?
  valid : ∀ x, answer.1 = some x →
    x.source.1 = v ∧ EntryValid S Q x ∧ ranks x.edge = x.rank

theorem idealNextLoop_correct [Fintype E] (height H : ℕ) (v : V) (cursor fuel : ℕ)
    (s : Cache S (2 ^ H)) (ranks : E → Fin (2 ^ H))
    (hs : Invariant S (2 ^ H) s) (hc : Consistent S (2 ^ H) s ranks)
    (hn : Function.Injective ranks) (hlen : Fintype.card E ≤ 2 ^ height)
    (hf : H + 2 ≤ fuel + s.level v) :
    IteratorCorrect S (2 ^ H) ranks v cursor
      (idealNextLoop S (2 ^ H) height v cursor fuel s ranks) := by
  induction fuel generalizing s with
  | zero =>
    have hl := level_le_power S H s v hs.legal
    omega
  | succ fuel ih =>
    rw [idealNextLoop]
    cases ha : available S (2 ^ H) v cursor s with
    | some x =>
      have hv := available_some_correct S (2 ^ H) s hs ranks hc hn v cursor x ha
      refine ⟨hs, hc, hv.1.symm, ?_⟩
      intro y hy
      have he := Option.some.inj hy
      subst y
      have hp := available_spec S (2 ^ H) s hs.ready v cursor x ha
      exact ⟨hp.1, hp.2.1, hv.2⟩
    | none =>
      by_cases hb : boundary S (2 ^ H) s v < 2 ^ H
      · simp only [hb, ↓reduceIte]
        have hnext := next_bound_le S H s v hb
        have ht := idealExtend_invariant S (2 ^ H) height v s ranks hs hc hlen
        have hlevel := congrFun (idealExtend_levels S (2 ^ H) height v s ranks hnext) v
        simp only [Function.update_self] at hlevel
        exact ih _ ht.1 ht.2 (by omega)
      · simp only [hb, ↓reduceIte]
        have hfull : boundary S (2 ^ H) s v = 2 ^ H := by
          have hh := hs.legal.1 v
          omega
        have hv := available_at_full S (2 ^ H) s hs ranks hc hn v cursor hfull
        rw [ha] at hv
        refine ⟨hs, hc, hv, ?_⟩
        intro x hx
        cases hx

theorem idealNext_correct [Fintype V] [Fintype E] (P : Parameters S)
    (v : V) (cursor : ℕ) (s : Cache S P.rankCard) (ranks : E → Fin P.rankCard)
    (hs : Invariant S P.rankCard s) (hc : Consistent S P.rankCard s ranks)
    (hn : Function.Injective ranks) :
    IteratorCorrect S P.rankCard ranks v cursor
      (idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks) := by
  unfold idealNext
  cases hp : s.prepared v with
  | true =>
    simp only [↓reduceIte]
    exact idealNextLoop_correct S P.sortHeight P.rankExponent v cursor (P.rankExponent + 2)
      _ ranks (administrative_invariant S P.rankCard s hs _ _) hc hn
      (Parameters.copies_le_sortCapacity S P) (by omega)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact idealNextLoop_correct S P.sortHeight P.rankExponent v cursor (P.rankExponent + 2)
      _ ranks (administrative_invariant S P.rankCard s hs _ _) hc hn
      (Parameters.copies_le_sortCapacity S P) (by omega)

theorem commit_administration (s : Cache S Q) (xs : List (Entry S Q)) :
    (commit S Q s xs).prepared = s.prepared ∧ (commit S Q s xs).requests = s.requests := by
  induction xs generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih => exact ih (assign S Q s x.source x.reverse x.edge x.rank)

theorem idealExtend_administration (height : ℕ) (v : V) (s : Cache S Q) (ranks : E → Fin Q) :
    (idealExtend S Q height v s ranks).prepared = s.prepared ∧
      (idealExtend S Q height v s ranks).requests = s.requests := by
  unfold idealExtend
  split_ifs
  · exact commit_administration S Q s _
  · exact ⟨rfl, rfl⟩

theorem idealNextLoop_administration (height : ℕ) (v : V) (cursor fuel : ℕ)
    (s : Cache S Q) (ranks : E → Fin Q) :
    (idealNextLoop S Q height v cursor fuel s ranks).2.prepared = s.prepared ∧
      (idealNextLoop S Q height v cursor fuel s ranks).2.requests = s.requests := by
  induction fuel generalizing s with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
    rw [idealNextLoop]
    cases ha : available S Q v cursor s with
    | some x => exact ⟨rfl, rfl⟩
    | none =>
      split_ifs
      · have ht := idealExtend_administration S Q height v s ranks
        have hh := ih (idealExtend S Q height v s ranks)
        exact ⟨hh.1.trans ht.1, hh.2.trans ht.2⟩
      · exact ⟨rfl, rfl⟩

theorem idealNext_requests (height maxLevel : ℕ) (v : V) (cursor : ℕ)
    (s : Cache S Q) (ranks : E → Fin Q) :
    (idealNext S Q height maxLevel v cursor s ranks).2.requests =
      Function.update s.requests v (s.requests v + 1) := by
  unfold idealNext
  cases hp : s.prepared v with
  | true =>
    simp only [↓reduceIte]
    exact (idealNextLoop_administration S Q height v cursor (maxLevel + 1) _ ranks).2
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact (idealNextLoop_administration S Q height v cursor (maxLevel + 1) _ ranks).2

end SteinerUpperBound.Matching.Padded.Cache
