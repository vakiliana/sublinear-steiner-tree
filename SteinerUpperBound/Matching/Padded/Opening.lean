module

public import SteinerUpperBound.Matching.Padded.LedgerExpected

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Cache

open SteinerLowerBound
open scoped Classical

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ) [Fintype E]

theorem prefix_count (ranks : E → Fin Q) (v : V) (x : ℕ) :
    UniformRanks.Count Q G v x ranks =
      ((G.candidates (UniformOrder.order ranks) (Fintype.card E) v).filter
        (fun e => (ranks e).val < x)).length := by
  classical
  let xs := (G.candidates (UniformOrder.order ranks) (Fintype.card E) v).filter
    (fun e => (ranks e).val < x)
  have hn := (G.candidates_nodup (UniformOrder.order ranks) (Fintype.card E) v).filter
    (fun e => (ranks e).val < x)
  unfold UniformRanks.Count IndependentTrials.count
  calc
    _ = xs.toFinset.card := by
      apply congrArg Finset.card
      ext e
      simp [xs, G.mem_candidates, (UniformOrder.order ranks).index_lt e]
    _ = _ := List.toFinset_card_of_nodup hn

theorem available_none_count (s : Cache S Q) (hs : Invariant S Q s) (ranks : E → Fin Q)
    (hc : Consistent S Q s ranks) (hn : Function.Injective ranks) (v : V) (cursor : ℕ)
    (ha : available S Q v cursor s = none) :
    UniformRanks.Count Q G v (boundary S Q s v) ranks ≤ cursor := by
  have hp := available_probe S Q s v cursor
  rw [ha, Option.map_none, probe_lowEntries S Q s hs.ready] at hp
  have hl := List.getElem?_eq_none_iff.mp hp.symm
  rw [lowEntries_eq S Q s hs ranks hc hn, ← prefix_count Q ranks v] at hl
  exact hl

def PriorCountBound (s : Cache S Q) (ranks : E → Fin Q) : Prop :=
  ∀ v, 0 < s.level v →
    UniformRanks.Count Q G v (Buckets.bound (s.level v - 1)) ranks < s.requests v

theorem empty_priorCountBound (ranks : E → Fin Q) : PriorCountBound S Q (empty S Q) ranks := by
  intro v hv
  change 0 < 0 at hv
  omega

theorem priorCountBound_mono (s t : Cache S Q) (ranks : E → Fin Q)
    (hs : PriorCountBound S Q s ranks) (hl : t.level = s.level)
    (hr : ∀ v, s.requests v ≤ t.requests v) : PriorCountBound S Q t ranks := by
  intro v hv
  rw [hl] at hv ⊢
  exact (hs v hv).trans_le (hr v)

theorem idealExtend_priorCountBound (height : ℕ) (v : V) (cursor : ℕ) (s : Cache S Q)
    (ranks : E → Fin Q) (hs : Invariant S Q s) (hc : Consistent S Q s ranks)
    (hn : Function.Injective ranks) (hprior : PriorCountBound S Q s ranks)
    (hcursor : cursor < s.requests v) (ha : available S Q v cursor s = none) :
    PriorCountBound S Q (idealExtend S Q height v s ranks) ranks := by
  classical
  by_cases hb : Buckets.bound (s.level v + 1) ≤ Q
  · have hl := idealExtend_levels S Q height v s ranks hb
    have hr := (idealExtend_administration S Q height v s ranks).2
    intro u hu
    rw [hr]
    by_cases huv : u = v
    · subst u
      rw [hl, Function.update_self, Nat.add_sub_cancel]
      exact (available_none_count S Q s hs ranks hc hn v cursor ha).trans_lt hcursor
    · rw [hl, Function.update_of_ne huv]
      have hpos : 0 < s.level u := by simpa only [hl, Function.update_of_ne huv] using hu
      exact hprior u hpos
  · simpa only [idealExtend, hb, ↓reduceIte] using hprior

theorem idealNextLoop_priorCountBound (height : ℕ) (v : V) (cursor fuel : ℕ) (s : Cache S Q)
    (ranks : E → Fin Q) (hs : Invariant S Q s) (hc : Consistent S Q s ranks)
    (hn : Function.Injective ranks) (hprior : PriorCountBound S Q s ranks)
    (hcursor : cursor < s.requests v) (hlen : Fintype.card E ≤ 2 ^ height) :
    PriorCountBound S Q (idealNextLoop S Q height v cursor fuel s ranks).2 ranks := by
  induction fuel generalizing s with
  | zero => exact hprior
  | succ fuel ih =>
    rw [idealNextLoop]
    cases ha : available S Q v cursor s with
    | some x => exact hprior
    | none =>
      split_ifs
      · have ht := idealExtend_invariant S Q height v s ranks hs hc hlen
        have hp := idealExtend_priorCountBound S Q height v cursor s ranks hs hc hn hprior hcursor ha
        have hr := (idealExtend_administration S Q height v s ranks).2
        exact ih _ ht.1 ht.2 hp (by simpa only [hr] using hcursor)
      · exact hprior

variable [Fintype V]

theorem idealNext_priorCountBound (P : Parameters S) (v : V) (cursor : ℕ) (s : Cache S P.rankCard)
    (ranks : E → Fin P.rankCard) (hs : Invariant S P.rankCard s)
    (hc : Consistent S P.rankCard s ranks) (hn : Function.Injective ranks)
    (hp : PriorCountBound S P.rankCard s ranks) (hcursor : cursor ≤ s.requests v) :
    PriorCountBound S P.rankCard
      (idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks).2 ranks := by
  classical
  have hr (u : V) : s.requests u ≤ Function.update s.requests v (s.requests v + 1) u := by
    by_cases hu : u = v
    · subst u; simp
    · simp [Function.update_of_ne hu]
  unfold idealNext
  cases hprep : s.prepared v with
  | true =>
    simp only [↓reduceIte]
    apply idealNextLoop_priorCountBound S P.rankCard P.sortHeight v cursor (P.rankExponent + 2)
      { s with requests := Function.update s.requests v (s.requests v + 1) } ranks
      (administrative_invariant S P.rankCard s hs s.prepared
        (Function.update s.requests v (s.requests v + 1))) hc hn
    · exact priorCountBound_mono S P.rankCard s _ ranks hp rfl hr
    · simpa only [Function.update_self] using Nat.lt_succ_of_le hcursor
    · exact Parameters.copies_le_sortCapacity S P
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply idealNextLoop_priorCountBound S P.rankCard P.sortHeight v cursor (P.rankExponent + 2)
      { s with requests := Function.update s.requests v (s.requests v + 1),
               prepared := Function.update s.prepared v true } ranks
      (administrative_invariant S P.rankCard s hs (Function.update s.prepared v true)
        (Function.update s.requests v (s.requests v + 1))) hc hn
    · exact priorCountBound_mono S P.rankCard s _ ranks hp rfl hr
    · simpa only [Function.update_self] using Nat.lt_succ_of_le hcursor
    · exact Parameters.copies_le_sortCapacity S P

end SteinerUpperBound.Matching.Padded.Cache
