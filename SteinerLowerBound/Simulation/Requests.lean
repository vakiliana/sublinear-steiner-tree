module

public import SteinerLowerBound.Simulation.Projection

@[expose] public section

namespace SteinerLowerBound.Simulation

open scoped Classical

variable {T X : Type*}

noncomputable def closeRequests (D : Finset T → Finset X) (support : X → Finset T)
    (cap : ℕ) : ℕ → State T X → (X → Bool) → List (Finset T)
  | fuel, s, o =>
      if s.stop ≠ none then [] else if cap < s.exposed.card then [] else
      match fuel with
      | 0 => []
      | fuel + 1 =>
          let cache := (readList (D s.exposed).toList s.cache).output o
          let Q := s.exposed ∪ vertices support cache.kept
          s.exposed :: if Q = s.exposed then [] else
            closeRequests D support cap fuel
              {s with exposed := Q, requested := s.exposed, cache := cache} o

def RequestBounds (cap : ℕ) (previous latest : Finset T) (requests : List (Finset T)) : Prop :=
  previous ⊆ latest ∧ requests.Pairwise (fun Q Q' => Q ⊆ Q') ∧
    ∀ Q ∈ requests, previous ⊆ Q ∧ Q ⊆ latest ∧ Q.card ≤ cap

theorem closeRequests_bounds (D : Finset T → Finset X) (support : X → Finset T)
    (cap fuel : ℕ) (s : State T X) (o : X → Bool) (hs : s.requested ⊆ s.exposed) :
    RequestBounds cap s.requested ((close D support cap fuel s).output o).requested
      (closeRequests D support cap fuel s o) := by
  classical
  induction fuel generalizing s with
  | zero =>
      rw [closeRequests, close]
      split_ifs <;> simp [RequestBounds, DecisionTree.output]
  | succ fuel ih =>
      rw [closeRequests, close]
      split_ifs with hstop hcap
      · simp [RequestBounds, DecisionTree.output]
      · simp [RequestBounds, DecisionTree.output]
      · rw [output_bind]
        let cache := (readList (D s.exposed).toList s.cache).output o
        let Q := s.exposed ∪ vertices support cache.kept
        let r : State T X := {s with requested := s.exposed, cache := cache}
        change RequestBounds cap s.requested
          ((if Q = s.exposed then .leaf r else
            close D support cap fuel {r with exposed := Q}).output o).requested
          (s.exposed :: if Q = s.exposed then [] else
            closeRequests D support cap fuel {r with exposed := Q} o)
        by_cases he : Q = s.exposed
        · rw [if_pos he, if_pos he]
          refine ⟨hs, by simp, ?_⟩
          intro Q' hQ'
          have hQ' : Q' = s.exposed := by simpa only [List.mem_singleton] using hQ'
          subst Q'
          exact ⟨hs, Finset.Subset.rfl, Nat.le_of_not_gt hcap⟩
        · rw [if_neg he, if_neg he]
          have hi := ih {r with exposed := Q} (Finset.subset_union_left)
          refine ⟨hs.trans hi.1, ?_, ?_⟩
          · exact List.pairwise_cons.mpr
              ⟨fun Q' hQ' => (hi.2.2 Q' hQ').1, hi.2.1⟩
          · intro Q' hQ'
            rcases List.mem_cons.mp hQ' with hQ' | hQ'
            · subst Q'
              exact ⟨hs, hi.1, Nat.le_of_not_gt hcap⟩
            · obtain ⟨hl, hu, hc⟩ := hi.2.2 Q' hQ'
              exact ⟨hs.trans hl, hu, hc⟩

theorem noticeOne_requested_mono (D : Finset T → Finset X) (support : X → Finset T)
    (R : ℕ) (u : T) (s : State T X) (o : X → Bool) (hs : s.requested ⊆ s.exposed) :
    s.requested ⊆ ((noticeOne D support R u s).output o).requested := by
  classical
  rw [noticeOne]
  split_ifs
  · exact Finset.Subset.rfl
  · dsimp only
    split_ifs
    · exact Finset.Subset.rfl
    · let r := {s with noticed := insert u s.noticed, exposed := insert u s.exposed}
      exact (closeRequests_bounds D support (2 * R) (2 * R + 1) r o
        (hs.trans (Finset.subset_insert _ _))).1

theorem noticeList_requested_mono (D : Finset T → Finset X) (support : X → Finset T)
    (hD : Monotone D) (R : ℕ) (l : List T) (s : State T X) (o : X → Bool)
    (hs : Stable D support R s) :
    s.requested ⊆ ((noticeList D support R l s).output o).requested := by
  induction l generalizing s with
  | nil => exact Finset.Subset.rfl
  | cons u l ih =>
      rw [noticeList, output_bind]
      have hsp := noticeOne_spec D support hD R u s hs
      exact (noticeOne_requested_mono D support R u s o hs.1.requested_subset).trans
        (ih _ (Spec.output _ _ _ _ hsp o))

namespace Public

open HardDistribution
open MetricComparison.Public

variable {S G I C Z : Type*}
  [Fintype S] [Fintype G] [Fintype I] [Fintype C]

theorem run_requested_mono (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (D t R : ℕ)
    (algorithm : DecisionTree (Query (Terminal S G I) C) Reply Z)
    (h : List (Query (Terminal S G I) C)) (s : SimState S G I C d)
    (hs : Stable (access π d F) (support π d) R s) (o : Candidate S C d → Bool) :
    s.requested ⊆ ((run π d F D t R algorithm h s).output o).state.requested := by
  induction algorithm generalizing h s with
  | leaf => exact Finset.Subset.rfl
  | query q next ih =>
      rw [run]
      split_ifs
      · exact Finset.Subset.rfl
      · dsimp only
        rw [output_bind, output_bind]
        let l := Screening.noticeOrder
          (notices π F D t h q (answer π d F s.cache h q) s.exposed)
        have hsp := noticeList_spec (access π d F) (support π d) (access_mono π d F) R l s hs
        exact (noticeList_requested_mono _ _ (access_mono π d F) R l s o hs).trans
          (ih _ _ _ (Spec.output _ _ _ _ hsp o))

end Public

end SteinerLowerBound.Simulation
