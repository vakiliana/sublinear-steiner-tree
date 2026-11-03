module

public import SteinerLowerBound.Simulation.Closure

@[expose] public section

namespace SteinerLowerBound.Simulation

open scoped BigOperators Classical

variable {T X : Type*}

def Stable (D : Finset T → Finset X) (support : X → Finset T)
    (R : ℕ) (s : State T X) : Prop :=
  Safe D support (2 * R) s ∧ Ready D support s ∧
    (s.stop = none → s.noticed.card ≤ R ∧ s.exposed.card ≤ 2 * R) ∧
    (s.stop = some .closure → s.noticed.card ≤ R ∧ 2 * R < s.exposed.card)

theorem initial_stable (D : Finset T → Finset X) (support : X → Finset T)
    (R : ℕ) (hD : D ∅ = ∅) : Stable D support R (State.initial : State T X) := by
  refine ⟨initial_safe D support _, initial_ready D support hD, ?_, ?_⟩ <;>
    simp [State.initial]

noncomputable def noticeOne (D : Finset T → Finset X) (support : X → Finset T)
    (R : ℕ) (u : T) (s : State T X) : DecisionTree X Bool (State T X) :=
  if s.stop ≠ none ∨ u ∈ s.exposed then .leaf s else
  let r := {s with noticed := insert u s.noticed, exposed := insert u s.exposed}
  if R < r.noticed.card then .leaf {r with stop := some .notices}
  else close D support (2 * R) (2 * R + 1) r

theorem noticeOne_spec (D : Finset T → Finset X) (support : X → Finset T)
    (hD : Monotone D) (R : ℕ) (u : T) (s : State T X) (hs : Stable D support R s) :
    Spec State.cache (Stable D support R) s.cache (noticeOne D support R u s) := by
  classical
  rw [noticeOne]
  split_ifs with hskip
  · exact ⟨rfl, hs⟩
  · dsimp only
    split_ifs with hN
    · refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · refine ⟨hs.1.requested_cap,
          hs.1.requested_subset.trans (Finset.subset_insert _ _),
          hs.1.read_subset, hs.1.kept_subset, ?_⟩
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
        · rcases Finset.mem_union.mp (hs.1.cover hv) with hn | hk
          · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hn)
          · exact Finset.mem_union_right _ hk
      · simp [Ready]
      · simp
      · simp
    · let r : State T X := {s with noticed := insert u s.noticed, exposed := insert u s.exposed}
      have hr : Safe D support (2 * R) r := by
        refine ⟨hs.1.requested_cap,
          hs.1.requested_subset.trans (Finset.subset_insert _ _),
          hs.1.read_subset, hs.1.kept_subset, ?_⟩
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
        · rcases Finset.mem_union.mp (hs.1.cover hv) with hn | hk
          · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hn)
          · exact Finset.mem_union_right _ hk
      apply (close_spec D support hD (2 * R) (2 * R + 1) r hr (by omega)).mono
      intro z hz
      refine ⟨hz.1, hz.2.1, ?_, ?_⟩
      · intro hn
        refine ⟨?_, hz.2.2.2.2.2.2 hn⟩
        rw [hz.2.2.1]
        exact Nat.le_of_not_gt hN
      · intro hc
        refine ⟨?_, ?_⟩
        · rw [hz.2.2.1]
          exact Nat.le_of_not_gt hN
        · rcases hz.2.2.2.2.2.1 hc with h | h
          · have hn : s.stop = none := by simpa using (not_or.mp hskip).1
            change s.stop = some .closure at h
            rw [hn] at h
            cases h
          · exact h

noncomputable def noticeList (D : Finset T → Finset X) (support : X → Finset T)
    (R : ℕ) : List T → State T X → DecisionTree X Bool (State T X)
  | [], s => .leaf s
  | u :: l, s => bind (noticeOne D support R u s) (noticeList D support R l)

theorem noticeList_spec (D : Finset T → Finset X) (support : X → Finset T)
    (hD : Monotone D) (R : ℕ) (l : List T) (s : State T X) (hs : Stable D support R s) :
    Spec State.cache (Stable D support R) s.cache (noticeList D support R l s) := by
  induction l generalizing s with
  | nil => exact ⟨rfl, hs⟩
  | cons u l ih =>
      exact (noticeOne_spec D support hD R u s hs).bind _ _ _ _ _ _ _
        (fun z hz => ih z hz)

theorem vertices_card_le (support : X → Finset T) (d : ℕ)
    (hd : ∀ x, (support x).card ≤ d) (K : Finset X) :
    (vertices support K).card ≤ d * K.card := by
  classical
  calc
    _ ≤ ∑ x ∈ K, (support x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ K, d := Finset.sum_le_sum (fun x _ => hd x)
    _ = _ := by simp [Nat.mul_comm]

theorem closure_overflow (D : Finset T → Finset X) (support : X → Finset T)
    (R d : ℕ) (hd : ∀ x, (support x).card ≤ d)
    (s : State T X) (hs : Stable D support R s) (hstop : s.stop = some .closure) :
    R < d * s.cache.kept.card := by
  have hcov := Finset.card_le_card hs.1.cover
  have huni := Finset.card_union_le s.noticed (vertices support s.cache.kept)
  have hv := vertices_card_le support d hd s.cache.kept
  have hb := hs.2.2.2 hstop
  omega

end SteinerLowerBound.Simulation
