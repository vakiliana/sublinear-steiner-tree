module

public import SteinerLowerBound.Screening.PriorMarks

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {T C : Type*}

noncomputable def historyCharge (cost : List (Query T C) → Query T C → ℝ)
    (h : List (Query T C)) : ℝ :=
  h.reverseRecOn 0 (fun h q s => s + cost h q)

@[simp]
theorem historyCharge_nil (cost : List (Query T C) → Query T C → ℝ) :
    historyCharge cost [] = 0 := by simp [historyCharge]

@[simp]
theorem historyCharge_append (cost : List (Query T C) → Query T C → ℝ)
    (h : List (Query T C)) (q : Query T C) :
    historyCharge cost (h ++ [q]) = historyCharge cost h + cost h q := by
  simp [historyCharge]

theorem historyCharge_nonneg (cost : List (Query T C) → Query T C → ℝ)
    (hc : ∀ h q, 0 ≤ cost h q) (h : List (Query T C)) : 0 ≤ historyCharge cost h := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h q ih => rw [historyCharge_append]; exact add_nonneg ih (hc h q)

theorem historyCharge_add (f g : List (Query T C) → Query T C → ℝ)
    (h : List (Query T C)) :
    historyCharge (fun h q => f h q + g h q) h = historyCharge f h + historyCharge g h := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h q ih => simp only [historyCharge_append, ih]; ring

theorem historyCharge_const_mul (a : ℝ) (f : List (Query T C) → Query T C → ℝ)
    (h : List (Query T C)) :
    historyCharge (fun h q => a * f h q) h = a * historyCharge f h := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h q ih => simp only [historyCharge_append, ih]; ring

theorem historyCharge_const (a : ℝ) (h : List (Query T C)) :
    historyCharge (fun _ _ => a) h = a * h.length := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h q ih =>
      simp only [historyCharge_append, ih, List.length_append, List.length_singleton,
        Nat.cast_add, Nat.cast_one]
      ring

theorem historyCharge_run {Ω Z : Type*} (answer : Ω → List (Query T C) → Query T C → Reply)
    (cost : Ω → List (Query T C) → Query T C → ℝ)
    (ω : Ω) (r : Record (Query T C) Reply)
    (tree : SteinerLowerBound.DecisionTree (Query T C) Reply Z) :
    historyCharge (cost ω) (questions (DecisionTree.run answer ω r tree)) =
      historyCharge (cost ω) (questions r) +
        DecisionTree.accumulate answer (fun ω r q => cost ω (questions r) q) ω r tree := by
  induction tree generalizing r with
  | leaf => simp [DecisionTree.run, DecisionTree.accumulate]
  | query q next ih =>
      simp only [DecisionTree.run, DecisionTree.accumulate]
      rw [ih]
      simp only [questions, List.map_append, List.map_singleton, historyCharge_append]
      ring

variable [Fintype T]

theorem addNotices_new_subset (F H : C → Finset T) (s : Book T) (l : List T) :
    (addNotices F H s l).noticed ⊆ s.noticed ∪ l.toFinset := by
  classical
  induction l generalizing s with
  | nil => simp [addNotices]
  | cons u l ih =>
      intro v hv
      have hh := ih (addNotice F H s u) hv
      rcases Finset.mem_union.mp hh with hh | hh
      · by_cases hu : u ∈ s.exposed
        · exact Finset.mem_union_left _ (by simpa only [addNotice, hu, ↓reduceIte] using hh)
        · have hv' : v ∈ insert u s.noticed := by simpa only [addNotice, hu, ↓reduceIte] using hh
          rcases Finset.mem_insert.mp hv' with rfl | hv'
          · simp
          · exact Finset.mem_union_left _ hv'
      · exact Finset.mem_union_right _ (by simp only [List.toFinset_cons]; exact Finset.mem_insert_of_mem hh)

variable {S G I : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

noncomputable def degreeCrossings (D : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    Finset (Terminal S G I) :=
  highDegree D (h ++ [q]) \ highDegree D h

theorem mem_degreeCrossings (D : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C)
    (u : Terminal S G I) :
    u ∈ degreeCrossings D h q ↔ degree h u < D ∧ D ≤ degree (h ++ [q]) u := by
  simp only [degreeCrossings, highDegree, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_univ, true_and, not_le, and_comm]

theorem degreeCrossings_charge (D : ℕ) (hD : 0 < D)
    (h : List (Query (Terminal S G I) C)) :
    historyCharge (fun h q => ((degreeCrossings D h q).card : ℝ)) h =
      (highDegree D h).card := by
  classical
  induction h using List.reverseRecOn with
  | nil => simp [highDegree, degree, Nat.not_le.mpr hD]
  | append_singleton h q ih =>
      rw [historyCharge_append, ih]
      have hh := Finset.card_sdiff_add_card_eq_card (highDegree_mono_append D h q)
      have hh' : ((degreeCrossings D h q).card : ℝ) + (highDegree D h).card =
          (highDegree D (h ++ [q])).card := by exact_mod_cast hh
      linarith

end Screening

end SteinerLowerBound
