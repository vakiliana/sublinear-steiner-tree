module

public import SteinerLowerBound.Screening.Adaptive

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

noncomputable def queryMarks (π : Equiv.Perm (Terminal S G I)) :
    Query (Terminal S G I) C → Finset (Terminal S G I)
  | .tt a b => if a ≠ b ∧ SameCluster π a b then {a, b} else ∅
  | _ => ∅

theorem marked_append (π : Equiv.Perm (Terminal S G I))
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    marked π (h ++ [q]) = marked π h ∪ queryMarks π q := by
  classical
  ext u
  simp only [marked, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, List.mem_append, List.mem_singleton]
  cases q with
  | ct c v => simp [queryMarks]
  | cc c c' => simp [queryMarks]
  | tt a b =>
      by_cases hp : a ≠ b ∧ SameCluster π a b
      · rw [queryMarks, if_pos hp]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨x, y, hq | hq, hne, hcl, he⟩
          · exact Or.inl ⟨x, y, hq, hne, hcl, he⟩
          · obtain ⟨rfl, rfl⟩ := Query.tt.inj hq
            exact Or.inr he
        · rintro (hh | hu)
          · obtain ⟨x, y, hq, hne, hcl, he⟩ := hh
            exact ⟨x, y, Or.inl hq, hne, hcl, he⟩
          · exact ⟨a, b, Or.inr rfl, hp.1, hp.2, hu⟩
      · rw [queryMarks, if_neg hp]
        simp only [Finset.notMem_empty, or_false]
        constructor
        · rintro ⟨x, y, hq | hq, hne, hcl, he⟩
          · exact ⟨x, y, hq, hne, hcl, he⟩
          · obtain ⟨rfl, rfl⟩ := Query.tt.inj hq
            exact False.elim (hp ⟨hne, hcl⟩)
        · rintro ⟨x, y, hq, hne, hcl, he⟩
          exact ⟨x, y, Or.inl hq, hne, hcl, he⟩

theorem marked_mono_append (π : Equiv.Perm (Terminal S G I))
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    marked π h ⊆ marked π (h ++ [q]) := by
  rw [marked_append]
  exact Finset.subset_union_left

noncomputable def clusterExposure (π : Equiv.Perm (Terminal S G I))
    (h : List (Query (Terminal S G I) C)) (u : Terminal S G I) : ℕ :=
  match clusterPosition (π u) with
  | none => 0
  | some g => (externalLabels π h g).card

noncomputable def lowMarkSet (π : Equiv.Perm (Terminal S G I)) (D t : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    Finset (Terminal S G I) :=
  (queryMarks π q \ marked π h).filter fun u =>
    degree h u < D ∧ clusterExposure π h u < t ∧ (marked π h).card < t

noncomputable def lowMarks (π : Equiv.Perm (Terminal S G I)) (D t : ℕ)
    (h : List (Query (Terminal S G I) C)) : Finset (Terminal S G I) :=
  h.reverseRecOn ∅ (fun h q s => s ∪ lowMarkSet π D t h q)

@[simp]
theorem lowMarks_nil (π : Equiv.Perm (Terminal S G I)) (D t : ℕ) :
    lowMarks (C := C) π D t [] = ∅ := by simp [lowMarks]

@[simp]
theorem lowMarks_append (π : Equiv.Perm (Terminal S G I)) (D t : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    lowMarks π D t (h ++ [q]) = lowMarks π D t h ∪ lowMarkSet π D t h q := by
  simp [lowMarks]

noncomputable def highDegree (D : ℕ) (h : List (Query (Terminal S G I) C)) :
    Finset (Terminal S G I) := Finset.univ.filter fun u => D ≤ degree h u

noncomputable def highClusters (π : Equiv.Perm (Terminal S G I)) (t : ℕ)
    (h : List (Query (Terminal S G I) C)) : Finset G :=
  Finset.univ.filter fun g => t ≤ (externalLabels π h g).card

noncomputable def highClusterLabels (π : Equiv.Perm (Terminal S G I)) (t : ℕ)
    (h : List (Query (Terminal S G I) C)) : Finset (Terminal S G I) :=
  (highClusters π t h).biUnion (clusterLabels π)

noncomputable def markCharges (π : Equiv.Perm (Terminal S G I)) (D t : ℕ)
    (h : List (Query (Terminal S G I) C)) : Finset (Terminal S G I) :=
  highDegree D h ∪ highClusterLabels π t h ∪ lowMarks π D t h

theorem highDegree_mono_append (D : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    highDegree D h ⊆ highDegree D (h ++ [q]) := by
  intro u hu
  simp only [highDegree, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rw [degree_append]
  omega

theorem highClusters_mono_append (π : Equiv.Perm (Terminal S G I)) (t : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    highClusters π t h ⊆ highClusters π t (h ++ [q]) := by
  intro g hg
  simp only [highClusters, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
  rw [externalLabels_append]
  exact hg.trans (Finset.card_le_card Finset.subset_union_left)

theorem markCharges_mono_append (π : Equiv.Perm (Terminal S G I)) (D t : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    markCharges π D t h ⊆ markCharges π D t (h ++ [q]) := by
  apply Finset.union_subset_union
  · apply Finset.union_subset_union (highDegree_mono_append D h q)
    exact Finset.biUnion_subset_biUnion_of_subset_left (clusterLabels π)
      (highClusters_mono_append π t h q)
  · rw [lowMarks_append]
    exact Finset.subset_union_left

theorem queryMarks_cluster (π : Equiv.Perm (Terminal S G I))
    (q : Query (Terminal S G I) C) (u : Terminal S G I) (hu : u ∈ queryMarks π q) :
    ∃ g, u ∈ clusterLabels π g := by
  classical
  cases q with
  | ct => simp [queryMarks] at hu
  | cc => simp [queryMarks] at hu
  | tt a b =>
      simp only [queryMarks] at hu
      split_ifs at hu with hp
      · obtain ⟨g, ha, hb⟩ := hp.2
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact ⟨g, (mem_clusterLabels _ _ _).mpr ha⟩
        · have heu := Finset.mem_singleton.mp hu
          subst u
          exact ⟨g, (mem_clusterLabels _ _ _).mpr hb⟩
      · simp at hu

theorem new_mark_charged (π : Equiv.Perm (Terminal S G I)) (D t : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C)
    (hm : (marked π h).card < t) (u : Terminal S G I)
    (hu : u ∈ queryMarks π q) (hnew : u ∉ marked π h) :
    u ∈ markCharges π D t (h ++ [q]) := by
  classical
  by_cases hd : D ≤ degree h u
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact highDegree_mono_append D h q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)
  · by_cases he : t ≤ clusterExposure π h u
    · obtain ⟨g, hg⟩ := queryMarks_cluster π q u hu
      have hce : clusterExposure π h u = (externalLabels π h g).card := by
        simp only [clusterExposure, (mem_clusterLabels π g u).mp hg]
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨g, highClusters_mono_append π t h q ?_, hg⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hce ▸ he⟩
    · apply Finset.mem_union_right
      rw [lowMarks_append]
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hu, hnew⟩,
        Nat.lt_of_not_ge hd, Nat.lt_of_not_ge he, hm⟩

theorem mark_threshold_charged (π : Equiv.Perm (Terminal S G I)) (D t : ℕ)
    (h : List (Query (Terminal S G I) C)) :
    ((marked π h).card < t → marked π h ⊆ markCharges π D t h) ∧
      (t ≤ (marked π h).card → t ≤ (markCharges π D t h).card) := by
  classical
  induction h using List.reverseRecOn with
  | nil =>
      constructor
      · intro _
        simp [marked]
      · intro hh
        have ht : t ≤ 0 := by simpa [marked] using hh
        omega
  | append_singleton h q ih =>
      by_cases hm : (marked π h).card < t
      · have hs : marked π (h ++ [q]) ⊆ markCharges π D t (h ++ [q]) := by
          rw [marked_append]
          apply Finset.union_subset
          · exact (ih.1 hm).trans (markCharges_mono_append π D t h q)
          · intro u hu
            by_cases hum : u ∈ marked π h
            · exact markCharges_mono_append π D t h q (ih.1 hm hum)
            · exact new_mark_charged π D t h q hm u hu hum
        exact ⟨fun _ => hs, fun hh => hh.trans (Finset.card_le_card hs)⟩
      · have ht := (ih.2 (Nat.le_of_not_gt hm)).trans
          (Finset.card_le_card (markCharges_mono_append π D t h q))
        refine ⟨fun hh => ?_, fun _ => ht⟩
        have hmono := Finset.card_le_card (marked_mono_append π h q)
        omega

theorem highDegree_budget (D : ℕ) (h : List (Query (Terminal S G I) C)) :
    D * (highDegree D h).card ≤ 2 * h.length := by
  classical
  calc
    _ = ∑ _u ∈ highDegree D h, D := by simp [Nat.mul_comm]
    _ ≤ ∑ u ∈ highDegree D h, degree h u := by
      apply Finset.sum_le_sum
      intro u hu
      exact (Finset.mem_filter.mp hu).2
    _ ≤ ∑ u, degree h u := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ ≤ _ := sum_degree_le h

theorem highClusters_budget (π : Equiv.Perm (Terminal S G I)) (t : ℕ)
    (h : List (Query (Terminal S G I) C)) :
    t * (highClusters π t h).card ≤ 2 * h.length := by
  classical
  calc
    _ = ∑ _g ∈ highClusters π t h, t := by simp [Nat.mul_comm]
    _ ≤ ∑ g ∈ highClusters π t h, (externalLabels π h g).card := by
      apply Finset.sum_le_sum
      intro g hg
      exact (Finset.mem_filter.mp hg).2
    _ ≤ ∑ g, (externalLabels π h g).card :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ ≤ _ := sum_externalLabels_le π h

theorem highClusterLabels_card (π : Equiv.Perm (Terminal S G I)) (t : ℕ)
    (h : List (Query (Terminal S G I) C)) :
    (highClusterLabels π t h).card ≤ (highClusters π t h).card * Fintype.card I := by
  calc
    _ ≤ ∑ g ∈ highClusters π t h, (clusterLabels π g).card := Finset.card_biUnion_le
    _ = _ := by simp

end Screening

end SteinerLowerBound
