module

public import SteinerLowerBound.CostLowerBound

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Steiner

variable {S G I C : Type*}

abbrev Solution (S G I C : Type*) :=
  Σ X : Finset C, {T : SimpleGraph (Point S G I {c // c ∈ X}) // T.IsTree}

noncomputable instance [Fintype S] [Fintype G] [Fintype I] [Fintype C] :
    Fintype (Solution S G I C) := by
  classical
  infer_instance

noncomputable def solutionCost [Fintype S] [Fintype G] [Fintype I] [Fintype C]
    (ell : ℝ) (nb : C → Finset S) (t : Solution S G I C) : ℝ :=
  GraphCost.cost (HardCost.edgeWeight ell (fun c => (nb c.val : Set S))) t.2.val

variable [Fintype S] [Fintype G] [Fintype I] [Fintype C] [Nonempty G] [Nonempty I]

omit [Fintype S] [Fintype G] [Fintype I] [Fintype C] in
theorem solution_nonempty : Nonempty (Solution S G I C) := by
  let r : Point S G I {c : C // c ∈ (∅ : Finset C)} :=
    .ordinary (Classical.arbitrary G) (Classical.arbitrary I)
  exact ⟨⟨∅, SimpleGraph.starGraph r, SimpleGraph.isTree_starGraph r⟩⟩

noncomputable def optimum (ell : ℝ) (nb : C → Finset S) : ℝ :=
  (Finset.univ.image (solutionCost (G := G) (I := I) ell nb)).min' (by
    obtain ⟨t⟩ := solution_nonempty (S := S) (G := G) (I := I) (C := C)
    exact ⟨solutionCost ell nb t, Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩⟩)

theorem optimum_le (ell : ℝ) (nb : C → Finset S) (t : Solution S G I C) :
    optimum (G := G) (I := I) ell nb ≤ solutionCost ell nb t := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)

theorem optimum_attained (ell : ℝ) (nb : C → Finset S) :
    ∃ t : Solution S G I C, solutionCost ell nb t = optimum (G := G) (I := I) ell nb := by
  have h := Finset.min'_mem
    (Finset.univ.image (solutionCost (G := G) (I := I) ell nb))
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (h _)
  exact ⟨t, ht⟩

theorem optimum_nonneg {ell : ℝ} (hEll : 0 ≤ ell) (nb : C → Finset S) :
    0 ≤ optimum (G := G) (I := I) ell nb := by
  obtain ⟨t, ht⟩ := optimum_attained (G := G) (I := I) ell nb
  rw [← ht]
  unfold solutionCost GraphCost.cost
  apply Finset.sum_nonneg
  intro e _
  rcases e with ⟨x, y⟩
  exact Point.distance_nonneg hEll _ x y

theorem optimum_lower {ell : ℝ} (hEll : ell ≤ 2) (nb : C → Finset S)
    (stars : Finset C) (positive : Finset S)
    (hstar : ∀ c ∈ stars, nb c ⊆ positive)
    (hfiller : ∀ c ∉ stars, (nb c).card ≤ 2) :
    ell * Fintype.card G * Fintype.card I +
        2 * Fintype.card S - 2 - positive.card ≤ optimum (G := G) (I := I) ell nb := by
  classical
  obtain ⟨t, ht⟩ := optimum_attained (G := G) (I := I) ell nb
  rw [← ht]
  let selectedStars : Finset {c // c ∈ t.1} := Finset.univ.filter (fun c => c.val ∈ stars)
  apply HardCost.tree_lower hEll t.2.val t.2.property
    (fun c => nb c.val) selectedStars positive
  · intro c hc
    exact hstar c.val (Finset.mem_filter.mp hc).2
  · intro c hc
    apply hfiller c.val
    intro hc'
    exact hc (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc'⟩)

theorem optimum_upper {ell : ℝ} (hEll : ell ≤ 2) (nb : C → Finset S)
    (stars : Finset C) :
    optimum (G := G) (I := I) ell nb ≤
      ell * Fintype.card G * ((Fintype.card I : ℝ) - 1) +
        2 * ((Fintype.card G : ℝ) + Fintype.card S - 1) -
          (((stars.biUnion nb).card : ℝ) - 2 * stars.card) := by
  classical
  let covered := stars.biUnion nb
  have hex (u : {u // u ∈ covered}) : ∃ c : {c // c ∈ stars}, u.val ∈ nb c.val := by
    obtain ⟨c, hc, hu⟩ := Finset.mem_biUnion.mp u.property
    exact ⟨⟨c, hc⟩, hu⟩
  let owner : {u // u ∈ covered} → {c // c ∈ stars} := fun u => Classical.choose (hex u)
  have howner (u : {u // u ∈ covered}) : u.val ∈ nb (owner u).val :=
    Classical.choose_spec (hex u)
  obtain ⟨T, hT, hcost⟩ := HardCost.exists_tree_upper (G := G) hEll
    (fun c : {c // c ∈ stars} => (nb c.val : Set S))
    (Classical.arbitrary I) covered owner howner
  have hopt := optimum_le ell nb (⟨stars, T, hT⟩ : Solution S G I C)
  exact hopt.trans (by simpa [solutionCost, covered] using hcost)

end Steiner

end SteinerLowerBound
