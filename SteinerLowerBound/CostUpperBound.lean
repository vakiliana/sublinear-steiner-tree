module

public import SteinerLowerBound.GraphCost

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace HardCost

variable {S G I C : Type*}

noncomputable def edgeWeight (ell : ℝ) (nb : C → Set S) : Sym2 (Point S G I C) → ℝ :=
  Sym2.lift ⟨Point.distance ell nb, Point.distance_comm ell nb⟩

@[simp]
theorem edgeWeight_mk (ell : ℝ) (nb : C → Set S) (x y : Point S G I C) :
    edgeWeight ell nb s(x, y) = Point.distance ell nb x y := rfl

noncomputable def parent (root : I) (covered : Finset S) (owner : {u // u ∈ covered} → C) :
    Point S G I C → Point S G I C
  | .special u => if h : u ∈ covered then .center (owner ⟨u, h⟩) else .special u
  | .ordinary a _ => .ordinary a root
  | .center c => .center c

theorem parent_idempotent (root : I) (covered : Finset S) (owner : {u // u ∈ covered} → C) :
    ∀ x : Point S G I C, parent (G := G) root covered owner (parent root covered owner x) =
      parent root covered owner x := by
  intro x
  cases x with
  | special u => by_cases h : u ∈ covered <;> simp [parent, h]
  | ordinary a i => rfl
  | center c => rfl

variable [Fintype S] [Fintype G] [Fintype I] [Fintype C]

theorem sum_except (root : I) (a : ℝ) :
    (∑ i : I, if i = root then 0 else a) = (Fintype.card I : ℝ) * a - a := by
  classical
  calc
    _ = (∑ _i : I, a) - ∑ i : I, if i = root then a else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i = root <;> simp [h]
    _ = _ := by simp

theorem parent_forest_cost (ell : ℝ) (nb : C → Set S)
    (root : I) (covered : Finset S) (owner : {u // u ∈ covered} → C)
    (howner : ∀ u : {u // u ∈ covered}, u.val ∈ nb (owner u)) :
    GraphCost.cost (edgeWeight ell nb) (GraphCost.parentGraph (parent (G := G) root covered owner)) =
      (covered.card : ℝ) + ell * Fintype.card G * ((Fintype.card I : ℝ) - 1) := by
  classical
  rw [GraphCost.parent_cost_sum _ _ (parent_idempotent (G := G) root covered owner),
    Point.sum_eq]
  have hs (u : S) :
      GraphCost.parentContribution (edgeWeight ell nb) (parent (G := G) root covered owner)
        (.special u) =
        if u ∈ covered then 1 else 0 := by
    by_cases h : u ∈ covered
    · simp [GraphCost.parentContribution, parent, h, Point.distance, Point.sameCluster,
        Point.unitAdjacent, howner]
    · simp [GraphCost.parentContribution, parent, h]
  have ho (a : G) (i : I) :
      GraphCost.parentContribution (edgeWeight ell nb) (parent (G := G) root covered owner)
        (.ordinary a i) =
        if i = root then 0 else ell := by
    by_cases h : i = root
    · simp [GraphCost.parentContribution, parent, h]
    · simp [GraphCost.parentContribution, parent, Point.distance, Point.sameCluster, h, Ne.symm h]
  simp_rw [hs, ho]
  simp [GraphCost.parentContribution, parent, sum_except, mul_sub]
  ring

theorem parent_forest_card (root : I) (covered : Finset S) (owner : {u // u ∈ covered} → C) :
    ((GraphCost.parentGraph (parent (G := G) root covered owner)).edgeFinset.card : ℝ) =
      (covered.card : ℝ) + (Fintype.card G : ℝ) * ((Fintype.card I : ℝ) - 1) := by
  classical
  rw [GraphCost.parent_card_sum _ (parent_idempotent (G := G) root covered owner)]
  rw [Point.sum_eq]
  have hs (u : S) :
      GraphCost.parentContribution (fun _ => 1) (parent (G := G) root covered owner) (.special u) =
        if u ∈ covered then 1 else 0 := by
    by_cases h : u ∈ covered <;> simp [GraphCost.parentContribution, parent, h]
  have ho (a : G) (i : I) :
      GraphCost.parentContribution (fun _ => 1) (parent (G := G) root covered owner) (.ordinary a i) =
        if i = root then 0 else 1 := by
    by_cases h : i = root
    · simp [GraphCost.parentContribution, parent, h]
    · simp [GraphCost.parentContribution, parent, h, Ne.symm h]
  simp_rw [hs, ho]
  simp [GraphCost.parentContribution, parent, sum_except, mul_sub]

theorem exists_tree_upper {ell : ℝ} (hEll : ell ≤ 2) (nb : C → Set S)
    (root : I) (covered : Finset S) (owner : {u // u ∈ covered} → C)
    (howner : ∀ u : {u // u ∈ covered}, u.val ∈ nb (owner u))
    [Nonempty G] :
    ∃ T : SimpleGraph (Point S G I C), T.IsTree ∧
      GraphCost.cost (edgeWeight ell nb) T ≤
        ell * Fintype.card G * ((Fintype.card I : ℝ) - 1) +
          2 * ((Fintype.card G : ℝ) + Fintype.card S - 1) -
            ((covered.card : ℝ) - 2 * Fintype.card C) := by
  classical
  have : Nonempty (Point S G I C) := ⟨.ordinary (Classical.arbitrary G) root⟩
  let F : SimpleGraph (Point S G I C) := GraphCost.parentGraph (parent root covered owner)
  have hF : F.IsAcyclic := GraphCost.parent_acyclic _ (parent_idempotent root covered owner)
  have htop : (⊤ : SimpleGraph (Point S G I C)).Connected := SimpleGraph.connected_top
  obtain ⟨T, hFT, _, hT⟩ := htop.exists_isTree_le_of_le_of_isAcyclic le_top hF
  refine ⟨T, hT, ?_⟩
  have hcost := GraphCost.cost_extension (edgeWeight ell nb) F T hFT 2 (fun e _ => by
    rcases e with ⟨x, y⟩
    exact Point.distance_le_two hEll nb x y)
  have hcard := hT.card_edgeFinset
  have hcard' :
      (T.edgeFinset.card : ℝ) + 1 =
        (Fintype.card S : ℝ) + Fintype.card G * Fintype.card I + Fintype.card C := by
    exact_mod_cast hcard.trans (Point.card_points)
  rw [parent_forest_cost ell nb root covered owner howner,
    parent_forest_card root covered owner] at hcost
  nlinarith

end HardCost

end SteinerLowerBound
