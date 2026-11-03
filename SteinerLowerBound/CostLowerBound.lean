module

public import SteinerLowerBound.CostUpperBound

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace HardCost

variable {S G I C : Type*}

noncomputable def unitGraph (nb : C → Finset S) : SimpleGraph (Point S G I C) where
  Adj := Point.unitAdjacent (fun c => (nb c : Set S))
  symm.symm := by
    intro x y h
    cases x <;> cases y <;> simp_all [Point.unitAdjacent]
  loopless.irrefl := by intro x h; cases x <;> simp [Point.unitAdjacent] at h

noncomputable def clusterGraph : SimpleGraph (Point S G I C) where
  Adj x y := x ≠ y ∧ Point.sameCluster x y
  symm.symm := by
    intro x y h
    cases x <;> cases y <;> simp_all [Point.sameCluster, eq_comm]
  loopless.irrefl := by intro x h; exact h.1 rfl

theorem cluster_unit_disjoint (nb : C → Finset S) (x y : Point S G I C)
    (h : Point.sameCluster x y) : ¬Point.unitAdjacent (fun c => (nb c : Set S)) x y := by
  cases x <;> cases y <;> simp_all [Point.sameCluster, Point.unitAdjacent]

variable [Fintype S] [Fintype G] [Fintype I] [Fintype C]

theorem indicator_sum {V : Type*} [Fintype V] (T H : SimpleGraph V) (hHT : H ≤ T) :
    (∑ e ∈ T.edgeFinset, GraphCost.edgeIndicator H e) = Nat.card H.edgeSet := by
  classical
  unfold GraphCost.edgeIndicator
  rw [← Finset.sum_filter]
  have he : T.edgeFinset.filter (fun e => e ∈ H.edgeSet) = H.edgeFinset := by
    ext e
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
    exact and_iff_right_of_imp (fun h => SimpleGraph.edgeSet_mono hHT h)
  rw [he]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast (GraphCost.edgeCount_eq_card H).symm

theorem tree_cost_formula (ell : ℝ) (nb : C → Finset S) (T : SimpleGraph (Point S G I C)) :
    GraphCost.cost (edgeWeight ell (fun c => (nb c : Set S))) T =
      2 * Nat.card T.edgeSet -
        (2 - ell) * Nat.card (T ⊓ clusterGraph).edgeSet -
          Nat.card (T ⊓ unitGraph nb).edgeSet := by
  classical
  have hw (e : Sym2 (Point S G I C)) (he : e ∈ T.edgeFinset) :
      edgeWeight ell (fun c => (nb c : Set S)) e =
        2 - (2 - ell) * GraphCost.edgeIndicator (T ⊓ clusterGraph) e -
          GraphCost.edgeIndicator (T ⊓ unitGraph nb) e := by
    rcases e with ⟨x, y⟩
    have hxy : T.Adj x y := by simpa using he
    have hne := hxy.ne
    by_cases hc : Point.sameCluster x y
    · have hu := cluster_unit_disjoint nb x y hc
      simp [GraphCost.edgeIndicator, SimpleGraph.mem_edgeSet, edgeWeight_mk,
        Point.distance, hne, hc, hu, clusterGraph, unitGraph, hxy]
    · by_cases hu : Point.unitAdjacent (fun c => (nb c : Set S)) x y <;>
        norm_num [GraphCost.edgeIndicator, SimpleGraph.mem_edgeSet, edgeWeight_mk,
          Point.distance, hne, hc, hu, clusterGraph, unitGraph, hxy]
  calc
    _ = ∑ e ∈ T.edgeFinset,
        (2 - (2 - ell) * GraphCost.edgeIndicator (T ⊓ clusterGraph) e -
          GraphCost.edgeIndicator (T ⊓ unitGraph nb) e) :=
      Finset.sum_congr rfl hw
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
        indicator_sum T (T ⊓ clusterGraph) inf_le_left,
        indicator_sum T (T ⊓ unitGraph nb) inf_le_left]
      rw [← GraphCost.edgeCount_eq_card]
      ring

theorem small_edges_le (T : SimpleGraph (Point S G I C)) (hT : T.IsAcyclic) :
    Nat.card (T ⊓ clusterGraph).edgeSet ≤ Fintype.card G * Fintype.card I := by
  classical
  let ordinary : Finset (Point S G I C) :=
    (Finset.univ : Finset (G × I)).image (fun p => Point.ordinary p.1 p.2)
  have hs : (T ⊓ clusterGraph).support ⊆ (ordinary : Set (Point S G I C)) := by
    intro x hx
    obtain ⟨y, hxy⟩ := (SimpleGraph.mem_support _).mp hx
    cases x with
    | special u => cases y <;> simp [clusterGraph, Point.sameCluster] at hxy
    | center c => cases y <;> simp [clusterGraph, Point.sameCluster] at hxy
    | ordinary a i =>
        exact Finset.mem_image.mpr ⟨(a, i), Finset.mem_univ _, rfl⟩
  calc
    _ ≤ ordinary.card := by
      simpa only [← GraphCost.edgeCount_eq_card] using
        GraphCost.forest_edges_support_le _ (hT.anti inf_le_left) ordinary hs
    _ ≤ (Finset.univ : Finset (G × I)).card := Finset.card_image_le
    _ = _ := by simp

theorem unit_degree_le (T : SimpleGraph (Point S G I C)) (nb : C → Finset S) (c : C) :
    Nat.card ((T ⊓ unitGraph nb).neighborSet (.center c)) ≤ (nb c).card := by
  classical
  have hs :
      (T ⊓ unitGraph nb).neighborFinset (.center c) ⊆ (nb c).image Point.special := by
    intro x hx
    have hx' : (T ⊓ unitGraph nb).Adj (.center c) x := by simpa using hx
    cases x with
    | special u =>
        have hu : u ∈ nb c := hx'.2
        exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
    | ordinary a i => simp [unitGraph, Point.unitAdjacent] at hx'
    | center c' => simp [unitGraph, Point.unitAdjacent] at hx'
  rw [GraphCost.degreeCount_eq]
  exact (Finset.card_le_card hs).trans Finset.card_image_le

theorem unit_edge_sum (T : SimpleGraph (Point S G I C)) (nb : C → Finset S) :
    Nat.card (T ⊓ unitGraph nb).edgeSet =
      ∑ c, Nat.card ((T ⊓ unitGraph nb).neighborSet (.center c)) := by
  classical
  let left : Finset (Point S G I C) := Finset.univ.image Point.center
  let right : Finset (Point S G I C) := Finset.univ.image Point.special
  have hb : (T ⊓ unitGraph nb).IsBipartiteWith left right := by
    constructor
    · rw [Set.disjoint_left]
      intro x hx hy
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨u, _, h⟩ := Finset.mem_image.mp hy
      cases h
    · intro x y hxy
      have hu := hxy.2
      cases x <;> cases y <;> simp_all [unitGraph, Point.unitAdjacent, left, right]
  have heq := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hb
  simp only [← GraphCost.edgeCount_eq_card, ← GraphCost.degreeCount_eq] at heq
  rw [← heq]
  exact Finset.sum_image (by
    intro c _ c' _ h
    exact Point.center.inj h)

noncomputable def restrictNeighbors (nb : C → Finset S) (keep : Finset C) (c : C) : Finset S :=
  if c ∈ keep then nb c else ∅

omit [Fintype S] [Fintype C] in
@[simp]
theorem mem_restrictNeighbors (nb : C → Finset S) (keep : Finset C) (c : C) (u : S) :
    u ∈ restrictNeighbors nb keep c ↔ c ∈ keep ∧ u ∈ nb c := by
  by_cases h : c ∈ keep <;> simp [restrictNeighbors, h]

omit [Fintype S] [Fintype G] [Fintype I] in
theorem unit_graph_split (nb : C → Finset S) (keep : Finset C) :
    (unitGraph nb : SimpleGraph (Point S G I C)) =
      unitGraph (restrictNeighbors nb keep) ⊔ unitGraph (restrictNeighbors nb keepᶜ) := by
  ext x y
  cases x <;> cases y <;>
    simp [unitGraph, Point.unitAdjacent, Finset.mem_compl] <;> tauto

omit [Fintype S] [Fintype G] [Fintype I] in
theorem unit_graph_disjoint (nb : C → Finset S) (keep : Finset C) :
    Disjoint (unitGraph (G := G) (I := I) (restrictNeighbors nb keep))
      (unitGraph (restrictNeighbors nb keepᶜ)) := by
  rw [SimpleGraph.disjoint_left]
  intro x y
  cases x <;> cases y <;>
    simp [unitGraph, Point.unitAdjacent, Finset.mem_compl] <;> tauto

theorem unit_count_split (T : SimpleGraph (Point S G I C))
    (nb : C → Finset S) (keep : Finset C) :
    Nat.card (T ⊓ unitGraph nb).edgeSet =
      Nat.card (T ⊓ unitGraph (restrictNeighbors nb keep)).edgeSet +
        Nat.card (T ⊓ unitGraph (restrictNeighbors nb keepᶜ)).edgeSet := by
  have hd : Disjoint (T ⊓ unitGraph (restrictNeighbors nb keep))
      (T ⊓ unitGraph (restrictNeighbors nb keepᶜ)) :=
    (unit_graph_disjoint nb keep).mono inf_le_right inf_le_right
  rw [unit_graph_split nb keep, inf_sup_left]
  change ((T ⊓ unitGraph (restrictNeighbors nb keep)) ⊔
    (T ⊓ unitGraph (restrictNeighbors nb keepᶜ))).edgeSet.ncard = _
  rw [SimpleGraph.edgeSet_sup, Set.ncard_union_eq (SimpleGraph.disjoint_edgeSet.mpr hd)]
  rfl

theorem star_edges_le (T : SimpleGraph (Point S G I C)) (hT : T.IsAcyclic)
    (nb : C → Finset S) (stars : Finset C) (positive : Finset S)
    (hstar : ∀ c ∈ stars, nb c ⊆ positive) :
    Nat.card (T ⊓ unitGraph (restrictNeighbors nb stars)).edgeSet ≤
      positive.card + stars.card := by
  classical
  let vertices : Finset (Point S G I C) :=
    positive.image Point.special ∪ stars.image Point.center
  have hs : (T ⊓ unitGraph (restrictNeighbors nb stars)).support ⊆
      (vertices : Set (Point S G I C)) := by
    intro x hx
    obtain ⟨y, hxy⟩ := (SimpleGraph.mem_support _).mp hx
    have hu := hxy.2
    cases x with
    | special u =>
        cases y with
        | special v => simp [unitGraph, Point.unitAdjacent] at hu
        | ordinary a i => simp [unitGraph, Point.unitAdjacent] at hu
        | center c =>
            have hp : c ∈ stars ∧ u ∈ nb c := (mem_restrictNeighbors nb stars c u).mp hu
            exact Finset.mem_union_left _ (Finset.mem_image.mpr
              ⟨u, hstar c hp.1 hp.2, rfl⟩)
    | ordinary a i => cases y <;> simp [unitGraph, Point.unitAdjacent] at hu
    | center c =>
        cases y with
        | special u =>
            have hp : c ∈ stars ∧ u ∈ nb c := (mem_restrictNeighbors nb stars c u).mp hu
            exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c, hp.1, rfl⟩)
        | ordinary a i => simp [unitGraph, Point.unitAdjacent] at hu
        | center c' => simp [unitGraph, Point.unitAdjacent] at hu
  calc
    _ ≤ vertices.card := by
      simpa only [← GraphCost.edgeCount_eq_card] using
        GraphCost.forest_edges_support_le _ (hT.anti inf_le_left) vertices hs
    _ ≤ (positive.image (Point.special : S → Point S G I C)).card +
        (stars.image Point.center).card := Finset.card_union_le _ _
    _ ≤ _ := add_le_add Finset.card_image_le Finset.card_image_le

theorem filler_edges_le (T : SimpleGraph (Point S G I C)) (nb : C → Finset S)
    (stars : Finset C) (hfiller : ∀ c ∉ stars, (nb c).card ≤ 2) :
    Nat.card (T ⊓ unitGraph (restrictNeighbors nb starsᶜ)).edgeSet ≤
      2 * (Fintype.card C - stars.card) := by
  classical
  rw [unit_edge_sum]
  calc
    _ ≤ ∑ c : C, if c ∈ stars then 0 else 2 := by
      apply Finset.sum_le_sum
      intro c _
      have h := unit_degree_le T (restrictNeighbors nb starsᶜ) c
      by_cases hc : c ∈ stars
      · simpa [restrictNeighbors, hc] using h
      · have hb : (restrictNeighbors nb starsᶜ c).card ≤ 2 := by
          simpa [restrictNeighbors, hc] using hfiller c hc
        simpa [hc] using h.trans hb
    _ = _ := by
      have hfun (c : C) :
          (if c ∈ stars then 0 else (2 : ℕ)) = if c ∈ starsᶜ then 2 else 0 := by
        by_cases hc : c ∈ stars <;> simp [hc]
      simp_rw [hfun]
      rw [← Finset.sum_filter]
      have he : Finset.univ.filter (fun c : C => c ∈ starsᶜ) = starsᶜ := by
        ext c
        simp
      rw [he]
      simp [Finset.card_compl, mul_comm]

theorem unit_edges_le (T : SimpleGraph (Point S G I C)) (hT : T.IsAcyclic)
    (nb : C → Finset S) (stars : Finset C) (positive : Finset S)
    (hstar : ∀ c ∈ stars, nb c ⊆ positive)
    (hfiller : ∀ c ∉ stars, (nb c).card ≤ 2) :
    Nat.card (T ⊓ unitGraph nb).edgeSet ≤ positive.card + 2 * Fintype.card C := by
  rw [unit_count_split T nb stars]
  have hs := star_edges_le T hT nb stars positive hstar
  have hf := filler_edges_le T nb stars hfiller
  have hc : stars.card ≤ Fintype.card C := Finset.card_le_univ _
  omega

theorem tree_lower {ell : ℝ} (hEll : ell ≤ 2) (T : SimpleGraph (Point S G I C))
    (hT : T.IsTree) (nb : C → Finset S) (stars : Finset C) (positive : Finset S)
    (hstar : ∀ c ∈ stars, nb c ⊆ positive)
    (hfiller : ∀ c ∉ stars, (nb c).card ≤ 2) :
    ell * Fintype.card G * Fintype.card I +
        2 * Fintype.card S - 2 - positive.card ≤
      GraphCost.cost (edgeWeight ell (fun c => (nb c : Set S))) T := by
  have hs : (Nat.card (T ⊓ clusterGraph).edgeSet : ℝ) ≤
      (Fintype.card G : ℝ) * Fintype.card I := by
    exact_mod_cast small_edges_le T hT.isAcyclic
  have hu : (Nat.card (T ⊓ unitGraph nb).edgeSet : ℝ) ≤
      (positive.card : ℝ) + 2 * Fintype.card C := by
    exact_mod_cast unit_edges_le T hT.isAcyclic nb stars positive hstar hfiller
  have hcard : (Nat.card T.edgeSet : ℝ) + 1 =
      (Fintype.card S : ℝ) + Fintype.card G * Fintype.card I + Fintype.card C := by
    have h := hT.card_edgeFinset.trans (Point.card_points)
    rw [← GraphCost.edgeCount_eq_card] at h
    exact_mod_cast h
  have hsmall := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hEll)
  rw [tree_cost_formula]
  nlinarith

end HardCost

end SteinerLowerBound
