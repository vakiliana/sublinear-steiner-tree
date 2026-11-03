module

public import SteinerUpperBound.MSTRankIntegral

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerUpperBound.Network

open SteinerLowerBound
open scoped Classical BigOperators Interval

variable {V : Type*}

theorem reachable_lift (G H : SimpleGraph V)
    (hGH : ∀ x y, G.Adj x y → H.Reachable x y) {x y : V} (hxy : G.Reachable x y) :
    H.Reachable x y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z hxy p ih => exact (hGH x y hxy).trans ih

theorem reachable_map {W : Type*} (G : SimpleGraph V) (f : V → W)
    {x y : V} (hxy : G.Reachable x y) :
    (G.map f).Reachable (f x) (f y) := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z hxy p ih =>
      by_cases he : f x = f y
      · simpa only [he] using ih
      · exact (SimpleGraph.map_adj_apply' hxy he).reachable.trans ih

variable [Fintype V]

theorem cost_sup_le (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) (G H : SimpleGraph V) :
    GraphCost.cost w (G ⊔ H) ≤ GraphCost.cost w G + GraphCost.cost w H := by
  calc
    _ = ∑ e, SpanningForest.contribution w (G ⊔ H) e := SpanningForest.cost_sum _ _
    _ ≤ ∑ e, (SpanningForest.contribution w G e + SpanningForest.contribution w H e) := by
      apply Finset.sum_le_sum
      intro e _
      by_cases hg : e ∈ G.edgeSet <;> by_cases hh : e ∈ H.edgeSet <;>
        simp [SpanningForest.contribution, SimpleGraph.edgeSet_sup, hg, hh] <;> linarith [hw e]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← SpanningForest.cost_sum, ← SpanningForest.cost_sum]

theorem cost_delete_zeroed (w : Sym2 V → ℝ) (G F : SimpleGraph V) :
    GraphCost.cost w (G.deleteEdges F.edgeSet) = GraphCost.cost (TerminalMST.zeroed w F) G := by
  rw [SpanningForest.cost_sum, SpanningForest.cost_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hg : e ∈ G.edgeSet <;> by_cases hf : e ∈ F.edgeSet <;>
    simp [SpanningForest.contribution, TerminalMST.zeroed, SimpleGraph.edgeSet_deleteEdges, hg, hf]

theorem optimum_lifting (I : Instance V) (F K : SimpleGraph V)
    (hFK : ∀ x y, F.Adj x y → K.Reachable x y) :
    I.optimum ≤ TerminalMST.value (TerminalMST.zeroed I.weight F) I.terminals +
      GraphCost.cost I.weight K := by
  let G := TerminalMST.graph (TerminalMST.zeroed I.weight F) I.terminals
  let H := G.deleteEdges F.edgeSet ⊔ K
  have hr : ∀ x y, G.Adj x y → H.Reachable x y := by
    intro x y hxy
    by_cases hf : F.Adj x y
    · exact (hFK x y hf).mono le_sup_right
    · have he : Sym2.mk x y ∉ F.edgeSet :=
        fun h => hf ((SimpleGraph.mem_edgeSet F).mp h)
      exact SimpleGraph.Adj.reachable (G := H)
        (Or.inl (SimpleGraph.deleteEdges_adj.mpr ⟨hxy, he⟩))
  have hfeas : Feasible I.terminals H := by
    intro x hx y hy
    exact reachable_lift G H hr (TerminalMST.graph_feasible _ _ x hx y hy)
  have hcost := (I.optimum_le H hfeas).trans
    (cost_sup_le I.weight I.weight_nonneg (G.deleteEdges F.edgeSet) K)
  rw [cost_delete_zeroed, ← TerminalMST.value_eq_cost _ _ (TerminalMST.zeroed_nonneg _ _ I.weight_nonneg)] at hcost
  exact hcost

theorem benefit_lifting (I : Instance V) (F K : SimpleGraph V)
    (hFK : ∀ x y, F.Adj x y → K.Reachable x y) :
    I.mst - TerminalMST.value (TerminalMST.zeroed I.weight F) I.terminals -
        GraphCost.cost I.weight K ≤ I.mst - I.optimum := by
  linarith [optimum_lifting I F K hFK]

theorem integral_lifting (I : Instance V) (F K : SimpleGraph V)
    (hF : TerminalOnly I.terminals F)
    (hFK : ∀ x y, F.Adj x y → K.Reachable x y)
    (M : ℝ) (hM₀ : 0 ≤ M)
    (hM : ∀ e ∈ (completeOn I.terminals).edgeSet, I.weight e ≤ M) :
    (∫ a in (0 : ℝ)..M, GraphRank.gain (TerminalMST.below I.weight I.terminals a) F) -
        GraphCost.cost I.weight K ≤ I.mst - I.optimum := by
  rw [← TerminalMST.value_difference_integral I.weight I.terminals F I.weight_nonneg hF M hM₀ hM,
    TerminalMST.value_instance]
  exact benefit_lifting I F K hFK

end SteinerUpperBound.Network
