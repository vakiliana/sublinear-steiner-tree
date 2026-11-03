module

public import SteinerLowerBound.SteinerOptimum

@[expose] public section

namespace SteinerLowerBound.MetricComparison.Padding

open scoped BigOperators Classical

variable {V W : Type*}

theorem connected_map (G : SimpleGraph V) (hG : G.Connected)
    (f : V → W) (hf : Function.Surjective f) : (G.map f).Connected := by
  have hr {u v : V} (h : G.Reachable u v) : (G.map f).Reachable (f u) (f v) := by
    obtain ⟨p⟩ := h
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons u v w ha p ih =>
      by_cases he : f u = f v
      · simpa only [he] using ih
      · exact (SimpleGraph.map_adj_apply' ha he).reachable.trans ih
  letI : Nonempty W := ⟨f (Classical.choice hG.nonempty)⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨u', rfl⟩ := hf u
  obtain ⟨v', rfl⟩ := hf v
  exact hr (hG.preconnected u' v')

theorem edgeFinset_map_subset [Fintype V] [Fintype W]
    (G : SimpleGraph V) (f : V → W)
    [DecidableRel G.Adj] [DecidableRel (G.map f).Adj] :
    (G.map f).edgeFinset ⊆ G.edgeFinset.image (Sym2.map f) := by
  classical
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
    have ha := (SimpleGraph.map_adj' f G u v).mp
      (SimpleGraph.mem_edgeSet (G.map f) |>.mp (SimpleGraph.mem_edgeFinset.mp he))
    obtain ⟨_, u', v', huv, rfl, rfl⟩ := ha
    exact Finset.mem_image.mpr
      ⟨Sym2.mk u' v', SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr huv), rfl⟩

theorem cost_map_le [Fintype V] [Fintype W] (G : SimpleGraph V) (f : V → W)
    (w : Sym2 V → ℝ) (w' : Sym2 W → ℝ)
    (hw' : ∀ e, 0 ≤ w' e)
    (hcost : ∀ e ∈ G.edgeFinset, w' (Sym2.map f e) ≤ w e) :
    GraphCost.cost w' (G.map f) ≤ GraphCost.cost w G := by
  classical
  letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel (G.map f).Adj := fun _ _ => Classical.propDecidable _
  unfold GraphCost.cost
  calc
    _ ≤ ∑ e ∈ G.edgeFinset.image (Sym2.map f), w' e :=
      Finset.sum_le_sum_of_subset_of_nonneg (edgeFinset_map_subset G f)
        (fun e _ _ => hw' e)
    _ ≤ ∑ e ∈ G.edgeFinset, w' (Sym2.map f e) :=
      Finset.sum_image_le_of_nonneg (fun e _ => hw' e)
    _ ≤ _ := Finset.sum_le_sum hcost

theorem exists_tree_cost_le [Fintype V] [Fintype W]
    (G : SimpleGraph V) (hG : G.Connected) (f : V → W) (hf : Function.Surjective f)
    (w : Sym2 V → ℝ) (w' : Sym2 W → ℝ)
    (hw' : ∀ e, 0 ≤ w' e)
    (hcost : ∀ e ∈ G.edgeFinset, w' (Sym2.map f e) ≤ w e) :
    ∃ T : SimpleGraph W, T.IsTree ∧ GraphCost.cost w' T ≤ GraphCost.cost w G := by
  classical
  letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel (G.map f).Adj := fun _ _ => Classical.propDecidable _
  obtain ⟨T, hT, ht⟩ := (connected_map G hG f hf).exists_isTree_le
  refine ⟨T, ht, ?_⟩
  apply le_trans _ (cost_map_le G f w w' hw' hcost)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (SimpleGraph.edgeFinset_mono hT) (fun e _ _ => hw' e)

end SteinerLowerBound.MetricComparison.Padding
