module

public import SteinerUpperBound.TerminalMST

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerUpperBound.TerminalMST

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V]

noncomputable def below (w : Sym2 V → ℝ) (T : Finset V) (a : ℝ) : SimpleGraph V :=
  GraphRank.ofEdges ((Network.completeOn T).edgeFinset.filter (fun e => w e < a))

theorem below_adj (w : Sym2 V → ℝ) (T : Finset V) (a : ℝ) (x y : V) :
    (below w T a).Adj x y ↔ x ≠ y ∧ x ∈ T ∧ y ∈ T ∧ w (Sym2.mk x y) < a := by
  simp only [below, GraphRank.ofEdges, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
    Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
    Network.completeOn_adj]
  tauto

theorem below_mono (w : Sym2 V → ℝ) (T : Finset V) {a b : ℝ} (hab : a ≤ b) :
    below w T a ≤ below w T b := by
  intro x y hxy
  obtain ⟨hne, hx, hy, hw⟩ := (below_adj w T a x y).mp hxy
  exact (below_adj w T b x y).mpr ⟨hne, hx, hy, hw.trans_le hab⟩

theorem below_input (w : Sym2 V → ℝ) (T : Finset V) (a : ℝ) :
    GraphRank.ofEdges ((input w T).takeWhile (fun e => decide (w e < a))).toFinset =
      below w T a := by
  rw [(WeightedSelection.sorted_cut (input w T) w a (input_sorted w T)).1]
  ext x y
  simp only [below, GraphRank.ofEdges, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
    Finset.mem_filter, List.mem_toFinset, List.mem_filter, input_mem, decide_eq_true_eq,
    SimpleGraph.mem_edgeFinset]

noncomputable def heavy (l : List (Sym2 V)) (w : Sym2 V → ℝ) (a : ℝ) : ℕ :=
  WeightedSelection.count (fun e => decide (a ≤ w e)) l

theorem heavy_profile (w : Sym2 V → ℝ) (T : Finset V) (a : ℝ) :
    heavy (SpanningForest.picked (input w T) ⊥) w a + GraphRank.rank (below w T a) =
      T.card - 1 := by
  let l := input w T
  let pre := l.takeWhile (fun e => decide (w e < a))
  let post := l.dropWhile (fun e => decide (w e < a))
  have hsplit : pre ++ post = l := List.takeWhile_append_dropWhile
  have hpre :
      (SpanningForest.picked pre ⊥).filter (fun e => decide (a ≤ w e)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    have hp : e ∈ pre := (SpanningForest.picked_sublist pre ⊥).subset he
    have hh : decide (w e < a) = true :=
      List.mem_takeWhile_imp (p := fun f : Sym2 V => decide (w f < a)) (l := l) hp
    have hw : w e < a := of_decide_eq_true hh
    simpa only [decide_eq_true_eq, not_le] using hw
  have hpost :
      (SpanningForest.picked post (SpanningForest.run pre ⊥)).filter
          (fun e => decide (a ≤ w e)) =
        SpanningForest.picked post (SpanningForest.run pre ⊥) := by
    apply List.filter_eq_self.mpr
    intro e he
    have hp : e ∈ post :=
      (SpanningForest.picked_sublist post (SpanningForest.run pre ⊥)).subset he
    exact decide_eq_true
      ((WeightedSelection.sorted_cut l w a (input_sorted w T)).2 e hp)
  have hjoin : SpanningForest.run post (SpanningForest.run pre ⊥) = graph w T := by
    rw [← SpanningForest.run_append, hsplit]
    rfl
  have hr := SpanningForest.rank_run post (SpanningForest.run pre ⊥)
  rw [hjoin, graph_rank] at hr
  have hp : GraphRank.rank (SpanningForest.run pre ⊥) = GraphRank.rank (below w T a) := by
    rw [rank_run_bot]
    exact congrArg GraphRank.rank (below_input w T a)
  change ((SpanningForest.picked l ⊥).filter (fun e => decide (a ≤ w e))).length +
    GraphRank.rank (below w T a) = T.card - 1
  rw [← hsplit, SpanningForest.picked_append, List.filter_append, hpre, hpost, List.nil_append]
  omega

theorem value_eq_sum (w : Sym2 V → ℝ) (T : Finset V) (hw : ∀ e, 0 ≤ w e) :
    value w T = ((SpanningForest.picked (input w T) ⊥).map w).sum := by
  rw [value_eq_cost w T hw, graph, SpanningForest.cost_run, Network.cost_bot, zero_add]

end SteinerUpperBound.TerminalMST
