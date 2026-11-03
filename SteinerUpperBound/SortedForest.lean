module

public import SteinerUpperBound.TerminalMST

@[expose] public section

namespace SteinerUpperBound.TerminalMST.SortedInput

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V]

noncomputable abbrev forest (l : List (Sym2 V)) : SimpleGraph V :=
  SpanningForest.run l ⊥

theorem rank (l : List (Sym2 V)) (T : Finset V)
    (hspan : GraphRank.ofEdges l.toFinset = Network.completeOn T) :
    GraphRank.rank (forest l) = T.card - 1 := by
  rw [forest, rank_run_bot, hspan, GraphRank.rank_completeOn]

theorem feasible (l : List (Sym2 V)) (T : Finset V)
    (hspan : GraphRank.ofEdges l.toFinset = Network.completeOn T) :
    Network.Feasible T (forest l) := by
  have hs : GraphRank.space (forest l) = GraphRank.space (Network.completeOn T) := by
    rw [forest, span_run_bot, hspan]
  intro x hx y hy
  apply (GraphRank.mem_space_iff _ _ _).mp
  rw [hs]
  exact GraphRank.reachable_mem _ (Network.completeOn_feasible T x hx y hy)

theorem terminalOnly (l : List (Sym2 V)) (T : Finset V)
    (hspan : GraphRank.ofEdges l.toFinset = Network.completeOn T) :
    Network.TerminalOnly T (forest l) := by
  have h := SpanningForest.run_le l (⊥ : SimpleGraph V)
  rw [hspan, bot_sup_eq] at h
  intro x y hxy
  exact (Network.completeOn_adj T x y).mp (h hxy) |>.2

theorem covers (l : List (Sym2 V)) (T : Finset V)
    (hspan : GraphRank.ofEdges l.toFinset = Network.completeOn T)
    (G : SimpleGraph V) (hT : Network.TerminalOnly T G) :
    ∀ e ∈ G.edgeSet, e ∈ l := by
  intro e he
  rcases e with ⟨x, y⟩
  have hxy := (SimpleGraph.mem_edgeSet G).mp he
  obtain ⟨hx, hy⟩ := hT x y hxy
  have ht : (GraphRank.ofEdges l.toFinset).Adj x y := by
    rw [hspan]
    exact (Network.completeOn_adj T x y).mpr ⟨hxy.ne, hx, hy⟩
  have hm : Sym2.mk x y ∈ l ∧ x ≠ y := by
    simpa only [GraphRank.ofEdges, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
      List.mem_toFinset] using ht
  exact hm.1

theorem tail_counts (l : List (Sym2 V)) (T : Finset V)
    (hspan : GraphRank.ofEdges l.toFinset = Network.completeOn T)
    (G : SimpleGraph V) (hG : Network.Feasible T G) (hT : Network.TerminalOnly T G) (i : ℕ) :
    WeightedSelection.count Prod.snd ((SpanningForest.trace l ⊥).drop i) ≤
      WeightedSelection.count (fun z => edgeFlag G z.1)
        ((SpanningForest.trace l ⊥).drop i) := by
  let pre := l.take i
  let post := l.drop i
  have hr := GraphRank.rank_mono (cover_split G l (covers l T hspan G hT) i)
  have hc := GraphRank.rank_add_edges_le (GraphRank.ofEdges pre.toFinset)
    (post.filter (edgeFlag G)).toFinset
  have hlen := List.toFinset_card_le (post.filter (edgeFlag G))
  have hp := rank_run_bot pre
  have ht := SpanningForest.rank_run post (SpanningForest.run pre ⊥)
  have hjoin : SpanningForest.run post (SpanningForest.run pre ⊥) = forest l := by
    dsimp only [pre, post]
    rw [← SpanningForest.run_append, List.take_append_drop]
  rw [hjoin, rank l T hspan] at ht
  rw [GraphRank.rank_of_feasible T G hG hT] at hr
  rw [SpanningForest.trace_drop, SpanningForest.trace_count, SpanningForest.trace_count_other]
  change (SpanningForest.picked post (SpanningForest.run pre ⊥)).length ≤
    (post.filter (edgeFlag G)).length
  dsimp only [pre, post] at hr hc hlen hp ht ⊢
  omega

theorem cost_le (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (l : List (Sym2 V)) (T : Finset V)
    (hspan : GraphRank.ofEdges l.toFinset = Network.completeOn T) (hn : l.Nodup)
    (hs : l.Pairwise (fun e f => w e ≤ w f))
    (G : SimpleGraph V) (hG : Network.Feasible T G) (hT : Network.TerminalOnly T G) :
    GraphCost.cost w (forest l) ≤ GraphCost.cost w G := by
  let tr := SpanningForest.trace l ⊥
  have hsorted : tr.Pairwise (fun x y => w x.1 ≤ w y.1) := by
    have h : (tr.map Prod.fst).Pairwise (fun x y => w x ≤ w y) := by
      rw [SpanningForest.trace_map]
      exact hs
    exact (List.pairwise_map (f := Prod.fst)
      (R := fun x y : Sym2 V => w x ≤ w y)).mp h
  have hdom := WeightedSelection.le_of_tail_counts tr (fun x => w x.1) Prod.snd
    (fun z => edgeFlag G z.1) (fun x _ => hw _) hsorted (tail_counts l T hspan G hG hT)
  rw [WeightedSelection.weighted_eq_sum, WeightedSelection.weighted_eq_sum,
    SpanningForest.trace_weight, SpanningForest.trace_weight_other] at hdom
  have hcost := SpanningForest.cost_run w l (⊥ : SimpleGraph V)
  rw [Network.cost_bot, zero_add] at hcost
  change GraphCost.cost w (SpanningForest.run l ⊥) ≤ _
  rw [hcost]
  exact hdom.trans_eq (comparison_sum w G l hn (covers l T hspan G hT))

theorem value_eq_cost (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (l : List (Sym2 V)) (T : Finset V)
    (hspan : GraphRank.ofEdges l.toFinset = Network.completeOn T) (hn : l.Nodup)
    (hs : l.Pairwise (fun e f => w e ≤ w f)) :
    value w T = GraphCost.cost w (forest l) := by
  apply le_antisymm
  · exact Network.minimum_le _ _ _ _ ⟨feasible l T hspan, terminalOnly l T hspan⟩
  · obtain ⟨G, hG, he⟩ := Network.minimum_attained w
      (fun G => Network.Feasible T G ∧ Network.TerminalOnly T G) _
    exact (cost_le w hw l T hspan hn hs G hG.1 hG.2).trans_eq he

theorem value_eq_sum (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (l : List (Sym2 V)) (T : Finset V)
    (hspan : GraphRank.ofEdges l.toFinset = Network.completeOn T) (hn : l.Nodup)
    (hs : l.Pairwise (fun e f => w e ≤ w f)) :
    value w T = ((SpanningForest.picked l ⊥).map w).sum := by
  rw [value_eq_cost w hw l T hspan hn hs, forest, SpanningForest.cost_run, Network.cost_bot,
    zero_add]

end SteinerUpperBound.TerminalMST.SortedInput
