module

public import SteinerUpperBound.SpanningForest

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerUpperBound.TerminalMST

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V]

noncomputable def edgeFlag (G : SimpleGraph V) (e : Sym2 V) : Bool :=
  decide (e ∈ G.edgeSet)

theorem edgeFlag_true (G : SimpleGraph V) (e : Sym2 V) :
    edgeFlag G e = true ↔ e ∈ G.edgeSet := by simp [edgeFlag]

noncomputable def input (w : Sym2 V → ℝ) (T : Finset V) : List (Sym2 V) :=
  (Network.completeOn T).edgeFinset.toList.mergeSort (fun e f => decide (w e ≤ w f))

theorem input_perm (w : Sym2 V → ℝ) (T : Finset V) :
    (input w T).Perm (Network.completeOn T).edgeFinset.toList :=
  List.mergeSort_perm _ _

theorem input_nodup (w : Sym2 V → ℝ) (T : Finset V) : (input w T).Nodup :=
  (input_perm w T).nodup_iff.mpr (Finset.nodup_toList _)

theorem input_mem (w : Sym2 V → ℝ) (T : Finset V) (e : Sym2 V) :
    e ∈ input w T ↔ e ∈ (Network.completeOn T).edgeSet := by
  have h := (input_perm w T).mem_iff (a := e)
  simpa only [Finset.mem_toList, SimpleGraph.mem_edgeFinset] using h

theorem input_edges (w : Sym2 V → ℝ) (T : Finset V) :
    GraphRank.ofEdges (input w T).toFinset = Network.completeOn T := by
  ext x y
  simp only [GraphRank.ofEdges, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
    List.mem_toFinset, input_mem, SimpleGraph.mem_edgeSet]
  exact ⟨And.left, fun h => ⟨h, h.ne⟩⟩

theorem input_sorted (w : Sym2 V → ℝ) (T : Finset V) :
    (input w T).Pairwise (fun e f => w e ≤ w f) := by
  have htrans (a b c : Sym2 V) :
      decide (w a ≤ w b) = true → decide (w b ≤ w c) = true → decide (w a ≤ w c) = true := by
    simp only [decide_eq_true_eq]
    exact le_trans
  have htotal (a b : Sym2 V) :
      (decide (w a ≤ w b) || decide (w b ≤ w a)) = true := by
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total (w a) (w b)
  simpa only [input, decide_eq_true_eq] using
    List.pairwise_mergeSort htrans htotal (Network.completeOn T).edgeFinset.toList

theorem span_run_bot (l : List (Sym2 V)) :
    GraphRank.space (SpanningForest.run l ⊥) = GraphRank.space (GraphRank.ofEdges l.toFinset) := by
  rw [SpanningForest.run_space, GraphRank.space_bot, bot_sup_eq]

theorem rank_run_bot (l : List (Sym2 V)) :
    GraphRank.rank (SpanningForest.run l ⊥) = GraphRank.rank (GraphRank.ofEdges l.toFinset) := by
  unfold GraphRank.rank
  rw [span_run_bot]

noncomputable def graph (w : Sym2 V → ℝ) (T : Finset V) : SimpleGraph V :=
  SpanningForest.run (input w T) ⊥

theorem graph_space (w : Sym2 V → ℝ) (T : Finset V) :
    GraphRank.space (graph w T) = GraphRank.space (Network.completeOn T) := by
  rw [graph, span_run_bot, input_edges]

theorem graph_feasible (w : Sym2 V → ℝ) (T : Finset V) : Network.Feasible T (graph w T) := by
  intro x hx y hy
  apply (GraphRank.mem_space_iff _ _ _).mp
  rw [graph_space]
  by_cases hxy : x = y
  · subst y
    rw [GraphRank.delta_self]
    exact Submodule.zero_mem _
  · exact GraphRank.edge_mem _ ((Network.completeOn_adj T x y).mpr ⟨hxy, hx, hy⟩)

theorem graph_terminalOnly (w : Sym2 V → ℝ) (T : Finset V) :
    Network.TerminalOnly T (graph w T) := by
  have h := SpanningForest.run_le (input w T) (⊥ : SimpleGraph V)
  rw [input_edges, bot_sup_eq] at h
  intro x y hxy
  exact ((Network.completeOn_adj T x y).mp (h hxy)).2

theorem graph_rank (w : Sym2 V → ℝ) (T : Finset V) : GraphRank.rank (graph w T) = T.card - 1 :=
  GraphRank.rank_of_feasible T _ (graph_feasible w T) (graph_terminalOnly w T)

theorem cover_split (G : SimpleGraph V) (l : List (Sym2 V))
    (hcover : ∀ e ∈ G.edgeSet, e ∈ l) (i : ℕ) :
    G ≤ GraphRank.ofEdges (l.take i).toFinset ⊔
      GraphRank.ofEdges ((l.drop i).filter (edgeFlag G)).toFinset := by
  intro x y hxy
  have he : Sym2.mk x y ∈ G.edgeSet := (SimpleGraph.mem_edgeSet G).mpr hxy
  have hl := hcover _ he
  rw [← List.take_append_drop i l, List.mem_append] at hl
  rcases hl with hl | hl
  · apply Or.inl
    simpa only [GraphRank.ofEdges, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
      List.mem_toFinset] using And.intro hl hxy.ne
  · apply Or.inr
    simpa only [GraphRank.ofEdges, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
      List.mem_toFinset, List.mem_filter, edgeFlag_true] using
        And.intro (And.intro hl he) hxy.ne

theorem tail_counts (w : Sym2 V → ℝ) (T : Finset V) (G : SimpleGraph V)
    (hG : Network.Feasible T G) (hT : Network.TerminalOnly T G) (i : ℕ) :
    WeightedSelection.count Prod.snd ((SpanningForest.trace (input w T) ⊥).drop i) ≤
      WeightedSelection.count (fun z => edgeFlag G z.1)
        ((SpanningForest.trace (input w T) ⊥).drop i) := by
  let l := input w T
  let pre := l.take i
  let post := l.drop i
  have hcover : ∀ e ∈ G.edgeSet, e ∈ l := by
    intro e he
    apply (input_mem w T e).mpr
    rcases e with ⟨x, y⟩
    have hxy := (SimpleGraph.mem_edgeSet G).mp he
    obtain ⟨hx, hy⟩ := hT x y hxy
    exact (SimpleGraph.mem_edgeSet _).mpr ((Network.completeOn_adj T x y).mpr ⟨hxy.ne, hx, hy⟩)
  have hr := GraphRank.rank_mono (cover_split G l hcover i)
  have hc := GraphRank.rank_add_edges_le (GraphRank.ofEdges pre.toFinset)
    (post.filter (edgeFlag G)).toFinset
  have hlen := List.toFinset_card_le (post.filter (edgeFlag G))
  have hp := rank_run_bot pre
  have ht := SpanningForest.rank_run post (SpanningForest.run pre ⊥)
  have hjoin : SpanningForest.run post (SpanningForest.run pre ⊥) = graph w T := by
    dsimp only [pre, post, l]
    rw [← SpanningForest.run_append, List.take_append_drop]
    rfl
  rw [hjoin, graph_rank] at ht
  rw [GraphRank.rank_of_feasible T G hG hT] at hr
  rw [SpanningForest.trace_drop, SpanningForest.trace_count, SpanningForest.trace_count_other]
  change (SpanningForest.picked post (SpanningForest.run pre ⊥)).length ≤
    (post.filter (edgeFlag G)).length
  dsimp only [pre, post] at hr hc hlen hp ht ⊢
  omega

theorem comparison_sum (w : Sym2 V → ℝ) (G : SimpleGraph V) (l : List (Sym2 V))
    (hl : l.Nodup) (hcover : ∀ e ∈ G.edgeSet, e ∈ l) :
    (l.map (fun e => if edgeFlag G e then w e else 0)).sum = GraphCost.cost w G := by
  have hp (e : Sym2 V) :
      (if edgeFlag G e then w e else 0) = SpanningForest.contribution w G e := by
    by_cases he : e ∈ G.edgeSet <;> simp [edgeFlag, SpanningForest.contribution, he]
  simp_rw [hp]
  rw [← List.sum_toFinset _ hl, SpanningForest.cost_sum]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  have hne : e ∉ G.edgeSet := fun hm => he (by simpa using hcover e hm)
  simp [SpanningForest.contribution, hne]

theorem graph_cost_le (w : Sym2 V → ℝ) (T : Finset V) (hw : ∀ e, 0 ≤ w e)
    (G : SimpleGraph V) (hG : Network.Feasible T G) (hT : Network.TerminalOnly T G) :
    GraphCost.cost w (graph w T) ≤ GraphCost.cost w G := by
  let l := input w T
  let tr := SpanningForest.trace l ⊥
  have hs : tr.Pairwise (fun x y => w x.1 ≤ w y.1) := by
    have h : (tr.map Prod.fst).Pairwise (fun x y => w x ≤ w y) := by
      rw [SpanningForest.trace_map]
      exact input_sorted w T
    exact (List.pairwise_map (f := Prod.fst)
      (R := fun x y : Sym2 V => w x ≤ w y)).mp h
  have hdom := WeightedSelection.le_of_tail_counts tr (fun x => w x.1) Prod.snd
    (fun z => edgeFlag G z.1) (fun x _ => hw _) hs (tail_counts w T G hG hT)
  rw [WeightedSelection.weighted_eq_sum, WeightedSelection.weighted_eq_sum,
    SpanningForest.trace_weight, SpanningForest.trace_weight_other] at hdom
  have hcost := SpanningForest.cost_run w l (⊥ : SimpleGraph V)
  rw [Network.cost_bot, zero_add] at hcost
  change GraphCost.cost w (SpanningForest.run l ⊥) ≤ _
  rw [hcost]
  apply hdom.trans_eq
  apply comparison_sum w G l (input_nodup w T)
  intro e he
  rcases e with ⟨x, y⟩
  have hxy := (SimpleGraph.mem_edgeSet G).mp he
  obtain ⟨hx, hy⟩ := hT x y hxy
  exact (input_mem w T _).mpr ((SimpleGraph.mem_edgeSet _).mpr
    ((Network.completeOn_adj T x y).mpr ⟨hxy.ne, hx, hy⟩))

noncomputable def value (w : Sym2 V → ℝ) (T : Finset V) : ℝ :=
  Network.minimum w (fun G => Network.Feasible T G ∧ Network.TerminalOnly T G)
    ⟨Network.completeOn T, Network.completeOn_feasible _, Network.completeOn_terminalOnly _⟩

theorem value_eq_cost (w : Sym2 V → ℝ) (T : Finset V) (hw : ∀ e, 0 ≤ w e) :
    value w T = GraphCost.cost w (graph w T) := by
  apply le_antisymm
  · exact Network.minimum_le _ _ _ _ ⟨graph_feasible w T, graph_terminalOnly w T⟩
  · obtain ⟨G, hG, he⟩ := Network.minimum_attained w
      (fun G => Network.Feasible T G ∧ Network.TerminalOnly T G) _
    exact (graph_cost_le w T hw G hG.1 hG.2).trans_eq he

theorem value_instance (I : Instance V) : value I.weight I.terminals = I.mst := rfl

end SteinerUpperBound.TerminalMST
