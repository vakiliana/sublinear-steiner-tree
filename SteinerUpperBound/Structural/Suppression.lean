module

public import SteinerUpperBound.Structural.Cleanup

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*}

namespace Tree

variable {I : Instance V}

noncomputable abbrev exchange (S : TreeGeometry.TreeSolution I)
    (u v a b : ↥S.vertices) (huv : S.graph.Adj u v)
    (ha : (S.graph.deleteEdges {s(u, v)}).Reachable u a)
    (hb : (S.graph.deleteEdges {s(u, v)}).Reachable v b) :
    TreeGeometry.TreeSolution I :=
  ⟨S.vertices, S.contains, exchangeEdge S.graph u v a b,
    exchangeEdge_tree S.graph S.isTree huv ha hb⟩

theorem exchange_preserves_terminals [Fintype V] (S : TreeGeometry.TreeSolution I)
    (u v a b : ↥S.vertices) (huv : S.graph.Adj u v)
    (ha : (S.graph.deleteEdges {s(u, v)}).Reachable u a)
    (hb : (S.graph.deleteEdges {s(u, v)}).Reachable v b)
    (hu : (u : V) ∉ I.terminals) :
    terminalGraph S ≤ terminalGraph (exchange S u v a b huv ha hb) := by
  intro x y hxy
  obtain ⟨hxy, hT⟩ := hxy
  obtain ⟨_, hxT, hyT⟩ := (Network.completeOn_adj _ _ _).mp hT
  change (S.graph.map Subtype.val).Adj x y at hxy
  obtain ⟨hne, x', y', hab, rfl, rfl⟩ :=
    (SimpleGraph.map_adj' Subtype.val S.graph x y).mp hxy
  have hnot : s(x', y') ≠ s(u, v) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨_, h⟩
    · exact hu (h ▸ hxT)
    · exact hu (h ▸ hyT)
  refine ⟨?_, hT⟩
  exact (SimpleGraph.map_adj' _ _ _ _).mpr
    ⟨hne, x', y', Or.inl (SimpleGraph.deleteEdges_adj.mpr
      ⟨hab, by simpa only [Set.mem_singleton_iff] using hnot⟩), rfl, rfl⟩

theorem sibling_cut_reachable (S : TreeGeometry.TreeSolution I)
    (v x y : ↥S.vertices) (hvx : S.graph.Adj v x) (hvy : S.graph.Adj v y)
    (hxy : x ≠ y) : (S.graph.deleteEdges {s(v, x)}).Reachable v y := by
  apply SimpleGraph.Adj.reachable
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨hvy, ?_⟩
  rw [Set.mem_singleton_iff]
  intro h
  rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h, _⟩
  · exact hxy h.symm
  · exact hvx.ne h

noncomputable abbrev suppressBefore (S : TreeGeometry.TreeSolution I)
    (v x y : ↥S.vertices) (hvx : S.graph.Adj v x) (hvy : S.graph.Adj v y)
    (hxy : x ≠ y) : TreeGeometry.TreeSolution I :=
  exchange S v x y x hvx (sibling_cut_reachable S v x y hvx hvy hxy)
    (SimpleGraph.Reachable.refl x)

theorem suppressBefore_adj (S : TreeGeometry.TreeSolution I)
    (v x y : ↥S.vertices) (hvx : S.graph.Adj v x) (hvy : S.graph.Adj v y)
    (hxy : x ≠ y) (hn : ∀ z, S.graph.Adj v z → z = x ∨ z = y) (z : ↥S.vertices) :
    (suppressBefore S v x y hvx hvy hxy).graph.Adj v z ↔ z = y := by
  constructor
  · intro h
    rcases h with h | h
    · obtain ⟨hvz, hnot⟩ := SimpleGraph.deleteEdges_adj.mp h
      rcases hn z hvz with h | h
      · exact False.elim (hnot (by simpa only [h, Set.mem_singleton_iff]))
      · exact h
    · rcases (SimpleGraph.edge_adj y x v z).mp h with ⟨h | h, _⟩
      · exact False.elim (hvy.ne h.1)
      · exact False.elim (hvx.ne h.1)
  · rintro rfl
    apply Or.inl
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hvy, ?_⟩
    rw [Set.mem_singleton_iff]
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h, _⟩
    · exact hxy h.symm
    · exact hvx.ne h

theorem suppressBefore_degree (S : TreeGeometry.TreeSolution I)
    (v x y : ↥S.vertices) (hvx : S.graph.Adj v x) (hvy : S.graph.Adj v y)
    (hxy : x ≠ y) (hn : ∀ z, S.graph.Adj v z → z = x ∨ z = y) :
    (suppressBefore S v x y hvx hvy hxy).graph.degree v = 1 := by
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  refine ⟨y, (suppressBefore_adj S v x y hvx hvy hxy hn y).mpr rfl, ?_⟩
  intro z hz
  exact (suppressBefore_adj S v x y hvx hvy hxy hn z).mp hz

noncomputable abbrev suppress (S : TreeGeometry.TreeSolution I)
    (v x y : ↥S.vertices) (hv : (v : V) ∉ I.terminals)
    (hvx : S.graph.Adj v x) (hvy : S.graph.Adj v y) (hxy : x ≠ y)
    (hn : ∀ z, S.graph.Adj v z → z = x ∨ z = y) :
    TreeGeometry.TreeSolution I :=
  deleteLeaf (suppressBefore S v x y hvx hvy hxy) v hv
    (suppressBefore_degree S v x y hvx hvy hxy hn)

theorem suppress_cost_le (S : TreeGeometry.TreeSolution I)
    (v x y : ↥S.vertices) (hv : (v : V) ∉ I.terminals)
    (hvx : S.graph.Adj v x) (hvy : S.graph.Adj v y) (hxy : x ≠ y)
    (hn : ∀ z, S.graph.Adj v z → z = x ∨ z = y)
    (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) :
    GraphCost.cost (fun e => w (e.map Subtype.val)) (suppress S v x y hv hvx hvy hxy hn).graph ≤
      GraphCost.cost (fun e => w (e.map Subtype.val)) S.graph -
        w s((v : V), (x : V)) - w s((v : V), (y : V)) +
          w s((y : V), (x : V)) := by
  let S₀ := suppressBefore S v x y hvx hvy hxy
  have hd := suppressBefore_degree S v x y hvx hvy hxy hn
  obtain ⟨z, hz, he⟩ := deleteLeaf_cost_add S₀ v hv hd w
  have hzy : z = y := (suppressBefore_adj S v x y hvx hvy hxy hn z).mp hz
  subst z
  have hs := exchangeEdge_cost_le S.graph (fun e => w (e.map Subtype.val))
    (fun e => hw _) (a := y) (b := x) hvx
  simp only [Sym2.map_mk] at hs
  change GraphCost.cost (fun e => w (e.map Subtype.val)) (deleteLeaf S₀ v hv hd).graph ≤ _
  change GraphCost.cost (fun e => w (e.map Subtype.val)) S₀.graph ≤ _ at hs
  linarith

theorem suppress_preserves_terminals [Fintype V] (S : TreeGeometry.TreeSolution I)
    (v x y : ↥S.vertices) (hv : (v : V) ∉ I.terminals)
    (hvx : S.graph.Adj v x) (hvy : S.graph.Adj v y) (hxy : x ≠ y)
    (hn : ∀ z, S.graph.Adj v z → z = x ∨ z = y) :
    terminalGraph S ≤ terminalGraph (suppress S v x y hv hvx hvy hxy hn) :=
  (exchange_preserves_terminals S v x y x hvx
    (sibling_cut_reachable S v x y hvx hvy hxy) (SimpleGraph.Reachable.refl x) hv).trans
      (deleteLeaf_preserves_terminals (suppressBefore S v x y hvx hvy hxy) v hv
        (suppressBefore_degree S v x y hvx hvy hxy hn))

end Tree

end SteinerUpperBound.Structural
