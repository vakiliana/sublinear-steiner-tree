module

public import SteinerUpperBound.Structural.TreeCuts

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

structure Cherry (S : TreeGeometry.TreeSolution I) (v : ↥S.vertices) where
  center : ↥S.vertices
  primary : ↥S.vertices
  secondary : ↥S.vertices
  attachment_nonterminal : (v : V) ∉ I.terminals
  center_nonterminal : (center : V) ∉ I.terminals
  primary_terminal : (primary : V) ∈ I.terminals
  secondary_terminal : (secondary : V) ∈ I.terminals
  ports_ne : primary ≠ secondary
  trunk : S.graph.Adj v center
  primary_arm : S.graph.Adj center primary
  secondary_arm : S.graph.Adj center secondary
  neighbors : ∀ z, S.graph.Adj center z → z = v ∨ z = primary ∨ z = secondary
  ordered : I.distance center primary ≤ I.distance center secondary

namespace Cherry

variable {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}

noncomputable abbrev promoted (C : Cherry S v) : TreeGeometry.TreeSolution I :=
  exchange S C.center C.secondary C.primary C.secondary C.secondary_arm
    (sibling_cut_reachable S C.center C.secondary C.primary C.secondary_arm C.primary_arm C.ports_ne.symm)
    (SimpleGraph.Reachable.refl C.secondary)

theorem primary_ne_attachment (C : Cherry S v) : C.primary ≠ v :=
  fun h => C.attachment_nonterminal (h ▸ C.primary_terminal)

theorem secondary_ne_attachment (C : Cherry S v) : C.secondary ≠ v :=
  fun h => C.attachment_nonterminal (h ▸ C.secondary_terminal)

theorem center_ne_primary (C : Cherry S v) : C.center ≠ C.primary :=
  fun h => C.center_nonterminal (h ▸ C.primary_terminal)

theorem center_ne_secondary (C : Cherry S v) : C.center ≠ C.secondary :=
  fun h => C.center_nonterminal (h ▸ C.secondary_terminal)

theorem primary_edge_ne_trunk (C : Cherry S v) : s(C.center, C.primary) ≠ s(v, C.center) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨_, h⟩
  · exact C.trunk.ne h.symm
  · exact C.primary_ne_attachment h

theorem secondary_edge_ne_trunk (C : Cherry S v) : s(C.center, C.secondary) ≠ s(v, C.center) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨_, h⟩
  · exact C.trunk.ne h.symm
  · exact C.secondary_ne_attachment h

theorem sibling_edge_ne_trunk (C : Cherry S v) : s(C.primary, C.secondary) ≠ s(v, C.center) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨h, _⟩
  · exact C.primary_ne_attachment h
  · exact C.center_ne_primary h.symm

theorem promoted_center_adj (C : Cherry S v) (z : ↥S.vertices) :
    C.promoted.graph.Adj C.center z ↔ z = v ∨ z = C.primary := by
  constructor
  · intro h
    rcases h with h | h
    · obtain ⟨hz, hnot⟩ := SimpleGraph.deleteEdges_adj.mp h
      rcases C.neighbors z hz with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hnot (by simp only [h, Set.mem_singleton_iff]))
    · rcases (SimpleGraph.edge_adj C.primary C.secondary C.center z).mp h with ⟨h | h, _⟩
      · exact False.elim (C.center_ne_primary h.1)
      · exact False.elim (C.center_ne_secondary h.1)
  · rintro (rfl | rfl)
    · apply Or.inl
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨C.trunk.symm, ?_⟩
      rw [Set.mem_singleton_iff]
      intro h
      rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h, _⟩
      · exact C.secondary_ne_attachment h.symm
      · exact C.center_ne_secondary h
    · apply Or.inl
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨C.primary_arm, ?_⟩
      rw [Set.mem_singleton_iff]
      intro h
      rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h, _⟩
      · exact C.ports_ne h
      · exact C.center_ne_secondary h

theorem promoted_trunk_regions (C : Cherry S v) {x y : ↥S.vertices}
    (hxy : (S.graph.deleteEdges {s(v, C.center)}).Reachable x y) :
    (C.promoted.graph.deleteEdges {s(v, C.center)}).Reachable x y := by
  let H := S.graph.deleteEdges {s(v, C.center)}
  have harm : (H.deleteEdges {s(C.center, C.secondary)}).Adj C.center C.primary := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨SimpleGraph.deleteEdges_adj.mpr
      ⟨C.primary_arm, by simpa only [Set.mem_singleton_iff] using C.primary_edge_ne_trunk⟩, ?_⟩
    rw [Set.mem_singleton_iff]
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h, _⟩
    · exact C.ports_ne h
    · exact C.center_ne_secondary h
  have hh := exchangeEdge_reachable H harm.reachable (SimpleGraph.Reachable.refl C.secondary) hxy
  change ((exchangeEdge S.graph C.center C.secondary C.primary C.secondary).deleteEdges
    {s(v, C.center)}).Reachable x y
  rw [exchange_delete_comm _ _ _ _ _ _ C.sibling_edge_ne_trunk]
  exact hh

theorem secondary_mem_region (C : Cherry S v) :
    (C.secondary : V) ∈ Tree.region S v C.center := by
  apply (Tree.mem_region S v C.center C.secondary).mpr
  exact (SimpleGraph.deleteEdges_adj.mpr
    ⟨C.secondary_arm, by simpa only [Set.mem_singleton_iff] using C.secondary_edge_ne_trunk⟩).reachable

theorem secondary_outside_primary_arm (C : Cherry S v) :
    (C.secondary : V) ∉ Tree.region S C.center C.primary :=
  not_mem_region_of_reachable S C.center C.primary C.secondary C.primary_arm
    (sibling_cut_reachable S C.center C.primary C.secondary C.primary_arm C.secondary_arm C.ports_ne)

theorem longer_arm_bound (C : Cherry S v) (hred : Reduced S) :
    I.distance C.center C.secondary < I.distance C.center C.primary / (chi - 1) := by
  have hx : (S.graph.deleteEdges {s(C.center, C.secondary)}).Reachable C.center C.primary :=
    sibling_cut_reachable S C.center C.secondary C.primary C.secondary_arm C.primary_arm C.ports_ne.symm
  have hd := reduced_cut_barrier S hred C.center C.secondary C.primary C.secondary
    C.secondary_arm hx (SimpleGraph.Reachable.refl _) C.center_nonterminal
      C.primary_terminal C.secondary_terminal
  have ht := I.distance_triangle (C.primary : V) C.center C.secondary
  rw [I.distance_comm (C.primary : V) C.center] at ht
  apply (lt_div_iff₀ (by norm_num [chi, e0] : 0 < chi - 1)).mpr
  nlinarith

end Cherry

end SteinerUpperBound.Structural.Tree
