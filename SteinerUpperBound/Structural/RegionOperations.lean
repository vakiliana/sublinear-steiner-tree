module

public import SteinerUpperBound.Structural.Promotion

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

theorem region_attachment_outside (S : TreeGeometry.TreeSolution I)
    (u v : ↥S.vertices) (huv : S.graph.Adj u v) : (u : V) ∉ region S u v :=
  not_mem_region_of_reachable S u v u huv (SimpleGraph.Reachable.refl u)

theorem ambient_region_closed (S : TreeGeometry.TreeSolution I) (u v : ↥S.vertices) :
    ClosedCut (S.ambient.deleteEdges {s((u : V), (v : V))}) (region S u v : Set V) := by
  intro a b hab
  obtain ⟨hab, hnot⟩ := SimpleGraph.deleteEdges_adj.mp hab
  change (S.graph.map Subtype.val).Adj a b at hab
  obtain ⟨_, a', b', hab', rfl, rfl⟩ :=
    (SimpleGraph.map_adj' Subtype.val S.graph a b).mp hab
  change (a' : V) ∈ region S u v ↔ (b' : V) ∈ region S u v
  rw [mem_region, mem_region]
  have hnot' : s(a', b') ≠ s(u, v) := by
    intro h
    exact hnot (Set.mem_singleton_iff.mpr (congrArg (Sym2.map Subtype.val) h))
  have hAdj : (S.graph.deleteEdges {s(u, v)}).Adj a' b' :=
    SimpleGraph.deleteEdges_adj.mpr ⟨hab', by simpa only [Set.mem_singleton_iff] using hnot'⟩
  exact (reachable_cut_closed _ v).reachable hAdj.reachable

theorem disjoint_regions_of_outside (S : TreeGeometry.TreeSolution I)
    (u v a b : ↥S.vertices) (huv : S.graph.Adj u v) (hab : S.graph.Adj a b)
    (hne : s(u, v) ≠ s(a, b))
    (huOut : (u : V) ∉ region S a b) (haOut : (a : V) ∉ region S u v) :
    Disjoint (region S u v) (region S a b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx1 hx2
  obtain ⟨x', _, hx'⟩ := Finset.mem_image.mp hx1
  have hxval : (x' : V) = x := hx'
  subst x
  have hx1' := (mem_region S u v x').mp hx1
  have hx2' := (mem_region S a b x').mp hx2
  have hau : (S.graph.deleteEdges {s(a, b)}).Reachable a u := by
    have hbu : ¬ (S.graph.deleteEdges {s(a, b)}).Reachable b u :=
      fun h => huOut ((mem_region S a b u).mpr h)
    exact (delete_edge_two_sides S.graph S.isTree.connected a b u).resolve_right hbu
  have huv' : (S.graph.deleteEdges {s(a, b)}).Adj u v :=
    SimpleGraph.deleteEdges_adj.mpr ⟨huv, by simpa only [Set.mem_singleton_iff] using hne⟩
  obtain ⟨p⟩ := hx1'
  have haNot : a ∉ p.support := by
    intro ha
    exact haOut ((mem_region S u v a).mpr (p.takeUntil a ha).reachable)
  have heNot : s(a, b) ∉ p.edges := by
    intro he
    exact haNot (p.fst_mem_support_of_mem_edges he)
  have hvx : (S.graph.deleteEdges {s(a, b)}).Reachable v x' :=
    SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
      ⟨p.mapLe (S.graph.deleteEdges_le _), by
        simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using heNot⟩
  have hax := hau.trans (huv'.reachable.trans hvx)
  have hbridge := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp S.isTree.isAcyclic hab
  exact SimpleGraph.isBridge_iff.mp hbridge (hax.trans hx2'.symm)

theorem region_eq_of_closed (Q : TreeGeometry.TreeSolution I)
    (u v : ↥Q.vertices) (A : Finset V)
    (hu : (u : V) ∉ A) (hv : (v : V) ∈ A)
    (hclosed : ClosedCut (Q.graph.deleteEdges {s(u, v)}) {x | (x : V) ∈ A}) :
    ∀ x : ↥Q.vertices, (x : V) ∈ region Q u v ↔ (x : V) ∈ A := by
  intro x
  rw [mem_region]
  constructor
  · intro hx
    exact (hclosed.reachable hx).mp hv
  · intro hx
    rcases delete_edge_two_sides Q.graph Q.isTree.connected u v x with h | h
    · exact False.elim (hu ((hclosed.reachable h).mpr hx))
    · exact h

theorem closedCut_mono {G H : SimpleGraph V} {A : Set V} (h : G ≤ H)
    (hc : ClosedCut H A) : ClosedCut G A :=
  fun x y hxy => hc x y (h hxy)

theorem closedCut_edge (A : Set V) (x y : V) (hxy : x ∈ A ↔ y ∈ A) :
    ClosedCut (SimpleGraph.edge x y) A := by
  intro a b hab
  rcases (SimpleGraph.edge_adj x y a b).mp hab with ⟨h | h, _⟩
  · rcases h with ⟨rfl, rfl⟩
    exact hxy
  · rcases h with ⟨rfl, rfl⟩
    exact hxy.symm

theorem pull_closed_cut (Q : TreeGeometry.TreeSolution I) (u v : ↥Q.vertices)
    (A : Finset V)
    (hclosed : ClosedCut (Q.ambient.deleteEdges {s((u : V), (v : V))}) (A : Set V)) :
    ClosedCut (Q.graph.deleteEdges {s(u, v)}) {x | (x : V) ∈ A} := by
  intro x y hxy
  obtain ⟨hxy, hnot⟩ := SimpleGraph.deleteEdges_adj.mp hxy
  apply hclosed x y
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨SimpleGraph.map_adj_apply' hxy (Subtype.val_injective.ne hxy.ne), ?_⟩
  rw [Set.mem_singleton_iff]
  intro he
  apply hnot
  apply Set.mem_singleton_iff.mpr
  rcases Sym2.eq_iff.mp he with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext hx, Subtype.ext hy⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext hx, Subtype.ext hy⟩)

theorem region_eq_under_additions (S Q : TreeGeometry.TreeSolution I)
    (u v : ↥S.vertices) (huv : S.graph.Adj u v)
    (u' v' : ↥Q.vertices) (hu' : (u' : V) = (u : V)) (hv' : (v' : V) = (v : V))
    (F : SimpleGraph V) (hle : Q.ambient ≤ S.ambient ⊔ F)
    (hF : ClosedCut F (region S u v : Set V)) :
    ∀ x : ↥Q.vertices, (x : V) ∈ region Q u' v' ↔ (x : V) ∈ region S u v := by
  have hDle : Q.ambient.deleteEdges {s((u' : V), (v' : V))} ≤
      S.ambient.deleteEdges {s((u : V), (v : V))} ⊔ F := by
    rw [hu', hv']
    apply (SimpleGraph.deleteEdges_mono hle).trans
    rw [SimpleGraph.deleteEdges_sup]
    exact sup_le_sup_left (SimpleGraph.deleteEdges_le _) _
  have hc : ClosedCut (Q.ambient.deleteEdges {s((u' : V), (v' : V))})
      (region S u v : Set V) :=
    closedCut_mono hDle ((ambient_region_closed S u v).sup hF)
  apply region_eq_of_closed Q u' v' (region S u v)
  · simpa only [hu'] using region_attachment_outside S u v huv
  · rw [hv']
    exact (mem_region S u v v).mpr (SimpleGraph.Reachable.refl v)
  · exact pull_closed_cut Q u' v' _ hc

namespace Cherry

variable {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}

theorem promote_ambient_le (C : Cherry S v) :
    C.promote.ambient ≤ S.ambient ⊔ SimpleGraph.edge C.primary C.secondary ⊔
      SimpleGraph.edge C.primary v := by
  intro a b hab
  change (C.promote.graph.map Subtype.val).Adj a b at hab
  obtain ⟨hne, x, y, hxy, rfl, rfl⟩ :=
    (SimpleGraph.map_adj' Subtype.val C.promote.graph a b).mp hab
  change ((S.graph.deleteEdges {s(C.center, C.secondary)} ⊔ SimpleGraph.edge C.primary C.secondary).deleteEdges
    {s(C.center, v)} ⊔ SimpleGraph.edge C.primary v).Adj
      (eraseEmbedding S C.center x) (eraseEmbedding S C.center y) at hxy
  rcases hxy with hxy | hxy
  · rcases (SimpleGraph.deleteEdges_adj.mp hxy).1 with hxy | hxy
    · apply Or.inl
      apply Or.inl
      exact (SimpleGraph.map_adj' Subtype.val S.graph _ _).mpr
        ⟨hne, eraseEmbedding S C.center x, eraseEmbedding S C.center y,
          (SimpleGraph.deleteEdges_adj.mp hxy).1, rfl, rfl⟩
    · apply Or.inl
      apply Or.inr
      rcases (SimpleGraph.edge_adj C.primary C.secondary _ _).mp hxy with ⟨h | h, _⟩
      · exact (SimpleGraph.edge_adj (C.primary : V) (C.secondary : V) _ _).mpr
          ⟨Or.inl ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩, hne⟩
      · exact (SimpleGraph.edge_adj (C.primary : V) (C.secondary : V) _ _).mpr
          ⟨Or.inr ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩, hne⟩
  · apply Or.inr
    rcases (SimpleGraph.edge_adj C.primary v _ _).mp hxy with ⟨h | h, _⟩
    · exact (SimpleGraph.edge_adj (C.primary : V) (v : V) _ _).mpr
        ⟨Or.inl ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩, hne⟩
    · exact (SimpleGraph.edge_adj (C.primary : V) (v : V) _ _).mpr
        ⟨Or.inr ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩, hne⟩

end Cherry

end SteinerUpperBound.Structural.Tree
