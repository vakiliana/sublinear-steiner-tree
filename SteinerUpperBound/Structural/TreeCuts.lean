module

public import SteinerUpperBound.Structural.Reduction
public import SteinerUpperBound.Structural.Cuts

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V]

theorem exchangeEdge_reachable (G : SimpleGraph V) {u v a b : V}
    (ha : (G.deleteEdges {s(u, v)}).Reachable u a)
    (hb : (G.deleteEdges {s(u, v)}).Reachable v b)
    {x y : V} (hxy : G.Reachable x y) :
    (exchangeEdge G u v a b).Reachable x y := by
  have hab : (exchangeEdge G u v a b).Reachable a b := by
    by_cases h : a = b
    · subst b
      exact SimpleGraph.Reachable.refl _
    · exact (show (exchangeEdge G u v a b).Adj a b from
        Or.inr ((SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, h⟩)).reachable
  have huv : (exchangeEdge G u v a b).Reachable u v :=
    (ha.mono le_sup_left).trans (hab.trans (hb.mono le_sup_left).symm)
  apply reachable_of_adj_reachable (G := G) (H := exchangeEdge G u v a b) _ hxy
  intro z w hzw
  by_cases he : s(z, w) = s(u, v)
  · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huv
    · exact huv.symm
  · exact (show (exchangeEdge G u v a b).Adj z w from
      Or.inl (SimpleGraph.deleteEdges_adj.mpr
        ⟨hzw, by simpa only [Set.mem_singleton_iff] using he⟩)).reachable

theorem edge_delete_other (a b : V) (e : Sym2 V) (he : s(a, b) ≠ e) :
    (SimpleGraph.edge a b).deleteEdges {e} = SimpleGraph.edge a b := by
  ext x y
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    rw [Set.mem_singleton_iff]
    rcases (SimpleGraph.edge_adj a b x y).mp h with ⟨h | h, _⟩
    · rcases h with ⟨rfl, rfl⟩
      exact he
    · rcases h with ⟨rfl, rfl⟩
      simpa only [Sym2.eq_swap] using he

theorem exchange_delete_comm (G : SimpleGraph V) (u v a b : V)
    (e : Sym2 V) (he : s(a, b) ≠ e) :
    (exchangeEdge G u v a b).deleteEdges {e} =
      exchangeEdge (G.deleteEdges {e}) u v a b := by
  unfold exchangeEdge
  rw [SimpleGraph.deleteEdges_sup, edge_delete_other a b e he]
  simp only [SimpleGraph.deleteEdges_deleteEdges, Set.union_comm]

theorem delete_edge_two_sides (G : SimpleGraph V) (hc : G.Connected) (u v x : V) :
    (G.deleteEdges {s(u, v)}).Reachable u x ∨
      (G.deleteEdges {s(u, v)}).Reachable v x := by
  let H := G.deleteEdges {s(u, v)}
  let A : Set V := {z | H.Reachable u z ∨ H.Reachable v z}
  have hclosed : ClosedCut G A := by
    intro a b hab
    by_cases he : s(a, b) = s(u, v)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [A]
      · simp [A]
    · have hH : H.Adj a b :=
        SimpleGraph.deleteEdges_adj.mpr ⟨hab, by simpa only [Set.mem_singleton_iff] using he⟩
      exact or_congr ((reachable_cut_closed H u).reachable hH.reachable)
        ((reachable_cut_closed H v).reachable hH.reachable)
  exact (hclosed.reachable (hc u x)).mp (Or.inl (SimpleGraph.Reachable.refl u))

namespace Tree

variable {I : Instance V}

noncomputable def region (S : TreeGeometry.TreeSolution I) (u v : ↥S.vertices) : Finset V :=
  (Finset.univ.filter (fun x => (S.graph.deleteEdges {s(u, v)}).Reachable v x)).image Subtype.val

theorem mem_region (S : TreeGeometry.TreeSolution I) (u v x : ↥S.vertices) :
    (x : V) ∈ region S u v ↔ (S.graph.deleteEdges {s(u, v)}).Reachable v x := by
  classical
  simp only [region, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, he⟩
    have h : y = x := Subtype.ext he
    simpa only [h] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem not_mem_region_of_reachable (S : TreeGeometry.TreeSolution I)
    (u v x : ↥S.vertices) (huv : S.graph.Adj u v)
    (hx : (S.graph.deleteEdges {s(u, v)}).Reachable u x) :
    (x : V) ∉ region S u v := by
  intro h
  have hvx := (mem_region S u v x).mp h
  have hreach := hx.trans hvx.symm
  have hb := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp S.isTree.isAcyclic huv
  exact SimpleGraph.isBridge_iff.mp hb hreach

theorem reduced_region_barrier (S : TreeGeometry.TreeSolution I) (hred : Reduced S)
    (u v : ↥S.vertices) (huv : S.graph.Adj u v) (hu : (u : V) ∉ I.terminals)
    {a b : V} (ha : a ∈ I.terminals) (hb : b ∈ I.terminals)
    (haR : a ∈ region S u v) (hbR : b ∉ region S u v) :
    chi * I.distance u v < I.distance a b := by
  let a' : ↥S.vertices := ⟨a, S.contains ha⟩
  let b' : ↥S.vertices := ⟨b, S.contains hb⟩
  have hva : (S.graph.deleteEdges {s(u, v)}).Reachable v a' :=
    (mem_region S u v a').mp haR
  have hvb : ¬ (S.graph.deleteEdges {s(u, v)}).Reachable v b' :=
    fun h => hbR ((mem_region S u v b').mpr h)
  have hub := (delete_edge_two_sides S.graph S.isTree.connected u v b').resolve_right hvb
  simpa only [a', b', I.distance_comm b a] using
    reduced_cut_barrier S hred u v b' a' huv hub hva hu hb ha

theorem terminalGraph_region_closed (S : TreeGeometry.TreeSolution I)
    (u v : ↥S.vertices) (hu : (u : V) ∉ I.terminals) :
    ClosedCut (terminalGraph S) (region S u v : Set V) := by
  intro a b hab
  obtain ⟨hab, hT⟩ := hab
  obtain ⟨_, haT, hbT⟩ := (Network.completeOn_adj _ _ _).mp hT
  change (S.graph.map Subtype.val).Adj a b at hab
  obtain ⟨_, a', b', hab', rfl, rfl⟩ := (SimpleGraph.map_adj' Subtype.val S.graph a b).mp hab
  change (a' : V) ∈ region S u v ↔ (b' : V) ∈ region S u v
  rw [mem_region, mem_region]
  have he : s(a', b') ≠ s(u, v) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨_, h⟩
    · exact hu (h ▸ haT)
    · exact hu (h ▸ hbT)
  have hadj : (S.graph.deleteEdges {s(u, v)}).Adj a' b' :=
    SimpleGraph.deleteEdges_adj.mpr ⟨hab', by simpa only [Set.mem_singleton_iff] using he⟩
  exact (reachable_cut_closed _ v).reachable hadj.reachable

theorem reduced_threshold_region_closed (S : TreeGeometry.TreeSolution I) (hred : Reduced S)
    (u v : ↥S.vertices) (huv : S.graph.Adj u v) (hu : (u : V) ∉ I.terminals)
    (a : ℝ) (ha : a ≤ chi * I.distance u v) :
    ClosedCut (threshold I a ⊔ terminalGraph S) (region S u v : Set V) := by
  apply threshold_sup_closedCut I (terminalGraph S) _ _ a ha
  · intro x hx y hy hxR hyR
    exact (reduced_region_barrier S hred u v huv hu hx hy hxR hyR).le
  · exact terminalGraph_region_closed S u v hu

end Tree

end SteinerUpperBound.Structural
