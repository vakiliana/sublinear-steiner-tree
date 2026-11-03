module

public import SteinerUpperBound.Structural.Potential

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V]

noncomputable def exchangeEdge (G : SimpleGraph V) (u v a b : V) : SimpleGraph V :=
  G.deleteEdges {s(u, v)} ⊔ SimpleGraph.edge a b

theorem reachable_of_adj_reachable {G H : SimpleGraph V}
    (h : ∀ x y, G.Adj x y → H.Reachable x y) {x y : V}
    (hxy : G.Reachable x y) : H.Reachable x y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih => exact (h a b hab).trans ih

theorem exchangeEdge_connected (G : SimpleGraph V) (ht : G.Connected)
    {u v a b : V} (ha : (G.deleteEdges {s(u, v)}).Reachable u a)
    (hb : (G.deleteEdges {s(u, v)}).Reachable v b) :
    (exchangeEdge G u v a b).Connected := by
  have hab : (exchangeEdge G u v a b).Reachable a b := by
    by_cases h : a = b
    · subst b
      exact SimpleGraph.Reachable.refl _
    · exact (show (exchangeEdge G u v a b).Adj a b from
        Or.inr ((SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, h⟩)).reachable
  have huv : (exchangeEdge G u v a b).Reachable u v :=
    (ha.mono le_sup_left).trans (hab.trans (hb.mono le_sup_left).symm)
  have hsim : ∀ x y, G.Adj x y → (exchangeEdge G u v a b).Reachable x y := by
    intro x y hxy
    by_cases he : s(x, y) = s(u, v)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv
      · exact huv.symm
    · exact (show (exchangeEdge G u v a b).Adj x y from
        Or.inl (SimpleGraph.deleteEdges_adj.mpr ⟨hxy, by simpa only [Set.mem_singleton_iff]⟩)).reachable
  have : Nonempty V := ht.nonempty
  exact ⟨fun x y => reachable_of_adj_reachable hsim (ht x y)⟩

theorem exchangeEdge_tree (G : SimpleGraph V) (ht : G.IsTree)
    {u v a b : V} (huv : G.Adj u v)
    (ha : (G.deleteEdges {s(u, v)}).Reachable u a)
    (hb : (G.deleteEdges {s(u, v)}).Reachable v b) :
    (exchangeEdge G u v a b).IsTree := by
  classical
  have hc := exchangeEdge_connected G ht.connected ha hb
  have hs : (exchangeEdge G u v a b).edgeFinset ⊆
      G.edgeFinset.erase s(u, v) ∪ {s(a, b)} := by
    intro e he
    rcases e with ⟨x, y⟩
    have hadj : (exchangeEdge G u v a b).Adj x y := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    rcases hadj with h | h
    · obtain ⟨hxy, hne⟩ := SimpleGraph.deleteEdges_adj.mp h
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr
        ⟨by simpa only [Set.mem_singleton_iff] using hne,
          by simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hxy⟩))
    · rcases (SimpleGraph.edge_adj a b x y).mp h with ⟨h | h, _⟩
      · rcases h with ⟨rfl, rfl⟩
        simp
      · rcases h with ⟨rfl, rfl⟩
        simp [Sym2.eq_swap]
  have hcard := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hmem : s(u, v) ∈ G.edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using huv
  have hpos : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨s(u, v), hmem⟩
  rw [Finset.card_erase_of_mem hmem, Finset.card_singleton] at hcard
  have hold := ht.card_edgeFinset
  have hlow : Nat.card V ≤ Nat.card (exchangeEdge G u v a b).edgeSet + 1 := by
    simpa only [← Nat.card_eq_fintype_card] using hc.card_vert_le_card_edgeSet_add_one
  rw [GraphCost.edgeCount_eq_card, Nat.card_eq_fintype_card] at hlow
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hc, ?_⟩
  rw [GraphCost.edgeCount_eq_card, Nat.card_eq_fintype_card]
  omega

theorem cost_edge_le (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) (a b : V) :
    GraphCost.cost w (SimpleGraph.edge a b) ≤ w s(a, b) := by
  classical
  unfold GraphCost.cost
  calc
    _ ≤ ∑ e ∈ ({s(a, b)} : Finset (Sym2 V)), w e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        rcases e with ⟨x, y⟩
        have hxy : (SimpleGraph.edge a b).Adj x y := by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
        rcases (SimpleGraph.edge_adj a b x y).mp hxy with ⟨h | h, _⟩
        · rcases h with ⟨rfl, rfl⟩
          simp
        · rcases h with ⟨rfl, rfl⟩
          simp [Sym2.eq_swap]
      · intro e _ _
        exact hw e
    _ = _ := by simp

theorem exchangeEdge_cost_le (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) {u v a b : V} (huv : G.Adj u v) :
    GraphCost.cost w (exchangeEdge G u v a b) ≤
      GraphCost.cost w G - w s(u, v) + w s(a, b) := by
  have hsup := TreeGeometry.cost_sup_le w (G.deleteEdges {s(u, v)}) (SimpleGraph.edge a b) hw
  have hdel := TreeGeometry.cost_delete_edge_add G w s(u, v) huv
  have hadd := cost_edge_le w hw a b
  change GraphCost.cost w (G.deleteEdges {s(u, v)} ⊔ SimpleGraph.edge a b) ≤ _
  linarith

end SteinerUpperBound.Structural
