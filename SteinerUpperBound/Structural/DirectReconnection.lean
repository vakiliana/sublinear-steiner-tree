module

public import SteinerUpperBound.Structural.StarBatchCuts

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators

variable {W J : Type*} [Fintype W]

theorem exchange_delete_le (G : SimpleGraph W) (u v a b : W) (e : Sym2 W) :
    (exchangeEdge G u v a b).deleteEdges {e} ≤
      G.deleteEdges {e} ⊔ SimpleGraph.edge a b := by
  unfold exchangeEdge
  rw [SimpleGraph.deleteEdges_sup]
  exact sup_le_sup (SimpleGraph.deleteEdges_mono (SimpleGraph.deleteEdges_le _))
    (SimpleGraph.deleteEdges_le _)

theorem reconnect_direct_edges (G : SimpleGraph W) (hG : G.IsTree)
    (D : Finset J) (u p : J → W) (target : W) (A : J → Set W)
    (hadj : ∀ i ∈ D, G.Adj (u i) (p i))
    (hu : ∀ i ∈ D, u i ∉ A i) (hp : ∀ i ∈ D, p i ∈ A i)
    (htarget : ∀ i ∈ D, target ∉ A i)
    (hclosed : ∀ i ∈ D, ClosedCut (G.deleteEdges {s(u i, p i)}) (A i))
    (hother : ∀ i ∈ D, ∀ j ∈ D, i ≠ j → p i ∉ A j)
    (hedges : ∀ i ∈ D, ∀ j ∈ D, i ≠ j → s(u i, p i) ≠ s(u j, p j))
    (hnew : ∀ i ∈ D, ∀ j ∈ D, s(target, p i) ≠ s(u j, p j)) :
    ∃ H : SimpleGraph W, H.IsTree ∧
      G.deleteEdges (D.image (fun i => s(u i, p i)) : Set (Sym2 W)) ≤ H ∧
      (∀ i ∈ D, H.Adj target (p i)) ∧
      ∀ (w : Sym2 W → ℝ), (∀ e, 0 ≤ w e) →
        GraphCost.cost w H ≤ GraphCost.cost w G +
          ∑ i ∈ D, (w s(target, p i) - w s(u i, p i)) := by
  classical
  induction D using Finset.induction_on generalizing G with
  | empty =>
    refine ⟨G, hG, ?_, by simp, ?_⟩
    · simp
    · intro w hw
      simp
  | @insert i D hi ih =>
    have hiI : i ∈ insert i D := Finset.mem_insert_self _ _
    have hcut := hclosed i hiI
    have hpt : ¬ (G.deleteEdges {s(u i, p i)}).Reachable (p i) target :=
      hcut.not_reachable (hp i hiI) (htarget i hiI)
    have hut := (delete_edge_two_sides G hG.connected (u i) (p i) target).resolve_right hpt
    let G₁ := exchangeEdge G (u i) (p i) target (p i)
    have hG₁ : G₁.IsTree := exchangeEdge_tree G hG (hadj i hiI) hut (SimpleGraph.Reachable.refl _)
    have hta : target ≠ p i := by
      intro he
      exact htarget i hiI (he ▸ hp i hiI)
    have hadj₁ : ∀ j ∈ D, G₁.Adj (u j) (p j) := by
      intro j hj
      have hjI : j ∈ insert i D := Finset.mem_insert_of_mem hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      exact Or.inl (SimpleGraph.deleteEdges_adj.mpr
        ⟨hadj j hjI, by simpa only [Set.mem_singleton_iff] using hedges j hjI i hiI hji⟩)
    have hclosed₁ : ∀ j ∈ D, ClosedCut (G₁.deleteEdges {s(u j, p j)}) (A j) := by
      intro j hj
      have hjI : j ∈ insert i D := Finset.mem_insert_of_mem hj
      have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
      apply Tree.closedCut_mono (exchange_delete_le G _ _ _ _ _)
      exact (hclosed j hjI).sup
        (Tree.closedCut_edge (A j) target (p i) (iff_of_false (htarget j hjI) (hother i hiI j hjI hij)))
    obtain ⟨H, hH, hkeep, hlinks, hcost⟩ := ih G₁ hG₁ hadj₁
      (fun j hj => hu j (Finset.mem_insert_of_mem hj))
      (fun j hj => hp j (Finset.mem_insert_of_mem hj))
      (fun j hj => htarget j (Finset.mem_insert_of_mem hj)) hclosed₁
      (fun j hj k hk => hother j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      (fun j hj k hk => hedges j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      (fun j hj k hk => hnew j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
    refine ⟨H, hH, ?_, ?_, ?_⟩
    · intro x y hxy
      obtain ⟨hxy, hnot⟩ := SimpleGraph.deleteEdges_adj.mp hxy
      apply hkeep
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨Or.inl (SimpleGraph.deleteEdges_adj.mpr ⟨hxy, ?_⟩), ?_⟩
      · intro he
        apply hnot
        rw [Set.mem_singleton_iff] at he
        exact Finset.mem_image.mpr ⟨i, hiI, he.symm⟩
      · intro he
        have he' : s(x, y) ∈ (D.image (fun j => s(u j, p j)) : Finset (Sym2 W)) := he
        obtain ⟨j, hj, hjxy⟩ := Finset.mem_image.mp he'
        exact hnot (Finset.mem_image.mpr ⟨j, Finset.mem_insert_of_mem hj, hjxy⟩)
    · intro j hj
      rcases Finset.mem_insert.mp hj with he | hj
      · subst j
        apply hkeep
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨Or.inr ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hta⟩), ?_⟩
        intro he
        obtain ⟨j, hj, he⟩ := Finset.mem_image.mp he
        exact hnew i hiI j (Finset.mem_insert_of_mem hj) he.symm
      · exact hlinks j hj
    · intro w hw
      have hfirst := exchangeEdge_cost_le G w hw (a := target) (b := p i) (hadj i hiI)
      change GraphCost.cost w G₁ ≤ _ at hfirst
      have htail := hcost w hw
      rw [Finset.sum_insert hi]
      linarith

end SteinerUpperBound.Structural
