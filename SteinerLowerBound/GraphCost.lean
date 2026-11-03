module

public import SteinerLowerBound.Metric

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace GraphCost

variable {V : Type*}

theorem edgeCount_eq_card (G : SimpleGraph V) [Fintype G.edgeSet] :
    Nat.card G.edgeSet = G.edgeFinset.card := by
  rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]

theorem degreeCount_eq (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    Nat.card (G.neighborSet v) = G.degree v := by
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card,
    Nat.card_eq_fintype_card]

noncomputable def edgeIndicator (G : SimpleGraph V) (e : Sym2 V) : ℝ :=
  if e ∈ G.edgeSet then 1 else 0

noncomputable def cost [Fintype V] (w : Sym2 V → ℝ) (G : SimpleGraph V) : ℝ :=
  ∑ e ∈ G.edgeFinset, w e

theorem forest_edges_le [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  by_cases hV : Nonempty V
  · have := hV
    have htop : (⊤ : SimpleGraph V).Connected := SimpleGraph.connected_top
    obtain ⟨T, hGT, _, hT⟩ :=
      htop.exists_isTree_le_of_le_of_isAcyclic le_top hG
    have hcard := hT.card_edgeFinset
    have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGT)
    omega
  · have : IsEmpty V := not_nonempty_iff.mp hV
    have he : G.edgeFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e _
      rcases e with ⟨x, y⟩
      exact isEmptyElim x
    simp [he]

theorem cost_extension [Fintype V] (w : Sym2 V → ℝ)
    (G H : SimpleGraph V) (hGH : G ≤ H) (B : ℝ)
    (hw : ∀ e ∈ H.edgeFinset, w e ≤ B) :
    cost w H ≤ cost w G + B * ((H.edgeFinset.card : ℝ) - G.edgeFinset.card) := by
  classical
  have hsub := SimpleGraph.edgeFinset_mono hGH
  have hcard := Finset.card_le_card hsub
  calc
    _ = cost w G + ∑ e ∈ H.edgeFinset \ G.edgeFinset, w e := by
      unfold cost
      rw [add_comm, Finset.sum_sdiff hsub]
    _ ≤ cost w G + ∑ _e ∈ H.edgeFinset \ G.edgeFinset, B := by
      exact add_le_add (le_refl _) (Finset.sum_le_sum
        fun e he => hw e (Finset.mem_sdiff.mp he).1)
    _ = _ := by
      simp [Finset.card_sdiff_of_subset hsub, Nat.cast_sub hcard, mul_comm]

noncomputable def parentGraph (f : V → V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y => f x = y)

theorem parent_adj (f : V → V) (x y : V) :
    (parentGraph f).Adj x y ↔ x ≠ y ∧ (f x = y ∨ f y = x) := by
  simp [parentGraph, SimpleGraph.fromRel]

theorem parent_neighbor_unique (f : V → V) (hf : ∀ x, f (f x) = f x)
    (x : V) (hx : f x ≠ x) (y : V) (hxy : (parentGraph f).Adj x y) :
    y = f x := by
  rcases (parent_adj f x y).mp hxy with ⟨_, h | h⟩
  · exact h.symm
  · have hfx : f x = x := by
      calc
        f x = f (f y) := by rw [h]
        _ = f y := hf y
        _ = x := h
    exact False.elim (hx hfx)

theorem parent_acyclic (f : V → V) (hf : ∀ x, f (f x) = f x) :
    (parentGraph f).IsAcyclic := by
  classical
  have hb (x y : V) (hxy : (parentGraph f).Adj x y) (hp : f x = y) :
      (parentGraph f).IsBridge s(x, y) := by
    have hx : f x ≠ x := by rw [hp]; exact hxy.ne.symm
    apply SimpleGraph.not_reachable_of_neighborSet_left_eq_empty hxy.ne
    ext z
    simp only [SimpleGraph.mem_neighborSet, SimpleGraph.deleteEdges_adj,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨hxz, hnot⟩
    have hz : z = y := (parent_neighbor_unique f hf x hx z hxz).trans hp
    subst z
    exact hnot (Set.mem_singleton _)
  apply SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr
  intro x y hxy
  rcases (parent_adj f x y).mp hxy with ⟨_, h | h⟩
  · exact hb x y hxy h
  · rw [Sym2.eq_swap]
    exact hb y x hxy.symm h

theorem parent_edges [Fintype V] (f : V → V) :
    (parentGraph f).edgeFinset =
      (Finset.univ.filter fun x => f x ≠ x).image (fun x => s(x, f x)) := by
  classical
  ext e
  rcases e with ⟨x, y⟩
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, parent_adj,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, h | h⟩
    · refine ⟨x, ?_, ?_⟩
      · rw [h]; exact hne.symm
      · rw [h]
    · refine ⟨y, ?_, ?_⟩
      · rw [h]; exact hne
      · rw [h, Sym2.eq_swap]
  · rintro ⟨z, hz, he⟩
    rcases Sym2.eq_iff.mp he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · subst x
      subst y
      exact ⟨hz.symm, Or.inl rfl⟩
    · subst x
      subst y
      exact ⟨hz, Or.inr rfl⟩

theorem parent_edge_injective (f : V → V) (hf : ∀ x, f (f x) = f x) :
    Set.InjOn (fun x => s(x, f x)) {x | f x ≠ x} := by
  intro x hx y hy h
  rcases Sym2.eq_iff.mp h with ⟨h₁, _⟩ | ⟨h₁, h₂⟩
  · exact h₁
  · have : f y = y := by
      calc
        f y = f (f x) := by rw [h₂]
        _ = f x := hf x
        _ = y := h₂
    exact False.elim (hy this)

theorem parent_card [Fintype V] (f : V → V) (hf : ∀ x, f (f x) = f x) :
    (parentGraph f).edgeFinset.card = (Finset.univ.filter fun x => f x ≠ x).card := by
  rw [parent_edges f, Finset.card_image_of_injOn]
  intro x hx y hy
  exact parent_edge_injective f hf (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2

theorem parent_cost [Fintype V] (w : Sym2 V → ℝ) (f : V → V)
    (hf : ∀ x, f (f x) = f x) :
    cost w (parentGraph f) = ∑ x ∈ Finset.univ.filter (fun x => f x ≠ x), w s(x, f x) := by
  unfold cost
  rw [parent_edges f, Finset.sum_image]
  intro x hx y hy
  exact parent_edge_injective f hf (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2

noncomputable def parentContribution (w : Sym2 V → ℝ) (f : V → V) (x : V) : ℝ :=
  if f x ≠ x then w s(x, f x) else 0

theorem parent_cost_sum [Fintype V] (w : Sym2 V → ℝ) (f : V → V)
    (hf : ∀ x, f (f x) = f x) :
    cost w (parentGraph f) = ∑ x, parentContribution w f x := by
  rw [parent_cost w f hf, Finset.sum_filter]
  rfl

theorem parent_card_sum [Fintype V] (f : V → V) (hf : ∀ x, f (f x) = f x) :
    ((parentGraph f).edgeFinset.card : ℝ) =
      ∑ x, parentContribution (fun _ => 1) f x := by
  rw [parent_card f hf, ← Finset.sum_boole]
  rfl

theorem forest_edges_support_le [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (s : Finset V) (hs : G.support ⊆ (s : Set V)) : G.edgeFinset.card ≤ s.card := by
  classical
  let _ : Fintype (s : Set V) := Subtype.fintype (fun x => x ∈ (s : Set V))
  calc
    _ = (G.induce (s : Set V)).edgeFinset.card :=
      (G.card_edgeFinset_induce_of_support_subset hs).symm
    _ ≤ Fintype.card (s : Set V) := forest_edges_le _ (hG.induce _)
    _ = _ := Fintype.card_of_subtype s (fun _ => Iff.rfl)

end GraphCost

end SteinerLowerBound
