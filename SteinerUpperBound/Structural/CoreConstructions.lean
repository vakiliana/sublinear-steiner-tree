module

public import SteinerUpperBound.Structural.CoreFrames
public import SteinerUpperBound.Structural.CherryData

@[expose] public section

namespace SteinerUpperBound.Structural.Tree.CoreFrame

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}
variable {S : TreeGeometry.TreeSolution I}

noncomputable abbrev three (v₀ v₁ v₂ : ↥S.vertices)
    (L₀ : Limb S v₀) (L₁ : Limb S v₁) (L₂ : Limb S v₂)
    (G : SimpleGraph V) (hle : G ≤ S.ambient)
    (hNN : Network.TerminalOnly (Finset.univ \ I.terminals) G)
    (pivot : V) (h₀ : G.Reachable pivot v₀) (h₁ : G.Reachable pivot v₁)
    (h₂ : G.Reachable pivot v₂)
    (ha₀ : G ≤ S.ambient.deleteEdges {s((v₀ : V), (L₀.stem : V))})
    (ha₁ : G ≤ S.ambient.deleteEdges {s((v₁ : V), (L₁.stem : V))})
    (ha₂ : G ≤ S.ambient.deleteEdges {s((v₂ : V), (L₂.stem : V))})
    (he₀₁ : s(v₀, L₀.stem) ≠ s(v₁, L₁.stem))
    (he₀₂ : s(v₀, L₀.stem) ≠ s(v₂, L₂.stem))
    (he₁₂ : s(v₁, L₁.stem) ≠ s(v₂, L₂.stem)) : CoreFrame S := by
  let L : Fin 3 → Σ v : ↥S.vertices, Limb S v := ![⟨v₀, L₀⟩, ⟨v₁, L₁⟩, ⟨v₂, L₂⟩]
  have hr : ∀ i, G.Reachable pivot (L i).1 := by
    intro i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
  refine
    { limbs := L
      core := G
      core_le := hle
      core_nonterminal := hNN
      core_connects := fun i j => (hr i).symm.trans (hr j)
      core_avoids := ?_
      edges_ne := ?_ }
  · intro j
    fin_cases j
    · exact ha₀
    · exact ha₁
    · exact ha₂
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact False.elim (hij rfl)
      | simpa [L] using he₀₁
      | simpa [L] using he₀₂
      | simpa [L] using he₁₂
      | simpa [L] using (Ne.symm he₀₁)
      | simpa [L] using (Ne.symm he₀₂)
      | simpa [L] using (Ne.symm he₁₂)

theorem parent_ne_child_edge {parent v : ↥S.vertices} (F : Fan S parent v)
    (L : Limb S v) (hp : parent ≠ L.stem) :
    s(parent, v) ≠ s(v, L.stem) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
  · exact F.parent_edge.ne h
  · exact hp h

noncomputable abbrev oneFan {parent v : ↥S.vertices} (F : Fan S parent v)
    (L : Limb S parent) (hst : L.stem ≠ v) : CoreFrame S := by
  let G : SimpleGraph V := SimpleGraph.edge (parent : V) (v : V)
  have hadj : S.ambient.Adj parent v := (ambient_adj_iff S _ _).mpr F.parent_edge
  have hGadj : G.Adj parent v :=
    (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, Subtype.val_injective.ne F.parent_edge.ne⟩
  have hN : Network.TerminalOnly (Finset.univ \ I.terminals) G :=
    edge_terminalOnly _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, F.parent_nonterminal⟩)
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, F.center_nonterminal⟩)
  have hleft := parent_ne_child_edge F F.left F.parent_ne_left
  have hright := parent_ne_child_edge F F.right F.parent_ne_right
  have hthird : s(parent, v) ≠ s(parent, L.stem) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨_, h⟩ | ⟨h, _⟩
    · exact hst h.symm
    · exact L.stem_adj.ne h
  have heLR : s(v, F.left.stem) ≠ s(v, F.right.stem) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨_, h⟩ | ⟨h, h'⟩
    · exact F.stems_ne h
    · exact F.stems_ne (h'.trans h)
  have heLT (B : Limb S v) : s(v, B.stem) ≠ s(parent, L.stem) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
    · exact F.parent_edge.ne h.symm
    · exact hst h.symm
  exact three v v parent F.left F.right L G (edge_le_of_adj hadj) hN parent
    hGadj.reachable hGadj.reachable (SimpleGraph.Reachable.refl _)
    (edge_delete_le_of_adj_ne hadj _ (pair_val_ne S _ _ _ _ hleft))
    (edge_delete_le_of_adj_ne hadj _ (pair_val_ne S _ _ _ _ hright))
    (edge_delete_le_of_adj_ne hadj _ (pair_val_ne S _ _ _ _ hthird))
    heLR (heLT F.left) (heLT F.right)

theorem distinct_neighbors_not_adj (v x y : ↥S.vertices)
    (hx : S.graph.Adj v x) (hy : S.graph.Adj v y) : ¬ S.graph.Adj x y := by
  intro hxy
  have hdx : S.graph.dist v x = 1 := (SimpleGraph.dist_eq_one_iff_adj).mpr hx
  have hdy : S.graph.dist v y = 1 := (SimpleGraph.dist_eq_one_iff_adj).mpr hy
  have hd := S.isTree.dist_eq_dist_add_one_of_adj v hxy
  omega

noncomputable abbrev twoFans {parent v w : ↥S.vertices} (F : Fan S parent v)
    (H : Fan S parent w) (hvw : v ≠ w) : CoreFrame S := by
  let E₁ : SimpleGraph V := SimpleGraph.edge (parent : V) (v : V)
  let E₂ : SimpleGraph V := SimpleGraph.edge (parent : V) (w : V)
  let G := E₁ ⊔ E₂
  have ha₁ : S.ambient.Adj parent v := (ambient_adj_iff S _ _).mpr F.parent_edge
  have ha₂ : S.ambient.Adj parent w := (ambient_adj_iff S _ _).mpr H.parent_edge
  have hG₁ : G.Adj parent v := Or.inl ((SimpleGraph.edge_adj _ _ _ _).mpr
    ⟨Or.inl ⟨rfl, rfl⟩, Subtype.val_injective.ne F.parent_edge.ne⟩)
  have hG₂ : G.Adj parent w := Or.inr ((SimpleGraph.edge_adj _ _ _ _).mpr
    ⟨Or.inl ⟨rfl, rfl⟩, Subtype.val_injective.ne H.parent_edge.ne⟩)
  have hN₁ : Network.TerminalOnly (Finset.univ \ I.terminals) E₁ :=
    edge_terminalOnly _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, F.parent_nonterminal⟩)
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, F.center_nonterminal⟩)
  have hN₂ : Network.TerminalOnly (Finset.univ \ I.terminals) E₂ :=
    edge_terminalOnly _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, H.parent_nonterminal⟩)
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, H.center_nonterminal⟩)
  have hN : Network.TerminalOnly (Finset.univ \ I.terminals) G := by
    intro x y hxy
    exact hxy.elim (hN₁ x y) (hN₂ x y)
  have h11 := parent_ne_child_edge F F.left F.parent_ne_left
  have h12 := parent_ne_child_edge F F.right F.parent_ne_right
  have h23 := parent_ne_child_edge H H.left H.parent_ne_left
  have h21 (B : Limb S v) (hp : parent ≠ B.stem) : s(parent, w) ≠ s(v, B.stem) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
    · exact F.parent_edge.ne h
    · exact hp h
  have h13 : s(parent, v) ≠ s(w, H.left.stem) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
    · exact H.parent_edge.ne h
    · exact H.parent_ne_left h
  have heLR : s(v, F.left.stem) ≠ s(v, F.right.stem) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨_, h⟩ | ⟨h, h'⟩
    · exact F.stems_ne h
    · exact F.stems_ne (h'.trans h)
  have hStem : H.left.stem ≠ v := by
    intro he
    have hadj : S.graph.Adj v w := by simpa only [he] using H.left.stem_adj.symm
    exact distinct_neighbors_not_adj parent v w F.parent_edge H.parent_edge hadj
  have heCross (B : Limb S v) : s(v, B.stem) ≠ s(w, H.left.stem) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
    · exact hvw h
    · exact hStem h.symm
  have hAvoid (B : Limb S v) (h1 : s(parent, v) ≠ s(v, B.stem))
      (h2 : s(parent, w) ≠ s(v, B.stem)) :
      G ≤ S.ambient.deleteEdges {s((v : V), (B.stem : V))} :=
    sup_le (edge_delete_le_of_adj_ne ha₁ _ (pair_val_ne S _ _ _ _ h1))
      (edge_delete_le_of_adj_ne ha₂ _ (pair_val_ne S _ _ _ _ h2))
  have hAvoidH : G ≤ S.ambient.deleteEdges {s((w : V), (H.left.stem : V))} :=
    sup_le (edge_delete_le_of_adj_ne ha₁ _ (pair_val_ne S _ _ _ _ h13))
      (edge_delete_le_of_adj_ne ha₂ _ (pair_val_ne S _ _ _ _ h23))
  exact three v v w F.left F.right H.left G
    (sup_le (edge_le_of_adj ha₁) (edge_le_of_adj ha₂)) hN parent
    hG₁.reachable hG₁.reachable hG₂.reachable
    (hAvoid F.left h11 (h21 F.left F.parent_ne_left))
    (hAvoid F.right h12 (h21 F.right F.parent_ne_right)) hAvoidH
    heLR (heCross F.left) (heCross F.right)

end SteinerUpperBound.Structural.Tree.CoreFrame
