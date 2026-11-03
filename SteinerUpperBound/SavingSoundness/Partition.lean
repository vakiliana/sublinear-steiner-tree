module

public import SteinerUpperBound.SavingSoundness.Graphs
public import SteinerUpperBound.Covers.Geometry.Structural

@[expose] public section

namespace SteinerUpperBound.SavingSoundness

open Covers.Geometry
open scoped Classical BigOperators

variable {V J W : Type*}

abbrev Cells (I : Instance V) (N : Finset V) (a : ℝ) :=
  ↥(componentsOn I N a)

abbrev Labels (I : Instance V) (N : Finset V) (a : ℝ) :=
  Cells I N a ⊕ {x : V // x ∉ I.terminals}

noncomputable instance [Fintype V] (I : Instance V) (N : Finset V) (a : ℝ) :
    Fintype (Labels I N a) := by
  classical
  unfold Labels Cells
  infer_instance

noncomputable def label (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (a : ℝ) (x : V) : Labels I N a :=
  if hx : x ∈ I.terminals then Sum.inl
    ⟨componentOn I N a (project I I.terminals N ρ hc x),
      componentOn_mem_componentsOn I N a (project_mem I I.terminals N ρ hc hx)⟩
  else Sum.inr ⟨x, hx⟩

theorem label_terminal (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (a : ℝ) {x : V} (hx : x ∈ I.terminals) :
    label I N ρ hc a x = Sum.inl
      ⟨componentOn I N a (project I I.terminals N ρ hc x),
        componentOn_mem_componentsOn I N a (project_mem I I.terminals N ρ hc hx)⟩ := by
  simp [label, hx]

theorem label_retained (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals) (a : ℝ)
    {x : V} (hx : x ∈ N) :
    label I N ρ hc a x = Sum.inl
      ⟨componentOn I N a x, componentOn_mem_componentsOn I N a hx⟩ := by
  rw [label_terminal I N ρ hc a (hNT hx)]
  apply congrArg Sum.inl
  apply Subtype.ext
  exact congrArg (componentOn I N a) (project_fix I I.terminals N ρ hc hx)

theorem label_of_mem_cell (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals) (a : ℝ)
    (C : Cells I N a) {x : V} (hx : x ∈ C.val) :
    label I N ρ hc a x = Sum.inl C := by
  have hxN := componentsOn_subset I N a C.property hx
  rw [label_retained I N ρ hc hNT a hxN]
  exact congrArg Sum.inl (Subtype.ext (componentOn_eq_of_mem I N a C.property hx))

theorem label_surjective (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals) (a : ℝ) :
    Function.Surjective (label I N ρ hc a) := by
  intro c
  cases c with
  | inl C =>
      obtain ⟨x, hx⟩ := componentsOn_nonempty I N a C.property
      exact ⟨x, label_of_mem_cell I N ρ hc hNT a C hx⟩
  | inr x => exact ⟨x.val, by simp [label, x.property]⟩

noncomputable def fiberGraph (q : V → W) : SimpleGraph V where
  Adj x y := x ≠ y ∧ q x = q y
  symm := ⟨by rintro x y ⟨hne, he⟩; exact ⟨hne.symm, he.symm⟩⟩
  loopless := ⟨by rintro x ⟨h, _⟩; exact h rfl⟩

theorem fiberGraph_reachable (q : V → W) (x y : V) :
    (fiberGraph q).Reachable x y ↔ q x = q y := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => rfl
    | @cons x y z hxy p ih => exact hxy.2.trans ih
  · intro h
    by_cases he : x = y
    · subst y; exact SimpleGraph.Reachable.refl _
    · exact (show (fiberGraph q).Adj x y from ⟨he, h⟩).reachable

theorem threshold_le_partition [Fintype V] (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hρ : 0 ≤ ρ) (a : ℝ) :
    Structural.threshold I (a - 2 * ρ) ≤ fiberGraph (label I N ρ hc a) := by
  intro x y hxy
  obtain ⟨hne, hx, hy, hd⟩ := (Structural.threshold_adj I _ x y).mp hxy
  have ha : (thresholdOn I I.terminals (a - 2 * ρ)).Adj x y :=
    (thresholdOn_adj I I.terminals _ x y).mpr ⟨hne, hx, hy, hd⟩
  have hp := project_reachable I I.terminals N ρ hc hρ a ha.reachable
  refine ⟨hne, ?_⟩
  rw [label_terminal I N ρ hc a hx, label_terminal I N ρ hc a hy]
  exact congrArg Sum.inl (Subtype.ext (componentOn_eq_of_reachable I N a hp))

theorem cells_separated (I : Instance V) (N : Finset V) (a : ℝ)
    (C D : Cells I N a) (hne : C ≠ D) {x y : V}
    (hx : x ∈ C.val) (hy : y ∈ D.val) : a ≤ I.distance x y := by
  by_contra hn
  have hd : I.distance x y < a := lt_of_not_ge hn
  have hr : (thresholdOn I N a).Reachable x y := by
    by_cases he : x = y
    · subst y; exact SimpleGraph.Reachable.refl _
    · exact ((thresholdOn_adj I N a x y).mpr ⟨he,
        componentsOn_subset I N a C.property hx,
        componentsOn_subset I N a D.property hy, hd⟩).reachable
  have he := componentOn_eq_of_reachable I N a hr
  rw [componentOn_eq_of_mem I N a C.property hx,
    componentOn_eq_of_mem I N a D.property hy] at he
  exact hne (Subtype.ext he)

theorem partition_gain [Fintype V] [Fintype J] (I : Instance V)
    (N : Finset V) (ρ : ℝ) (hc : CoverOn I I.terminals N ρ)
    (hNT : N ⊆ I.terminals) (a : ℝ) (ports : J → Finset (Cells I N a))
    (pick : ∀ j, ↥(ports j) → V) (hcell : ∀ j c, pick j c ∈ c.val.val) :
    GraphRank.gain (fiberGraph (label I N ρ hc a)) (chosenLinks ports pick) =
      (GraphRank.rank (SetSystem.portGraph ports) : ℝ) := by
  have hq := SetSystem.quotient_gain (fiberGraph (label I N ρ hc a))
    (chosenLinks ports pick) (label I N ρ hc a) (label_surjective I N ρ hc hNT a)
    (fiberGraph_reachable _)
  have hm := chosenLinks_map ports pick (label I N ρ hc a)
    (Sum.inl : Cells I N a → Labels I N a)
    (fun j c => label_of_mem_cell I N ρ hc hNT a c.val (hcell j c))
  rw [hm, SetSystem.rank_map_injective _ Sum.inl Sum.inl_injective] at hq
  exact hq

end SteinerUpperBound.SavingSoundness
