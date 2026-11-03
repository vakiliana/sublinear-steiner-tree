module

public import SteinerUpperBound.Covers.Geometry.Projection

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry

open scoped Classical BigOperators

variable {V : Type*}

theorem cover_nonempty (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hT : T.Nonempty) : N.Nonempty := by
  obtain ⟨x, hx⟩ := hT
  obtain ⟨y, hy, _⟩ := hc x hx
  exact ⟨y, hy⟩

theorem projected_componentMap (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) {x : V} (hx : x ∈ T) :
    componentMap I T a (componentOn I N a (project I T N ρ hc x)) =
      componentOn I T a x := by
  have hyN := project_mem I T N ρ hc hx
  have hD := componentOn_mem_componentsOn I N a hyN
  rw [componentMap_eq I T a hD hNT (componentOn_self I N a hyN)]
  exact (componentOn_eq_of_reachable I T a
    (terminal_attachment I T N ρ hc hNT hρ a hρa hx)).symm

/-- Every exact terminal component receives a retained component. The map is
proved onto, not assumed as a partition certificate. -/
theorem componentMap_image (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) :
    (componentsOn I N a).image (componentMap I T a) = componentsOn I T a := by
  classical
  apply Finset.Subset.antisymm
  · intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    exact componentMap_mem I T a hNT hD
  · intro C hC
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hC
    exact Finset.mem_image.mpr
      ⟨componentOn I N a (project I T N ρ hc x),
        componentOn_mem_componentsOn I N a (project_mem I T N ρ hc hx),
        projected_componentMap I T N ρ hc hNT hρ a hρa hx⟩

theorem components_card_le_retained (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) :
    (componentsOn I T a).card ≤ (componentsOn I N a).card := by
  rw [← componentMap_image I T N ρ hc hNT hρ a hρa]
  exact Finset.card_image_le

noncomputable def projectedComponentMap (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (a : ℝ) (C : Finset V) : Finset V :=
  if hC : C.Nonempty then
    componentOn I N a (project I T N ρ hc (Classical.choose hC)) else ∅

theorem projectedComponentMap_eq (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hρ : 0 ≤ ρ) (a : ℝ) {C : Finset V}
    (hC : C ∈ componentsOn I T (a - 2 * ρ)) {x : V} (hx : x ∈ C) :
    projectedComponentMap I T N ρ hc a C = componentOn I N a (project I T N ρ hc x) := by
  have hn := componentsOn_nonempty I T (a - 2 * ρ) hC
  have hr := componentOn_pair_reachable I T (a - 2 * ρ) hC (Classical.choose_spec hn) hx
  rw [projectedComponentMap, dif_pos hn]
  exact componentOn_eq_of_reachable I N a (project_reachable I T N ρ hc hρ a hr)

theorem projectedComponentMap_image (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ) (a : ℝ) :
    (componentsOn I T (a - 2 * ρ)).image (projectedComponentMap I T N ρ hc a) =
      componentsOn I N a := by
  classical
  apply Finset.Subset.antisymm
  · intro D hD
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨x, hx⟩ := componentsOn_nonempty I T (a - 2 * ρ) hC
    rw [projectedComponentMap_eq I T N ρ hc hρ a hC hx]
    exact componentOn_mem_componentsOn I N a
      (project_mem I T N ρ hc (componentsOn_subset I T (a - 2 * ρ) hC hx))
  · intro D hD
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hD
    have hF := componentOn_mem_componentsOn I T (a - 2 * ρ) (hNT hy)
    refine Finset.mem_image.mpr
      ⟨componentOn I T (a - 2 * ρ) y, hF, ?_⟩
    rw [projectedComponentMap_eq I T N ρ hc hρ a hF
      (componentOn_self I T (a - 2 * ρ) (hNT hy)), project_fix I T N ρ hc hy]

theorem components_card_sandwich (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) :
    (componentsOn I T a).card ≤ (componentsOn I N a).card ∧
      (componentsOn I N a).card ≤ (componentsOn I T (a - 2 * ρ)).card := by
  refine ⟨components_card_le_retained I T N ρ hc hNT hρ a hρa, ?_⟩
  rw [← projectedComponentMap_image I T N ρ hc hNT hρ a]
  exact Finset.card_image_le

noncomputable def rowOn (I : Instance V) (S : Finset V) (a radius : ℝ) (v : V) :
    Finset (Finset V) :=
  (componentsOn I S a).filter (fun C => ∃ x ∈ C, I.distance v x ≤ radius)

theorem mem_rowOn (I : Instance V) (S : Finset V) (a radius : ℝ) (v : V) (C : Finset V) :
    C ∈ rowOn I S a radius v ↔
      C ∈ componentsOn I S a ∧ ∃ x ∈ C, I.distance v x ≤ radius := by
  classical
  exact Finset.mem_filter

theorem rowOn_subset_componentsOn (I : Instance V) (S : Finset V)
    (a radius : ℝ) (v : V) : rowOn I S a radius v ⊆ componentsOn I S a :=
  Finset.filter_subset _ _

/-- Covering the witness terminal by its retained projection dominates every
ideal row after mapping retained components onto exact components. -/
theorem row_domination (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) (idealRadius retainedRadius : ℝ)
    (hradius : idealRadius + ρ ≤ retainedRadius) (v : V) :
    rowOn I T a idealRadius v ⊆
      (rowOn I N a retainedRadius v).image (componentMap I T a) := by
  classical
  intro C hC
  obtain ⟨hCcomp, x, hxC, hdist⟩ := (mem_rowOn I T a idealRadius v C).mp hC
  have hxT := componentsOn_subset I T a hCcomp hxC
  let y := project I T N ρ hc x
  have hyN : y ∈ N := project_mem I T N ρ hc hxT
  let D := componentOn I N a y
  have hD : D ∈ rowOn I N a retainedRadius v := by
    apply (mem_rowOn I N a retainedRadius v D).mpr
    refine ⟨componentOn_mem_componentsOn I N a hyN, y, componentOn_self I N a hyN, ?_⟩
    have htriangle := I.distance_triangle v x y
    have hmove : I.distance x y ≤ ρ := project_move I T N ρ hc hρ hxT
    linarith
  refine Finset.mem_image.mpr ⟨D, hD, ?_⟩
  exact (projected_componentMap I T N ρ hc hNT hρ a hρa hxT).trans
    (componentOn_eq_of_mem I T a hCcomp hxC)

theorem row_card_le_retained (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) (idealRadius retainedRadius : ℝ)
    (hradius : idealRadius + ρ ≤ retainedRadius) (v : V) :
    (rowOn I T a idealRadius v).card ≤ (rowOn I N a retainedRadius v).card :=
  (Finset.card_le_card
    (row_domination I T N ρ hc hNT hρ a hρa idealRadius retainedRadius hradius v)).trans
      Finset.card_image_le

noncomputable def eligibleOn [Fintype V] (I : Instance V) (S : Finset V)
    (a radius : ℝ) : Finset V :=
  Finset.univ.filter (fun v => 3 ≤ (rowOn I S a radius v).card)

theorem eligibility_domination [Fintype V] (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) (idealRadius retainedRadius : ℝ)
    (hradius : idealRadius + ρ ≤ retainedRadius) :
    eligibleOn I T a idealRadius ⊆ eligibleOn I N a retainedRadius := by
  classical
  intro v hv
  have hv3 := (Finset.mem_filter.mp hv).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    hv3.trans (row_card_le_retained I T N ρ hc hNT hρ a hρa
      idealRadius retainedRadius hradius v)⟩

theorem ideal_retained_rows (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) (hgap : 3 * a / 5 + ρ < 5 * a / 8) (v : V) :
    rowOn I T a (3 * a / 5) v ⊆
      (rowOn I N a (5 * a / 8) v).image (componentMap I T a) :=
  row_domination I T N ρ hc hNT hρ a hρa _ _ hgap.le v

theorem ideal_retained_eligibility [Fintype V] (I : Instance V)
    (T N : Finset V) (ρ : ℝ) (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) (hgap : 3 * a / 5 + ρ < 5 * a / 8) :
    eligibleOn I T a (3 * a / 5) ⊆ eligibleOn I N a (5 * a / 8) :=
  eligibility_domination I T N ρ hc hNT hρ a hρa _ _ hgap.le

end SteinerUpperBound.Covers.Geometry
