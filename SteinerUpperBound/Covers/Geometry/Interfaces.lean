module

public import SteinerUpperBound.Covers.Interfaces
public import SteinerUpperBound.Covers.Geometry.Structural
public import SteinerUpperBound.Covers.Geometry.Band

@[expose] public section

/-!
# Checked geometry signatures for algorithm integration

This facade also imports the four exact probability/factory signatures from
`Covers.Interfaces`. Everything below is proved by the concrete geometry, not
supplied as a partition or projection certificate.

The original namespaces are `Covers.Geometry` and `Covers.Factory`; the
restatements here are in `Covers.Geometry.Interfaces`.
`thresholdOn I S t` has edges between distinct points of `S` at distance `< t`.
`componentOn` and `componentsOn` are actual finite reachable components.
`CoverOn I T N ρ` means `∀ x ∈ T, ∃ y ∈ N, distance x y ≤ ρ`.

Defining modules:
* `Geometry.Projection`: `project`, `projection`, sandwich, bottleneck bounds.
* `Geometry.Domination`: component surjections, counts, rows and eligibility.
* `Geometry.Persistence`: `phaseBad`, `nonpersistent`, component-drop bound,
  and exact retained intersections off the deterministic phase-bad set.
* `Geometry.Structural`: equality with `Structural.Statistics` definitions and
  the ideal-versus-retained saving inequality.
* `Geometry.Selected`: `isCover_iff_coverOn` and `selectedTerminals_card`.

The base `Covers.Geometry` intentionally does not import `Structural`; import
this facade, or `Geometry.Structural`, only above `Structural.Statistics`.
No theorem asserts that conditioning on cover-good preserves a uniform shift.
The persistence bound instead uses the deterministic inclusion
`nonpersistent_subset_phaseBad`, whose right-hand side does not mention `N`.
-/

namespace SteinerUpperBound.Covers.Geometry.Interfaces

open scoped Classical

variable {V : Type*}

theorem projection_spec (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ) :
    (∀ x : {x // x ∈ T}, I.distance x.val (projection I T N ρ hc x).val ≤ ρ) ∧
      (∀ y : {y // y ∈ N},
        (projection I T N ρ hc ⟨y.val, hNT y.property⟩).val = y.val) :=
  ⟨projection_move I T N ρ hc hρ, projection_fix I T N ρ hc hNT⟩

theorem component_sandwich (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) {x : V} (hx : x ∈ T) :
    componentOn I T (a - 2 * ρ) x ⊆ pullbackComponent I T N ρ hc a x ∧
      pullbackComponent I T N ρ hc a x ⊆ componentOn I T a x :=
  SteinerUpperBound.Covers.Geometry.component_sandwich I T N ρ hc hNT hρ a hρa hx

theorem bottleneck_sandwich (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ) (a : ℝ)
    {C : Finset V} (hC : C ∈ componentsOn I N a) {x y : V}
    (hx : x ∈ C) (hy : y ∈ C) :
    (∀ t, (thresholdOn I C t).Reachable x y → (thresholdOn I T t).Reachable x y) ∧
      (∀ t, (thresholdOn I T t).Reachable x y →
        (thresholdOn I C (t + 2 * ρ)).Reachable x y) :=
  ⟨fun t h => bottleneck_lower I T N hNT a hC t h,
    fun t h => bottleneck_upper I T N ρ hc hρ a hC hx hy t h⟩

theorem component_shifted_reachable (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hρ : 0 ≤ ρ) (a : ℝ)
    {C Y : Finset V} (hC : C ∈ componentsOn I N a) (hY : Y ⊆ C)
    (t : ℝ) (hta : t ≤ a - 2 * ρ) {x y : V} (hx : x ∈ Y) (hy : y ∈ Y)
    (hxy : (thresholdOn I T (t - 2 * ρ)).Reachable x y) :
    (thresholdOn I C t).Reachable x y :=
  SteinerUpperBound.Covers.Geometry.component_shifted_reachable
    I T N ρ hc hρ a hC hY t (by linarith) hx hy hxy

theorem componentMap_image (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) :
    (componentsOn I N a).image (componentMap I T a) = componentsOn I T a :=
  SteinerUpperBound.Covers.Geometry.componentMap_image I T N ρ hc hNT hρ a hρa

theorem components_card_sandwich (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) :
    (componentsOn I T a).card ≤ (componentsOn I N a).card ∧
      (componentsOn I N a).card ≤ (componentsOn I T (a - 2 * ρ)).card :=
  SteinerUpperBound.Covers.Geometry.components_card_sandwich I T N ρ hc hNT hρ a hρa

theorem ideal_retained_rows (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) (hgap : 3 * a / 5 + ρ < 5 * a / 8) (v : V) :
    rowOn I T a (3 * a / 5) v ⊆
      (rowOn I N a (5 * a / 8) v).image (componentMap I T a) :=
  SteinerUpperBound.Covers.Geometry.ideal_retained_rows I T N ρ hc hNT hρ a hρa hgap v

theorem ideal_retained_eligibility [Fintype V] (I : Instance V)
    (T N : Finset V) (ρ : ℝ) (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) (hgap : 3 * a / 5 + ρ < 5 * a / 8) :
    eligibleOn I T a (3 * a / 5) ⊆ eligibleOn I N a (5 * a / 8) :=
  SteinerUpperBound.Covers.Geometry.ideal_retained_eligibility I T N ρ hc hNT hρ a hρa hgap

theorem nonpersistent_card_le_drop (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hρ : 0 ≤ ρ) (a : ℝ) :
    (nonpersistent I T N ρ hc a).card ≤
      (componentsOn I T (a - 2 * ρ)).card - (componentsOn I T a).card :=
  SteinerUpperBound.Covers.Geometry.nonpersistent_card_le_drop I T N ρ hc hρ a

theorem structural_rowSaving_le_retained [Fintype V] (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) (hgap : 3 * a / 5 + ρ < 5 * a / 8) :
    Structural.rowSaving I a ≤ savingOn I N a (5 * a / 8) :=
  SteinerUpperBound.Covers.Geometry.structural_rowSaving_le_retained I N ρ hc hNT hρ a hρa hgap

end SteinerUpperBound.Covers.Geometry.Interfaces
