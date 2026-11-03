module

public import SteinerUpperBound.Covers.Geometry
public import SteinerUpperBound.Structural.Statistics

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry

open scoped Classical BigOperators

variable {V : Type*} [Fintype V]

def withTerminals (I : Instance V) (S : Finset V) : Instance V :=
  ⟨I.metric, S⟩

theorem withTerminals_self (I : Instance V) : withTerminals I I.terminals = I := rfl

theorem thresholdOn_eq_structural (I : Instance V) (S : Finset V) (a : ℝ) :
    thresholdOn I S a = Structural.threshold (withTerminals I S) a := by
  ext x y
  rw [thresholdOn_adj, Structural.threshold_adj]
  rfl

theorem componentOn_eq_structural (I : Instance V) (S : Finset V) (a : ℝ) (x : V) :
    componentOn I S a x = Structural.component (withTerminals I S) a x := by
  ext y
  rw [mem_componentOn, Structural.mem_component]
  rw [← thresholdOn_eq_structural]
  rfl

theorem componentsOn_eq_structural (I : Instance V) (S : Finset V) (a : ℝ) :
    componentsOn I S a = Structural.components (withTerminals I S) a := by
  unfold componentsOn Structural.components
  congr 1
  funext x
  exact componentOn_eq_structural I S a x

theorem thresholdOn_terminals_eq (I : Instance V) (a : ℝ) :
    thresholdOn I I.terminals a = Structural.threshold I a := by
  rw [thresholdOn_eq_structural, withTerminals_self]

theorem componentsOn_terminals_eq (I : Instance V) (a : ℝ) :
    componentsOn I I.terminals a = Structural.components I a := by
  rw [componentsOn_eq_structural, withTerminals_self]

theorem rowOn_eq_structural (I : Instance V) (a : ℝ) (v : V) :
    rowOn I I.terminals a (3 * a / 5) v = Structural.row I a v := by
  unfold rowOn Structural.row
  rw [componentsOn_terminals_eq]

theorem eligibleOn_eq_structural (I : Instance V) (a : ℝ) :
    eligibleOn I I.terminals a (3 * a / 5) = Structural.eligible I a := by
  classical
  ext v
  simp only [eligibleOn, Structural.eligible, Finset.mem_filter, Finset.mem_univ, true_and,
    rowOn_eq_structural]

noncomputable def savingOn (I : Instance V) (S : Finset V) (a radius : ℝ) : ℝ :=
  Structural.saving (eligibleOn I S a radius) (rowOn I S a radius) (componentsOn I S a)

theorem savingOn_domination (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) (idealRadius retainedRadius : ℝ)
    (hradius : idealRadius + ρ ≤ retainedRadius) :
    savingOn I T a idealRadius ≤ savingOn I N a retainedRadius := by
  classical
  apply Structural.saving_domination_of_rows
    (eligibleOn I T a idealRadius) (eligibleOn I N a retainedRadius)
    (rowOn I T a idealRadius) (rowOn I N a retainedRadius)
    (componentsOn I T a) (componentsOn I N a) (componentMap I T a)
    (eligibility_domination I T N ρ hc hNT hρ a hρa _ _ hradius)
  · intro v _
    intro C hC
    obtain ⟨D, hD, he⟩ := Finset.mem_image.mp
      (row_domination I T N ρ hc hNT hρ a hρa _ _ hradius v hC)
    exact (@Finset.mem_image (Finset V) (Finset V) (Classical.decEq _)
      (componentMap I T a) (rowOn I N a retainedRadius v) C).mpr ⟨D, hD, he⟩
  · intro v _
    exact rowOn_subset_componentsOn I N a retainedRadius v

theorem savingOn_eq_structural (I : Instance V) (a : ℝ) :
    savingOn I I.terminals a (3 * a / 5) = Structural.rowSaving I a := by
  have hr : rowOn I I.terminals a (3 * a / 5) = Structural.row I a :=
    funext (rowOn_eq_structural I a)
  unfold savingOn Structural.rowSaving
  rw [eligibleOn_eq_structural, componentsOn_terminals_eq, hr]

/-- The ideal structural row saving is dominated by the actual retained-row
saving at radius `5a/8`, with no assumed row-domination certificate. -/
theorem structural_rowSaving_le_retained (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) (hgap : 3 * a / 5 + ρ < 5 * a / 8) :
    Structural.rowSaving I a ≤ savingOn I N a (5 * a / 8) := by
  rw [← savingOn_eq_structural]
  exact savingOn_domination I I.terminals N ρ hc hNT hρ a hρa _ _ hgap.le

theorem structural_bottleneck_upper (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hρ : 0 ≤ ρ) (a : ℝ)
    {C : Finset V} (hC : C ∈ Structural.components (withTerminals I N) a)
    {x y : V} (hx : x ∈ C) (hy : y ∈ C) (t : ℝ)
    (hxy : (Structural.threshold I t).Reachable x y) :
    (Structural.threshold (withTerminals I C) (t + 2 * ρ)).Reachable x y := by
  rw [← componentsOn_eq_structural] at hC
  rw [← thresholdOn_terminals_eq] at hxy
  rw [← thresholdOn_eq_structural]
  exact bottleneck_upper I I.terminals N ρ hc hρ a hC hx hy t hxy

theorem structural_nonpersistent_card_le_drop (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hρ : 0 ≤ ρ) (a : ℝ) :
    (nonpersistent I I.terminals N ρ hc a).card ≤
      (Structural.components I (a - 2 * ρ)).card - (Structural.components I a).card := by
  simpa only [componentsOn_terminals_eq] using
    nonpersistent_card_le_drop I I.terminals N ρ hc hρ a

end SteinerUpperBound.Covers.Geometry
