module

public import SteinerUpperBound.Covers.Actual

@[expose] public section

namespace SteinerUpperBound.Covers

open SteinerLowerBound
open scoped Classical BigOperators

noncomputable local instance {V : Type*} (I : Instance V) : DecidableEq (Terminal I) :=
  Classical.decEq _

theorem hopCount_pos (k : ℕ) : 0 < hopCount k := by
  unfold hopCount
  omega

theorem actual_cover_at_radius {V : Type*} [Fintype V] (I : Instance V)
    (ρ : ℝ) (hρ : 0 < ρ) (root : Terminal I) (B ψ : ℕ) (v : ℝ) :
    (actualBits I (ρ / hopCount I.terminals.card) root B ψ).prob
      {b | ¬ IsCover I ρ b ∨
        Real.exp 1 * (1 + (ψ : ℝ) *
          (1 + 2 * hopCount I.terminals.card * I.mst / ρ)) + v ≤
            ((CategoricalCoupling.selected b).card : ℝ)} ≤
      (I.terminals.card : ℝ) * Real.exp (-(ψ : ℝ) / 2) + Real.exp (-v) +
        (I.terminals.card : ℝ) * Real.exp (-(B : ℝ) / I.terminals.card) := by
  have hh : (0 : ℝ) < hopCount I.terminals.card := by exact_mod_cast hopCount_pos _
  have hr : 0 < ρ / (hopCount I.terminals.card : ℝ) := div_pos hρ hh
  have he : (hopCount I.terminals.card : ℝ) * (ρ / hopCount I.terminals.card) = ρ := by
    field_simp
  have hc : 2 * I.mst / (ρ / hopCount I.terminals.card) =
      2 * hopCount I.terminals.card * I.mst / ρ := by
    field_simp
  simpa only [he, hc] using actual_cover_and_size I _ hr root B ψ _
    (hopCount_growth I.terminals.card) v

theorem actual_cover_at_radius_budget {V : Type*} [Fintype V] (I : Instance V)
    (ρ : ℝ) (hρ : 0 < ρ) (root : Terminal I) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 0 < β) :
    (actualBits I (ρ / hopCount I.terminals.card) root
      (privateDrawBudget I.terminals.card m β) (retentionBudget I.terminals.card m β)).prob
      {b | ¬ IsCover I ρ b ∨
        Real.exp 1 * (1 + (retentionBudget I.terminals.card m β : ℝ) *
          (1 + 2 * hopCount I.terminals.card * I.mst / ρ)) + sizeSlack m β ≤
            ((CategoricalCoupling.selected b).card : ℝ)} ≤ β / m := by
  apply (actual_cover_at_radius I ρ hρ root _ _ _).trans
  exact budget_error I.terminals.card m (Finset.card_pos.mpr ⟨root.val, root.property⟩)
    hm β hβ

end SteinerUpperBound.Covers
