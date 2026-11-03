module

public import SteinerUpperBound.MSTApproximation.Quadrature
public import SteinerUpperBound.Covers.Scales

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry
open scoped Classical BigOperators

variable {V : Type*} [Fintype V]

noncomputable def weightedMass (g : Grid) (N : ℕ → Finset V) : ℝ :=
  ∑ i ∈ Finset.range g.intervals, g.scale i * (N i).card

noncomputable def massAllowance (g : Grid) (delta Hc psi hop : ℝ) (budget : ℕ) : ℝ :=
  Hc * (5 * g.q / (g.q - 1)) + (budget : ℝ) * (6 * psi * hop / delta)

theorem weightedMass_bound (I : Instance V) (g : Grid) (N : ℕ → Finset V)
    (delta Hc psi hop R : ℝ) (budget : ℕ)
    (hd : 0 < delta) (hH : 0 ≤ Hc) (hp : 0 ≤ psi) (hh : 0 ≤ hop)
    (hR : 0 ≤ R) (hRL : R ≤ I.mst) (hn : g.intervals ≤ budget)
    (hlast : g.scale g.intervals ≤ 4 * g.q * R)
    (hsize : ∀ i < g.intervals,
      ((N i).card : ℝ) ≤ Hc + 6 * psi * hop * I.mst / (delta * g.scale i)) :
    weightedMass g N ≤ massAllowance g delta Hc psi hop budget * I.mst := by
  have hpoint (i : ℕ) (hi : i < g.intervals) :
      g.scale i * (N i).card ≤ Hc * g.scale i + 6 * psi * hop * I.mst / delta := by
    have h := mul_le_mul_of_nonneg_left (hsize i hi) (g.scale_pos i).le
    have he : g.scale i * (Hc + 6 * psi * hop * I.mst / (delta * g.scale i)) =
        Hc * g.scale i + 6 * psi * hop * I.mst / delta := by
      field_simp [hd.ne', (g.scale_pos i).ne']
      <;> ring
    exact h.trans_eq he
  have hs := Finset.sum_le_sum (fun i hi => hpoint i (Finset.mem_range.mp hi))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hs
  have hcoef : 0 ≤ 5 * g.q / (g.q - 1) :=
    div_nonneg (by positivity [g.ratio_pos]) (sub_pos.mpr g.ratio_gt_one).le
  have hsum := (generated_sum_scales g R hR hlast).trans
    (mul_le_mul_of_nonneg_left hRL hcoef)
  have hsumH := mul_le_mul_of_nonneg_left hsum hH
  have hnR : (g.intervals : ℝ) ≤ budget := by exact_mod_cast hn
  have hbudget := mul_le_mul_of_nonneg_right hnR
    (show 0 ≤ 6 * psi * hop * I.mst / delta by positivity [I.mst_nonneg])
  calc
    weightedMass g N ≤ Hc * (∑ i ∈ Finset.range g.intervals, g.scale i) +
        (g.intervals : ℝ) * (6 * psi * hop * I.mst / delta) := hs
    _ ≤ Hc * (5 * g.q / (g.q - 1) * I.mst) +
        (budget : ℝ) * (6 * psi * hop * I.mst / delta) := add_le_add hsumH hbudget
    _ = _ := by unfold massAllowance; ring

theorem massAllowance_ge_one (g : Grid) (delta Hc psi hop : ℝ) (budget : ℕ)
    (hd : 0 < delta) (hH : 1 ≤ Hc) (hp : 0 ≤ psi) (hh : 0 ≤ hop) :
    1 ≤ massAllowance g delta Hc psi hop budget := by
  have hratio : 1 ≤ 5 * g.q / (g.q - 1) :=
    (le_div_iff₀ (sub_pos.mpr g.ratio_gt_one)).mpr (by linarith [g.ratio_gt_one])
  have hmain := mul_le_mul hH hratio (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
  have hrest : 0 ≤ (budget : ℝ) * (6 * psi * hop / delta) := by positivity
  unfold massAllowance
  nlinarith

theorem factory_size_bound (I : Instance V) (g rho slack : ℝ) (psi hop : ℕ)
    (hr : 0 < rho)
    (hsize : g ≤ Real.exp 1 * (1 + (psi : ℝ) *
      (1 + 2 * hop * I.mst / rho)) + slack) :
    g ≤ (3 * (1 + (psi : ℝ)) + slack) + 6 * psi * hop * I.mst / rho := by
  have hm := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le
    (show 0 ≤ 1 + (psi : ℝ) * (1 + 2 * hop * I.mst / rho) by positivity [I.mst_nonneg])
  calc
    g ≤ Real.exp 1 * (1 + (psi : ℝ) * (1 + 2 * hop * I.mst / rho)) + slack := hsize
    _ ≤ 3 * (1 + (psi : ℝ) * (1 + 2 * hop * I.mst / rho)) + slack := add_le_add hm le_rfl
    _ = _ := by ring

end SteinerUpperBound.MSTApproximation
