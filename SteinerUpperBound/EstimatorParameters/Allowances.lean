module

public import SteinerUpperBound.EstimatorParameters.Confidence

@[expose] public section

namespace SteinerUpperBound.EstimatorParameters

open scoped Classical BigOperators

def A (n : ℕ) : ℕ :=
  1 + 505 * Hc n + 60000000000 * heightBudget n * coverTrials n * hopBudget n

def AM (n : ℕ) : ℕ :=
  1 + 5000000000000005 * Hc n +
    600000000000000000 * heightBudget n * coverTrials n * hopBudget n

def aFactor : ℕ :=
  1 + 505 * hcFactor + 120000000000 * heightFactor * clockFactor

def amFactor : ℕ :=
  1 + 5000000000000005 * hcFactor + 1200000000000000000 * heightFactor * clockFactor

theorem A_pos (n : ℕ) : 0 < A n := by unfold A; omega
theorem AM_pos (n : ℕ) : 0 < AM n := by unfold AM; omega

theorem mass_product_bound (n : ℕ) :
    heightBudget n * coverTrials n * hopBudget n ≤
      (2 * heightFactor * clockFactor) * ell n ^ 3 := by
  have hp := (elementary_polylog n).1
  unfold heightBudget hopBudget
  calc
    _ ≤ (heightFactor * ell n) * ((2 * clockFactor) * ell n) * ell n :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)
    _ = _ := by ring

theorem allowance_polylog (n : ℕ) :
    A n ≤ aFactor * ell n ^ 3 ∧ AM n ≤ amFactor * ell n ^ 3 := by
  have he : ell n ≤ ell n ^ 3 := by
    simpa only [pow_one] using ell_power_le n 1 3 (by omega)
  have hh : Hc n ≤ hcFactor * ell n ^ 3 :=
    (elementary_polylog n).2.2.trans (Nat.mul_le_mul_left _ he)
  have h1 : 1 ≤ ell n ^ 3 := by
    have h : 0 < ell n ^ 3 := by positivity [ell_pos n]
    exact h
  have hp := mass_product_bound n
  constructor
  · have hm := Nat.mul_le_mul_left 60000000000 hp
    have hc := Nat.mul_le_mul_left 505 hh
    unfold A aFactor
    nlinarith
  · have hm := Nat.mul_le_mul_left 600000000000000000 hp
    have hc := Nat.mul_le_mul_left 5000000000000005 hh
    unfold AM amFactor
    nlinarith

theorem coarse_allowance_eq (n : ℕ) (g : MSTApproximation.Grid) (hq : g.q = Structural.omega) :
    (A n : ℝ) = 1 +
      MSTApproximation.massAllowance g deltaCoarse (Hc n) (coverTrials n) (hopBudget n) (heightBudget n) := by
  unfold A MSTApproximation.massAllowance
  push_cast
  rw [hq]
  norm_num [deltaCoarse, deltaCoarseQ, Structural.omega]
  ring

theorem fine_allowance_eq (n : ℕ) (g : MSTApproximation.Grid) (hq : g.q = MSTApproximation.fineRatio nu) :
    (AM n : ℝ) = 1 +
      MSTApproximation.massAllowance g deltaFine (Hc n) (coverTrials n) (hopBudget n) (heightBudget n) := by
  unfold AM MSTApproximation.massAllowance
  push_cast
  rw [hq]
  norm_num [deltaFine, deltaFineQ, MSTApproximation.fineRatio, nu, nuQ, cQ]
  ring

theorem coarse_mass_bound {V : Type*} [Fintype V] (I : Instance V)
    (g : MSTApproximation.Grid) (N : ℕ → Finset V) (n : ℕ) (R : ℝ)
    (hq : g.q = Structural.omega) (hR : 0 ≤ R) (hRL : R ≤ I.mst)
    (hn : g.intervals ≤ heightBudget n) (hlast : g.scale g.intervals ≤ 4 * g.q * R)
    (hsize : ∀ i < g.intervals, ((N i).card : ℝ) ≤
      Hc n + 6 * coverTrials n * hopBudget n * I.mst / (deltaCoarse * g.scale i)) :
    MSTApproximation.weightedMass g N ≤ (A n : ℝ) * I.mst := by
  have hm := MSTApproximation.weightedMass_bound I g N deltaCoarse (Hc n) (coverTrials n) (hopBudget n)
    R (heightBudget n) (by norm_num [deltaCoarse, deltaCoarseQ]) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hR hRL hn hlast hsize
  have he := coarse_allowance_eq n g hq
  have hl : MSTApproximation.massAllowance g deltaCoarse (Hc n) (coverTrials n)
      (hopBudget n) (heightBudget n) ≤ (A n : ℝ) := by linarith
  exact hm.trans (mul_le_mul_of_nonneg_right hl I.mst_nonneg)

theorem fine_mass_bound {V : Type*} [Fintype V] (I : Instance V)
    (g : MSTApproximation.Grid) (N : ℕ → Finset V) (n : ℕ) (R : ℝ)
    (hq : g.q = MSTApproximation.fineRatio nu) (hR : 0 ≤ R) (hRL : R ≤ I.mst)
    (hn : g.intervals ≤ heightBudget n) (hlast : g.scale g.intervals ≤ 4 * g.q * R)
    (hsize : ∀ i < g.intervals, ((N i).card : ℝ) ≤
      Hc n + 6 * coverTrials n * hopBudget n * I.mst / (deltaFine * g.scale i)) :
    MSTApproximation.weightedMass g N ≤ (AM n : ℝ) * I.mst := by
  have hm := MSTApproximation.weightedMass_bound I g N deltaFine (Hc n) (coverTrials n) (hopBudget n)
    R (heightBudget n) (by norm_num [deltaFine, deltaFineQ, nuQ, cQ]) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hR hRL hn hlast hsize
  have he := fine_allowance_eq n g hq
  have hl : MSTApproximation.massAllowance g deltaFine (Hc n) (coverTrials n)
      (hopBudget n) (heightBudget n) ≤ (AM n : ℝ) := by linarith
  exact hm.trans (mul_le_mul_of_nonneg_right hl I.mst_nonneg)

end SteinerUpperBound.EstimatorParameters
