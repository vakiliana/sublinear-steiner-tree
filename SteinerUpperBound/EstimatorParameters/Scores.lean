module

public import SteinerUpperBound.EstimatorParameters.Allowances

@[expose] public section

namespace SteinerUpperBound.EstimatorParameters

open scoped Classical

def epsInv (n : ℕ) : ℕ := 1000000000 * A n
def epsQ (n : ℕ) : ℚ := 1 / epsInv n
def B (n : ℕ) : ℕ := 10 * epsInv n
def BQ (n : ℕ) : ℕ := 400 * A n
def xiSavingInv (n : ℕ) : ℕ := 100 * epsInv n
def xiBandInv (n : ℕ) : ℕ := 100000000 * A n
def BM (n : ℕ) : ℕ := 1000000000000000 * AM n
def xiMInv (n : ℕ) : ℕ := BM n
def xiSavingQ (n : ℕ) : ℚ := 1 / xiSavingInv n
def xiBandQ (n : ℕ) : ℚ := 1 / xiBandInv n
def xiMQ (n : ℕ) : ℚ := 1 / xiMInv n

noncomputable abbrev eps (n : ℕ) : ℝ := (epsQ n : ℝ)
noncomputable abbrev xiSaving (n : ℕ) : ℝ := (xiSavingQ n : ℝ)
noncomputable abbrev xiBand (n : ℕ) : ℝ := (xiBandQ n : ℝ)
noncomputable abbrev xiM (n : ℕ) : ℝ := (xiMQ n : ℝ)

theorem integer_budget_pos (n : ℕ) :
    0 < epsInv n ∧ 0 < B n ∧ 0 < BQ n ∧
      0 < xiSavingInv n ∧ 0 < xiBandInv n ∧ 0 < BM n ∧ 0 < xiMInv n := by
  have ha := A_pos n
  have hm := AM_pos n
  dsimp only [epsInv, B, BQ, xiSavingInv, xiBandInv, BM, xiMInv]
  exact ⟨by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity⟩

theorem score_scalar_equations (n : ℕ) :
    eps n = Structural.e0 / (100000 * (A n : ℝ)) ∧
      xiSaving n = eps n / 100 ∧ xiBand n = Structural.sigma0 / (100000 * (A n : ℝ)) ∧
      xiM n = nu / (100 * (AM n : ℝ)) := by
  unfold eps epsQ xiSaving xiSavingQ xiBand xiBandQ xiM xiMQ
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  dsimp only [epsInv, xiSavingInv, xiBandInv, xiMInv, BM]
  push_cast
  norm_num [Structural.e0, Structural.sigma0, nu, nuQ, cQ] <;> ring_nf <;> simp

theorem reciprocal_range (d : ℕ) (hd : 0 < d) :
    0 < (1 / (d : ℝ)) ∧ 1 / (d : ℝ) ≤ 1 := by
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact ⟨by positivity, (div_le_one hp).mpr h1⟩

theorem score_ranges (n : ℕ) :
    0 < eps n ∧ eps n ≤ 1 / 100 ∧ 0 < xiSaving n ∧ xiSaving n ≤ 1 ∧
      0 < xiBand n ∧ xiBand n ≤ 1 ∧ 0 < xiM n ∧ xiM n ≤ 1 := by
  obtain ⟨he, _, _, hs, hb, _, hm⟩ := integer_budget_pos n
  have hsr := reciprocal_range _ hs
  have hbr := reciprocal_range _ hb
  have hmr := reciprocal_range _ hm
  simp only [eps, epsQ, xiSaving, xiSavingQ, xiBand, xiBandQ, xiM, xiMQ,
    Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  refine ⟨(reciprocal_range _ he).1, ?_, hsr.1, hsr.2, hbr.1, hbr.2, hmr.1, hmr.2⟩
  have hp : (0 : ℝ) < epsInv n := by exact_mod_cast he
  have hA : (1 : ℝ) ≤ A n := by exact_mod_cast A_pos n
  apply (div_le_div_iff₀ hp (by norm_num : (0 : ℝ) < 100)).mpr
  dsimp only [epsInv]
  push_cast
  nlinarith

theorem integer_budget_equations (n : ℕ) :
    (B n : ℝ) = 10 / eps n ∧ (BQ n : ℝ) = 400 * (A n : ℝ) ∧
      (BM n : ℝ) = 100 * (AM n : ℝ) / nu := by
  have ha : (0 : ℝ) < A n := by exact_mod_cast A_pos n
  have hm : (0 : ℝ) < AM n := by exact_mod_cast AM_pos n
  simp only [(score_scalar_equations n).1]
  unfold B BQ BM epsInv
  push_cast
  norm_num [Structural.e0, nu, nuQ, cQ]
  field_simp
  norm_num

theorem actual_ceiling_budgets (n : ℕ) :
    B n = ⌈10 / eps n⌉₊ ∧ BQ n = ⌈400 * (A n : ℝ)⌉₊ ∧ BM n = ⌈100 * (AM n : ℝ) / nu⌉₊ := by
  rw [← (integer_budget_equations n).1, ← (integer_budget_equations n).2.1,
    ← (integer_budget_equations n).2.2]
  simp

theorem score_budget_polylog (n : ℕ) :
    B n ≤ (10000000000 * aFactor) * ell n ^ 3 ∧
      BQ n ≤ (400 * aFactor) * ell n ^ 3 ∧
      xiSavingInv n ≤ (100000000000 * aFactor) * ell n ^ 3 ∧
      xiBandInv n ≤ (100000000 * aFactor) * ell n ^ 3 ∧
      BM n ≤ (1000000000000000 * amFactor) * ell n ^ 3 := by
  have ha := (allowance_polylog n).1
  have hm := (allowance_polylog n).2
  dsimp only [B, epsInv, BQ, xiSavingInv, xiBandInv, BM]
  constructor
  · nlinarith [Nat.mul_le_mul_left 10000000000 ha]
  constructor
  · nlinarith [Nat.mul_le_mul_left 400 ha]
  constructor
  · nlinarith [Nat.mul_le_mul_left 100000000000 ha]
  constructor
  · nlinarith [Nat.mul_le_mul_left 100000000 ha]
  · nlinarith [Nat.mul_le_mul_left 1000000000000000 hm]

end SteinerUpperBound.EstimatorParameters
