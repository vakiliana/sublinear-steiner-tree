module

public import SteinerUpperBound.EstimatorParameters.Scores

@[expose] public section

namespace SteinerUpperBound.EstimatorParameters

open scoped Classical

def meanSamples (n denom : ℕ) : ℕ := 256 * betaDenom n * denom ^ 2
def proposalClock (n denom : ℕ) : ℕ :=
  Nat.log2 (16 * meanSamples n denom * betaDenom n * denom + 1) + 1
def samplerCap (n k denom : ℕ) : ℕ := k * proposalClock n denom
def meanFactor (F : ℕ) : ℕ := 256 * betaFactor * F ^ 2
def proposalFactor (F : ℕ) : ℕ := 16 * meanFactor F * betaFactor * F + 17

theorem meanSamples_positive (n denom : ℕ) (hd : 0 < denom) : 0 < meanSamples n denom := by
  have h := betaDenom_pos n
  unfold meanSamples
  positivity

theorem meanSamples_exact (n denom : ℕ) (hd : 0 < denom) :
    beta n * ((meanSamples n denom : ℝ) * (1 / (denom : ℝ)) ^ 2) = 256 := by
  have hb : (betaDenom n : ℝ) ≠ 0 := by exact_mod_cast (betaDenom_pos n).ne'
  have hdn : (denom : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [beta_eq]
  unfold meanSamples
  push_cast
  field_simp

theorem meanSamples_is_ceiling (n denom : ℕ) (hd : 0 < denom) :
    meanSamples n denom = MSTApproximation.scoreSamples (beta n) (1 / (denom : ℝ)) := by
  have hp : (0 : ℝ) < beta n * (1 / (denom : ℝ)) ^ 2 := by
    have hb := (beta_bounds n).1
    positivity
  have h := meanSamples_exact n denom hd
  have he : 256 / (beta n * (1 / (denom : ℝ)) ^ 2) = (meanSamples n denom : ℝ) :=
    (div_eq_iff hp.ne').mpr (by nlinarith)
  unfold MSTApproximation.scoreSamples
  rw [he]
  simp

theorem samplerCap_test (n k denom : ℕ) (hk : 0 < k) (hd : 0 < denom) :
    Real.exp (-(samplerCap n k denom : ℝ) / k) ≤
      beta n * (1 / (denom : ℝ)) / (16 * meanSamples n denom) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hD : (0 : ℝ) < betaDenom n := by exact_mod_cast betaDenom_pos n
  have hdR : (0 : ℝ) < denom := by exact_mod_cast hd
  have hs : (0 : ℝ) < meanSamples n denom := by exact_mod_cast meanSamples_positive n denom hd
  have he : -(samplerCap n k denom : ℝ) / k = -(proposalClock n denom : ℝ) := by
    unfold samplerCap
    push_cast
    field_simp
  rw [he]
  apply (MSTApproximation.exp_neg_nat_le_two_pow_inv _).trans
  have hnat : 16 * meanSamples n denom * betaDenom n * denom + 1 < 2 ^ proposalClock n denom :=
    Nat.lt_log2_self
  have hreal : 16 * (meanSamples n denom : ℝ) * betaDenom n * denom ≤ (2 : ℝ) ^ proposalClock n denom := by
    exact_mod_cast (show 16 * meanSamples n denom * betaDenom n * denom ≤
      2 ^ proposalClock n denom by omega)
  have hp := inv_anti₀ (show (0 : ℝ) < 16 * meanSamples n denom * betaDenom n * denom by positivity) hreal
  calc
    ((2 : ℝ) ^ proposalClock n denom)⁻¹ ≤
        (16 * (meanSamples n denom : ℝ) * betaDenom n * denom)⁻¹ := hp
    _ = _ := by rw [beta_eq]; field_simp <;> ring

theorem meanSamples_polylog (n denom F : ℕ) (hden : denom ≤ F * ell n ^ 3) :
    meanSamples n denom ≤ meanFactor F * ell n ^ 9 := by
  have hD := betaDenom_polylog n
  have hd := Nat.pow_le_pow_left hden 2
  have hm := Nat.mul_le_mul hD hd
  unfold meanSamples meanFactor
  nlinarith [Nat.mul_le_mul_left 256 hm]

theorem proposalClock_polylog (n denom F : ℕ) (hden : denom ≤ F * ell n ^ 3) :
    proposalClock n denom ≤ proposalFactor F * ell n := by
  have hs := meanSamples_polylog n denom F hden
  have hb := betaDenom_polylog n
  have hh := Nat.mul_le_mul (Nat.mul_le_mul hs hb) hden
  have h1 : 1 ≤ ell n ^ 15 := by
    have h : 0 < ell n ^ 15 := by positivity [ell_pos n]
    exact h
  have hpolylog : 16 * meanSamples n denom * betaDenom n * denom + 1 ≤
      (16 * meanFactor F * betaFactor * F + 1) * ell n ^ 15 := by nlinarith
  have hp := hpolylog.trans (polylog_to_polynomial n (16 * meanFactor F * betaFactor * F + 1) 15)
  exact log_of_polynomial_bound n _ (16 * meanFactor F * betaFactor * F + 1) 15 hp

theorem samplerCap_polylog (n k denom F : ℕ) (hden : denom ≤ F * ell n ^ 3) :
    samplerCap n k denom ≤ proposalFactor F * k * ell n := by
  have h := Nat.mul_le_mul_left k (proposalClock_polylog n denom F hden)
  unfold samplerCap
  nlinarith

theorem concrete_sampling_polylog (n : ℕ) :
    meanSamples n (xiSavingInv n) ≤ meanFactor (100000000000 * aFactor) * ell n ^ 9 ∧
      meanSamples n (xiBandInv n) ≤ meanFactor (100000000 * aFactor) * ell n ^ 9 ∧
      meanSamples n (xiMInv n) ≤ meanFactor (1000000000000000 * amFactor) * ell n ^ 9 := by
  have h := score_budget_polylog n
  exact ⟨meanSamples_polylog _ _ _ h.2.2.1, meanSamples_polylog _ _ _ h.2.2.2.1,
    meanSamples_polylog _ _ _ h.2.2.2.2⟩

end SteinerUpperBound.EstimatorParameters
