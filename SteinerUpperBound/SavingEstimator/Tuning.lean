module

public import SteinerUpperBound.SavingEstimator.Configuration

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.SavingEstimator

open SteinerLowerBound EstimatorParameters QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

theorem mean_sample_positive (n : ℕ) : 0 < meanSamples n (xiSavingInv n) :=
  meanSamples_positive n _ (integer_budget_pos n).2.2.2.1

theorem mean_sample_budget (n : ℕ) :
    beta n * ((meanSamples n (xiSavingInv n) : ℝ) * xiSaving n ^ 2) = 256 := by
  simpa only [xiSaving, xiSavingQ, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
    meanSamples_exact n (xiSavingInv n) (integer_budget_pos n).2.2.2.1

theorem reusable_budgets (n : ℕ) :
    ReusableSample.logBudget (t n) (beta n) ≤ Lbar n ∧
      ReusableSample.rowBudget n (t n) (beta n) ≤ Mbar n :=
  ⟨ReusableSample.logBudget_le_of_doubling _ (t_pos n) _ (beta_bounds n).1 _ (noise_doubling n).1,
    ReusableSample.rowBudget_le_of_doubling _ _ (t_pos n) _ (beta_bounds n).1 _ (noise_doubling n).2⟩

theorem calibration_exp (n count : ℕ) (hk : 0 < count) :
    Real.exp (-(samplerCap n count (xiSavingInv n) : ℝ) / count) ≤
      beta n * xiSaving n / (16 * meanSamples n (xiSavingInv n)) := by
  simpa only [xiSaving, xiSavingQ, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
    samplerCap_test n count (xiSavingInv n) hk (integer_budget_pos n).2.2.2.1

theorem calibration_exp_small (n count : ℕ) (hk : 0 < count) :
    Real.exp (-(samplerCap n count (xiSavingInv n) : ℝ) / count) ≤ xiSaving n / 8 := by
  have he := calibration_exp n count hk
  have hs : (1 : ℝ) ≤ meanSamples n (xiSavingInv n) := by exact_mod_cast mean_sample_positive n
  have hb : beta n ≤ 1 := (beta_bounds n).2.1.trans (by norm_num)
  have hx : 0 < xiSaving n := (score_ranges n).2.2.1
  have hscaled := (le_div_iff₀ (by positivity)).mp he
  have hprod := mul_le_mul_of_nonneg_right hb hx.le
  have hpos := (Real.exp_pos (-(samplerCap n count (xiSavingInv n) : ℝ) / count)).le
  nlinarith

theorem calibration_error (n count : ℕ) (hk : 0 < count) :
    (meanSamples n (xiSavingInv n) : ℝ) *
        Real.exp (-(samplerCap n count (xiSavingInv n) : ℝ) / count) +
      8 / (((xiSaving n : ℝ) / 4) ^ 2 * meanSamples n (xiSavingInv n)) ≤ (9 / 16 : ℝ) * beta n := by
  have hb : 0 < beta n := (beta_bounds n).1
  have hx : 0 < xiSaving n := (score_ranges n).2.2.1
  have hx1 : xiSaving n ≤ 1 := (score_ranges n).2.2.2.1
  have hs : (0 : ℝ) < meanSamples n (xiSavingInv n) := by exact_mod_cast mean_sample_positive n
  have hexp := calibration_exp n count hk
  have hscaled := (le_div_iff₀ (by positivity)).mp hexp
  have hprod := mul_le_mul_of_nonneg_left hx1 hb.le
  have hbudget := mean_sample_budget n
  have hcheb : 8 / ((xiSaving n / 4) ^ 2 * (meanSamples n (xiSavingInv n) : ℝ)) ≤ beta n / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  linarith

variable {U : Type*} [Fintype U] [Nonempty U]

theorem no_abort_capError (bits : U → Bool) (C s : ℕ) :
    Mean.capError bits C s (s * C) =
      (Covers.Rejection.poolLaw C s).prob {rows | ¬ Covers.Rejection.Successful bits C s rows} := by
  unfold Mean.capError
  have he : {rows | s * C < Covers.Rejection.proposals bits C s rows} = (∅ : Set (Fin s → Fin C → U)) := by
    ext rows
    constructor
    · intro h
      exact (not_lt_of_ge (Covers.Rejection.proposals_le bits C s rows)) h
    · intro h
      exact False.elim h
  rw [he]
  simp

theorem mean_cap_error (bits : U → Bool) (hb : (Covers.Rejection.retained bits).Nonempty)
    (n count : ℕ) (hk : 0 < count) (hcard : Fintype.card U = count) :
    Mean.capError bits (samplerCap n count (xiSavingInv n)) (meanSamples n (xiSavingInv n))
      (meanSamples n (xiSavingInv n) * samplerCap n count (xiSavingInv n)) ≤ beta n / 16 := by
  rw [no_abort_capError]
  have hsurvival :
      (1 - Covers.Rejection.hitRate bits) ^ samplerCap n count (xiSavingInv n) ≤
        beta n * xiSaving n / (16 * meanSamples n (xiSavingInv n)) := by
    rw [← Covers.Rejection.first_failure bits hb]
    have h := Covers.Rejection.first_failure_exp bits hb (samplerCap n count (xiSavingInv n))
    rw [hcard] at h
    exact h.trans (calibration_exp n count hk)
  have hs : (0 : ℝ) < meanSamples n (xiSavingInv n) := by exact_mod_cast mean_sample_positive n
  have hh := Covers.Rejection.pool_failure_le bits hb
    (samplerCap n count (xiSavingInv n)) (meanSamples n (xiSavingInv n))
  have hscaled := (le_div_iff₀ (by positivity)).mp hsurvival
  have hprod := mul_le_mul_of_nonneg_left (score_ranges n).2.2.2.1 (beta_bounds n).1.le
  linarith

theorem pool_exp (n count : ℕ) (hk : 0 < count) :
    Real.exp (-((count * poolClock n : ℕ) : ℝ) / count) ≤ beta n / (16 * NsPool n) := by
  have hcount : (0 : ℝ) < count := by exact_mod_cast hk
  have hpool : (0 : ℝ) < NsPool n := by exact_mod_cast (reusablePool_positive n).2.2.1
  have hD : (0 : ℝ) < betaDenom n := by exact_mod_cast betaDenom_pos n
  have he : -((count * poolClock n : ℕ) : ℝ) / count = -(poolClock n : ℝ) := by
    push_cast
    field_simp
  rw [he]
  apply (MSTApproximation.exp_neg_nat_le_two_pow_inv _).trans
  have hnat : 16 * NsPool n * betaDenom n + 1 < 2 ^ poolClock n := Nat.lt_log2_self
  have hreal : 16 * (NsPool n : ℝ) * betaDenom n ≤ (2 : ℝ) ^ poolClock n := by
    exact_mod_cast (show 16 * NsPool n * betaDenom n ≤ 2 ^ poolClock n by omega)
  have hi := inv_anti₀ (by positivity : 0 < 16 * (NsPool n : ℝ) * betaDenom n) hreal
  apply hi.trans_eq
  rw [beta_eq]
  field_simp

theorem pool_cap_error (bits : U → Bool) (hb : (Covers.Rejection.retained bits).Nonempty)
    (n count : ℕ) (hk : 0 < count) (hcard : Fintype.card U = count) :
    Mean.capError bits (count * poolClock n) (NsPool n) (NsPool n * (count * poolClock n)) ≤
      beta n / 16 := by
  rw [no_abort_capError]
  have hsurvival : (1 - Covers.Rejection.hitRate bits) ^ (count * poolClock n) ≤
      beta n / (16 * NsPool n) := by
    rw [← Covers.Rejection.first_failure bits hb]
    have h := Covers.Rejection.first_failure_exp bits hb (count * poolClock n)
    rw [hcard] at h
    exact h.trans (pool_exp n count hk)
  have hs : (0 : ℝ) < NsPool n := by exact_mod_cast (reusablePool_positive n).2.2.1
  have hh := Covers.Rejection.pool_failure_le bits hb (count * poolClock n) (NsPool n)
  have hscaled := (le_div_iff₀ (by positivity)).mp hsurvival
  linarith

end SteinerUpperBound.SavingEstimator
