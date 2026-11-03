module

public import SteinerUpperBound.EstimatorParameters.Confidence
public import SteinerUpperBound.EstimatorParameters.Balance
public import SteinerUpperBound.ReusableSample.MembershipMatrix

@[expose] public section

namespace SteinerUpperBound.EstimatorParameters

open SteinerLowerBound
open scoped Classical

def noiseK1 (n : ℕ) : ℕ := Nat.log2 (512 * t n * betaDenom n) + 1
def noiseK2 (n : ℕ) : ℕ := Nat.log2 (128 * (n + 1) * t n * betaDenom n) + 1
def Lbar (n : ℕ) : ℕ := noiseK1 n + 1
def Mbar (n : ℕ) : ℕ := noiseK2 n + 1
def NsPool (n : ℕ) : ℕ := 512 * t n * Lbar n * Mbar n
def lFactor : ℕ := 512 * betaFactor + 6
def mFactor : ℕ := 128 * betaFactor + 7
def poolFactor : ℕ := 512 * lFactor * mFactor

theorem noise_doubling_nat (n : ℕ) :
    512 * t n * betaDenom n < 2 ^ noiseK1 n ∧
      128 * (n + 1) * t n * betaDenom n < 2 ^ noiseK2 n :=
  ⟨Nat.lt_log2_self, Nat.lt_log2_self⟩

theorem noise_doubling (n : ℕ) :
    512 * (t n : ℝ) ≤ beta n * (2 : ℝ) ^ noiseK1 n ∧
      128 * ((n : ℝ) + 1) * t n ≤ beta n * (2 : ℝ) ^ noiseK2 n := by
  have hd : (0 : ℝ) < betaDenom n := by exact_mod_cast betaDenom_pos n
  have h1 : 512 * (t n : ℝ) * betaDenom n ≤ (2 : ℝ) ^ noiseK1 n := by
    exact_mod_cast (noise_doubling_nat n).1.le
  have h2 : 128 * ((n : ℝ) + 1) * t n * betaDenom n ≤ (2 : ℝ) ^ noiseK2 n := by
    exact_mod_cast (noise_doubling_nat n).2.le
  rw [beta_eq, one_div_mul_eq_div, one_div_mul_eq_div]
  exact ⟨(le_div_iff₀ hd).mpr h1, (le_div_iff₀ hd).mpr h2⟩

theorem noise_polylog (n : ℕ) :
    Lbar n ≤ lFactor * ell n ∧ Mbar n ≤ mFactor * ell n := by
  have hd := (betaDenom_polylog n).trans (polylog_to_polynomial n betaFactor 3)
  have ht := (t_le n).trans (show n + 1 ≤ n + 2 by omega)
  have h1 : 512 * t n * betaDenom n ≤ (512 * betaFactor) * (n + 2) ^ 4 := by
    nlinarith [Nat.mul_le_mul ht hd]
  have h2 : 128 * (n + 1) * t n * betaDenom n ≤ (128 * betaFactor) * (n + 2) ^ 5 := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul (show n + 1 ≤ n + 2 by omega) ht) hd
    nlinarith
  have hk1 := log_of_polynomial_bound n _ (512 * betaFactor) 4 h1
  have hk2 := log_of_polynomial_bound n _ (128 * betaFactor) 5 h2
  have he := ell_ge_one n
  unfold Lbar Mbar noiseK1 noiseK2 lFactor mFactor
  constructor <;> nlinarith

theorem reusablePool_polylog (n : ℕ) :
    NsPool n ≤ poolFactor * t n * ell n ^ 2 := by
  obtain ⟨hl, hm⟩ := noise_polylog n
  have h := Nat.mul_le_mul_left (512 * t n) (Nat.mul_le_mul hl hm)
  unfold NsPool poolFactor
  nlinarith

theorem reusablePool_positive (n : ℕ) :
    0 < Lbar n ∧ 0 < Mbar n ∧ 0 < NsPool n ∧ t n ∣ NsPool n := by
  have ht := t_pos n
  have hl : 0 < Lbar n := by unfold Lbar; omega
  have hm : 0 < Mbar n := by unfold Mbar; omega
  refine ⟨hl, hm, by unfold NsPool; positivity, ?_⟩
  exact ⟨512 * Lbar n * Mbar n, by unfold NsPool; ring⟩

theorem reusable_sample_ready {U : Type*} [Fintype U] [Nonempty U] (n : ℕ) (rows : Fin n → Finset U) :
    1 - beta n ≤
      (ReusableSample.rationalRun (Lbar n) (NsPool n) (t n) rows).prob
        {T | ReusableSample.Specification rows (t n) T} ∧
    (∀ T, 0 < (ReusableSample.rationalRun (Lbar n) (NsPool n) (t n) rows).mass T →
      ReusableSample.acceptances T ≤ t n) ∧
    (∀ (X : Fin (NsPool n) → U) (T : Fin n → Bool),
      ReusableSample.queryWork rows (t n) X T ≤ n * NsPool n) := by
  have h := ReusableSample.integer_reusable_sample_rational_of_doubling rows (t n) (t_pos n)
    (beta n) (beta_bounds n).1 (beta_bounds n).2.2 (noiseK1 n) (noiseK2 n)
    (noise_doubling n).1 (noise_doubling n).2
  simpa only [Lbar, Mbar, NsPool, ReusableSample.integerSamples] using h

end SteinerUpperBound.EstimatorParameters
