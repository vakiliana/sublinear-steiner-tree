module

public import SteinerUpperBound.SavingEstimator.Resources.Polynomial

@[expose] public section

set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

namespace SteinerUpperBound.SavingEstimator.Resources

open EstimatorParameters
open PortGraph.RuntimeAdapter.Averaged
open scoped Classical

theorem samples_mul_monomial (kind : CounterKind) (n C a d : ℕ) :
    meanSamples n (xiSavingInv n) * monomial kind n C a d ≤
      monomial kind n C (a + 1) (d + 9) := by
  have hh := Nat.mul_le_mul_right (monomial kind n C a d) (samples_bound n)
  calc
    _ ≤ _ := hh
    _ = _ := by unfold monomial; simp only [pow_add, pow_one]; ring

theorem lazy_mul_monomial (kind : CounterKind) (n C a d : ℕ) :
    lazyFactor n * monomial kind n C a d ≤
      monomial kind n (2 ^ 160 * C) (a + 9) (d + 9) := by
  have hh := Nat.mul_le_mul_right (monomial kind n C a d) (lazyFactor_bound n)
  calc
    _ ≤ _ := hh
    _ = _ := by unfold monomial; simp only [pow_add]; ring

theorem proposal_bound (n k : ℕ) (hk : k + 1 ≤ n) :
    meanSamples n (xiSavingInv n) * samplerCap n (k + 1) (xiSavingInv n) ≤
      monomial .ordinary n 1 2 10 := by
  have hc : samplerCap n (k + 1) (xiSavingInv n) ≤ magnitude * (n + 1) * ell n := by
    have hh := (all_sampler_caps n (k + 1)).1
    exact hh.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul magnitude_bounds.2.1 (by omega)))
  have hh := Nat.mul_le_mul (samples_bound n) hc
  have ht := Nat.le_mul_of_pos_right
    ((magnitude * ell n ^ 9) * (magnitude * (n + 1) * ell n)) (t_pos n)
  calc
    _ ≤ (magnitude * ell n ^ 9) * (magnitude * (n + 1) * ell n) := hh
    _ ≤ ((magnitude * ell n ^ 9) * (magnitude * (n + 1) * ell n)) * t n := ht
    _ = _ := by unfold monomial space; ring

theorem calibrationBase_bound (kind : CounterKind) (n k : ℕ) (hk : k + 1 ≤ n) :
    samplerBudget kind (closed n (k + 1)).calibrationProposals
      (closed n (k + 1)).calibrationSamples ≤ monomial kind n (2 ^ 6) 2 10 := by
  cases kind
  · have hp := proposal_bound n k hk
    have hs := (core_le_monomial .ordinary n _ (samples_bound n)).trans
      (monomial_mono .ordinary n 1 1 1 2 9 10 (le_refl _) (by omega) (by omega))
    have h1 := (unit_le_monomial .ordinary n).trans
      (monomial_mono .ordinary n 1 1 0 2 0 10 (le_refl _) (by omega) (by omega))
    change 16 * (meanSamples n (xiSavingInv n) * samplerCap n (k + 1) (xiSavingInv n) +
      meanSamples n (xiSavingInv n) + 1) ≤ _
    have hh := Nat.mul_le_mul_left 16 (Nat.add_le_add (Nat.add_le_add hp hs) h1)
    have hsum : 16 * (monomial .ordinary n 1 2 10 + monomial .ordinary n 1 2 10 +
        monomial .ordinary n 1 2 10) ≤ 64 * monomial .ordinary n 1 2 10 := by omega
    exact (hh.trans hsum).trans_eq (by unfold monomial; norm_num; ring)
  · exact (core_le_monomial .positive n _ (samples_bound n)).trans
      (monomial_mono .positive n 1 (2 ^ 6) 1 2 9 10 (by norm_num) (by omega) (by omega))

theorem meanBase_bound (kind : CounterKind) (n k : ℕ) (hk : k + 1 ≤ n) :
    meanBase kind n k ≤ monomial kind n (2 ^ 8) 2 10 := by
  have hbase :
      meanBase kind n k ≤
        4 * samplerBudget kind (closed n (k + 1)).calibrationProposals
          (closed n (k + 1)).calibrationSamples := by
    cases kind <;> dsimp only [meanBase, samplerBudget, closed] <;> omega
  have hh := hbase.trans (Nat.mul_le_mul_left 4 (calibrationBase_bound kind n k hk))
  convert hh using 1 <;> norm_num only [monomial] <;> ring

private theorem setup_value_bound (kind : CounterKind) (n value : ℕ)
    (hw : value ≤ magnitude * ell n) :
    (value + 12) * workUnit kind ≤ monomial kind n 16 1 1 := by
  cases kind
  · simp only [workUnit, Nat.mul_one]
    have hunit : 1 ≤ magnitude * ell n := Nat.mul_le_mul magnitude_one (ell_ge_one n)
    have hsp : 1 ≤ (n + 1) * t n :=
      Nat.mul_le_mul (show 1 ≤ n + 1 by omega) (Nat.succ_le_of_lt (t_pos n))
    calc
      _ ≤ 16 * magnitude * ell n := by nlinarith only [hw, hunit]
      _ ≤ (16 * magnitude * ell n) * ((n + 1) * t n) := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (16 * magnitude * ell n) hsp
      _ = _ := by unfold monomial space; ring
  · simp only [workUnit, Nat.mul_zero]
    exact Nat.zero_le _

theorem setup_bound (kind : CounterKind) (n k : ℕ) :
    (configurationWork n (k + 1) (parameters n (k + 1)) + 12) * workUnit kind ≤
      monomial kind n 16 1 1 :=
  setup_value_bound kind n _
    ((configuration_work_polylog n (k + 1)).trans (Nat.mul_le_mul_right _ magnitude_bounds.2.2.1))

theorem pool_bound (n : ℕ) : NsPool n ≤ magnitude * t n * ell n ^ 2 :=
  (pool_public_bound n).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ magnitude_bounds.2.1))

theorem poolClock_bound (n : ℕ) : poolClock n ≤ magnitude * ell n := by
  have hh := log_of_polynomial_bound n (16 * NsPool n * betaDenom n + 1)
    (16 * poolFactor * betaFactor + 1) 6 (pool_argument_bound n)
  have hp : poolClock n ≤ poolLogFactor * ell n := by
    convert hh using 1 <;> dsimp only [poolClock, poolLogFactor] <;> ring
  exact hp.trans (Nat.mul_le_mul_right _ magnitude_bounds.2.2.2.1)

theorem poolCount_log_bound (n : ℕ) : Nat.log2 (NsPool n + 1) + 1 ≤ 2 * magnitude * ell n := by
  have ht : t n ≤ n + 2 := (t_le n).trans (by omega)
  have hp : NsPool n ≤ magnitude * (n + 2) ^ 3 := by
    have hh := Nat.mul_le_mul (Nat.mul_le_mul_left magnitude ht)
      (Nat.pow_le_pow_left (ell_le n) 2)
    exact (pool_bound n).trans (by convert hh using 1 <;> ring)
  have h1 : 1 ≤ (n + 2) ^ 3 := one_le_pow₀ (by omega)
  have harg : NsPool n + 1 ≤ (magnitude + 1) * (n + 2) ^ 3 := by nlinarith only [hp, h1]
  have hh := log_of_polynomial_bound n (NsPool n + 1) (magnitude + 1) 3 harg
  have hc : magnitude + 1 + 3 + 1 ≤ 2 * magnitude := by have := magnitude_bounds.1; omega
  exact hh.trans (Nat.mul_le_mul_right _ hc)

theorem smallCount_log_bound (n count : ℕ) :
    Nat.log2 (LargeCoverProgram.smallLimit (closed n count) + 1) + 1 ≤ 11 * magnitude * ell n := by
  rw [smallLimit_eq]
  have hb : B n ≤ magnitude * (n + 2) ^ 9 :=
    (cutoff_bound n).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (ell_le n) 9))
  have ht : t n ≤ n + 2 := (t_le n).trans (by omega)
  have hm := Nat.mul_le_mul hb ht
  have hp : 10 * B n * t n ≤ 10 * magnitude * (n + 2) ^ 10 := by nlinarith only [hm]
  have h1 : 1 ≤ (n + 2) ^ 10 := one_le_pow₀ (by omega)
  have harg : 10 * B n * t n + 1 ≤ (10 * magnitude + 1) * (n + 2) ^ 10 := by
    nlinarith only [hp, h1]
  have hh := log_of_polynomial_bound n (10 * B n * t n + 1) (10 * magnitude + 1) 10 harg
  have hc : 10 * magnitude + 1 + 10 + 1 ≤ 11 * magnitude := by have := magnitude_bounds.1; omega
  exact hh.trans (Nat.mul_le_mul_right _ hc)

end SteinerUpperBound.SavingEstimator.Resources
