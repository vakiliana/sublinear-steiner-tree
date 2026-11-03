module

public import SteinerUpperBound.SavingEstimator.Configuration

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.SavingEstimator

open EstimatorParameters

theorem cutoff_height (n : ℕ) : 100 * (heightBudget n + 1) ≤ B n := by
  have ht : 1 ≤ coverTrials n := Nat.succ_le_of_lt (coverTrials_pos n)
  have hh : 1 ≤ hopBudget n := ell_ge_one n
  have hm : heightBudget n ≤ heightBudget n * coverTrials n * hopBudget n := by
    calc
      _ = heightBudget n * 1 * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ ht) hh
  have hA : heightBudget n + 1 ≤ A n := by
    unfold A
    rw [show 60000000000 * heightBudget n * coverTrials n * hopBudget n =
      60000000000 * (heightBudget n * coverTrials n * hopBudget n) by ring]
    omega
  unfold B epsInv
  omega

theorem betaDenom_le_cube (n : ℕ) : betaDenom n ≤ B n ^ 3 := by
  unfold betaDenom
  calc
    _ = (100 * (heightBudget n + 1)) ^ 3 := by ring
    _ ≤ _ := Nat.pow_le_pow_left (cutoff_height n) 3

theorem inverse_eq_ten_cutoff (n : ℕ) : xiSavingInv n = 10 * B n := by
  unfold xiSavingInv B
  ring

theorem samples_power_bound (n : ℕ) : meanSamples n (xiSavingInv n) ≤ 25600 * B n ^ 5 := by
  unfold meanSamples
  rw [inverse_eq_ten_cutoff]
  calc
    _ ≤ 256 * (B n ^ 3) * (10 * B n) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (betaDenom_le_cube n))
    _ = _ := by ring

theorem rank_polynomial_budget (n : ℕ) :
    betaDenom n * meanSamples n (xiSavingInv n) ≤ B n ^ 30 := by
  have hB : 2 ≤ B n := by
    have hA := A_pos n
    unfold B epsInv
    omega
  have hsmall : betaDenom n * meanSamples n (xiSavingInv n) ≤ 25600 * B n ^ 8 := by
    calc
      _ ≤ B n ^ 3 * (25600 * B n ^ 5) :=
        Nat.mul_le_mul (betaDenom_le_cube n) (samples_power_bound n)
      _ = _ := by ring
  have hlarge : 25600 ≤ B n ^ 22 :=
    (by norm_num : (25600 : ℕ) ≤ 2 ^ 22).trans (Nat.pow_le_pow_left hB 22)
  calc
    _ ≤ 25600 * B n ^ 8 := hsmall
    _ ≤ B n ^ 22 * B n ^ 8 := Nat.mul_le_mul_right _ hlarge
    _ = _ := by rw [← pow_add]

theorem publicSize_ge_cutoff (n count : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ count) :
    B n ≤ PortGraph.RuntimeAdapter.publicSize n count 1 (B n) := by
  have hk' : B n ≤ B n * count := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (B n) hk
  have hn' : B n * count + 1 ≤ n * (B n * count + 1) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (B n * count + 1) hn
  unfold PortGraph.RuntimeAdapter.publicSize
  simp only [Nat.one_mul]
  omega

private theorem error_from_budget (D s N : ℕ) (hD : (0 : ℝ) < D) (hN : (0 : ℝ) < N)
    (h : D * s ≤ N ^ 30) :
    (s : ℝ) / (N : ℝ) ^ 30 ≤ 1 / (D : ℝ) := by
  have h' : s * D ≤ N ^ 30 := by simpa only [Nat.mul_comm] using h
  apply (div_le_div_iff₀ (pow_pos hN 30) hD).mpr
  simp only [one_mul]
  exact_mod_cast h'

theorem concrete_rank_error (n count : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ count) :
    (meanSamples n (xiSavingInv n) : ℝ) * LargeCoverProgram.concreteVOError n count (B n) ≤ beta n := by
  let N := PortGraph.RuntimeAdapter.publicSize n count 1 (B n)
  have hsize : B n ≤ N := publicSize_ge_cutoff n count hn hk
  have hN : (0 : ℝ) < N := by
    have hh := (integer_budget_pos n).2.1
    exact_mod_cast (lt_of_lt_of_le hh hsize)
  have hD : (0 : ℝ) < betaDenom n := by exact_mod_cast betaDenom_pos n
  have hp := (rank_polynomial_budget n).trans (Nat.pow_le_pow_left hsize 30)
  unfold LargeCoverProgram.concreteVOError
  rw [beta_eq, mul_one_div]
  exact error_from_budget _ _ _ hD hN hp

end SteinerUpperBound.SavingEstimator
