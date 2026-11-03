module

public import SteinerUpperBound.EstimatorBudget

@[expose] public section

namespace SteinerUpperBound.EstimatorBudget

open EstimatorClocks

theorem factory_threshold_pos (count ordinary positive : ℕ) :
    (0 : ℝ) < (factory count ordinary positive).positiveThreshold := by
  have h : 0 < (factory count ordinary positive).positiveThreshold := by
    change 0 < amplification * (positive + 1)
    unfold amplification
    positivity
  exact_mod_cast h

theorem factory_threshold_ratio (count ordinary positive : ℕ) :
    (positive : ℝ) / (factory count ordinary positive).positiveThreshold ≤ 1 / 100000 := by
  have hd := factory_threshold_pos count ordinary positive
  apply (div_le_div_iff₀ hd (by norm_num : (0 : ℝ) < 100000)).mpr
  simp only [factory, amplification, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  nlinarith

theorem factory_real_cutoff_loss (count ordinary positive : ℕ) (hc : 0 < count) :
    (ordinary : ℝ) / ((factory count ordinary positive).clock.workBudget + 1 : ℕ) +
        (positive : ℝ) / (factory count ordinary positive).positiveThreshold +
        Real.exp ((factory count ordinary positive).positiveThreshold -
          ((factory count ordinary positive).clock.disclosureBudget : ℝ) / (2 * count)) ≤
      3 / 20000 := by
  have hw := (factory_ratios count ordinary positive).1
  simp only [mul_div_assoc] at hw
  have hn : 0 ≤ (ordinary : ℝ) / ((factory count ordinary positive).clock.workBudget + 1 : ℕ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hp := factory_threshold_ratio count ordinary positive
  have he := factory_exponential count ordinary positive hc
  linarith

end SteinerUpperBound.EstimatorBudget
