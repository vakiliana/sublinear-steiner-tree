module

public import SteinerUpperBound.EstimatorParameters.Logarithms

@[expose] public section

namespace SteinerUpperBound.EstimatorParameters

def t (n : ℕ) : ℕ := Nat.sqrt n + 1

theorem t_pos (n : ℕ) : 0 < t n := by unfold t; omega

theorem n_lt_t_sq (n : ℕ) : n < t n ^ 2 := by
  simpa only [t, pow_two, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt n

theorem t_le (n : ℕ) : t n ≤ n + 1 := by
  have h := Nat.sqrt_le n
  unfold t
  nlinarith

theorem t_sq_le (n : ℕ) : t n ^ 2 ≤ 2 * (n + 1) := by
  have hsN : Nat.sqrt n ^ 2 ≤ n := by simpa only [pow_two] using Nat.sqrt_le n
  have hs : (Nat.sqrt n : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hsN
  have h : ((t n : ℕ) : ℝ) ^ 2 ≤ 2 * ((n : ℝ) + 1) := by
    unfold t
    push_cast
    nlinarith [sq_nonneg ((Nat.sqrt n : ℝ) - 1)]
  exact_mod_cast h

theorem t_le_twice_natSqrt (n : ℕ) : t n ≤ 2 * Nat.sqrt (n + 1) := by
  have hm := Nat.sqrt_le_sqrt (show n ≤ n + 1 by omega)
  have hp : 0 < Nat.sqrt (n + 1) := by
    by_contra h
    have hh := Nat.sqrt_lt.mp (show Nat.sqrt (n + 1) < 1 by omega)
    omega
  unfold t
  omega

theorem t_le_twice_sqrt (n : ℕ) : (t n : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) + 1) := by
  have h : (t n : ℝ) ^ 2 ≤ 2 * ((n : ℝ) + 1) := by exact_mod_cast t_sq_le n
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n + 1 by positivity)
  have hp := Real.sqrt_nonneg ((n : ℝ) + 1)
  nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n,
    show (0 : ℝ) ≤ t n from Nat.cast_nonneg (t n)]

theorem balanced_integer_cost (n : ℕ) : n * t n + n ^ 2 / t n ≤ 2 * (n + 1) * t n := by
  have hn := (n_lt_t_sq n).le
  have hm : n ^ 2 ≤ t n * (n * t n) := by nlinarith [Nat.mul_le_mul_left n hn]
  have hd : n ^ 2 / t n ≤ n * t n := Nat.div_le_of_le_mul hm
  nlinarith

end SteinerUpperBound.EstimatorParameters
