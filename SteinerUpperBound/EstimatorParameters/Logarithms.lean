module

public import SteinerUpperBound.EstimatorParameters.Fixed
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace SteinerUpperBound.EstimatorParameters

def ell (n : ℕ) : ℕ := 1 + Nat.log2 (n + 2)

theorem ell_pos (n : ℕ) : 0 < ell n := by unfold ell; omega
theorem ell_ge_one (n : ℕ) : 1 ≤ ell n := ell_pos n

theorem log2_mono {a b : ℕ} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  simp only [Nat.log2_eq_log_two]
  exact Nat.log_mono_right h

theorem ell_mono {a b : ℕ} (h : a ≤ b) : ell a ≤ ell b := by
  exact Nat.add_le_add_left (log2_mono (Nat.add_le_add_right h 2)) 1

theorem ell_le (n : ℕ) : ell n ≤ n + 2 := by
  have h : Nat.log2 (n + 2) < n + 2 :=
    (Nat.log2_lt (by omega : n + 2 ≠ 0)).mpr Nat.lt_two_pow_self
  unfold ell
  omega

theorem below_doubling (n : ℕ) : n + 2 < 2 ^ ell n := by
  simpa only [ell, Nat.add_comm] using (Nat.lt_log2_self (n := n + 2))

theorem log_of_polynomial_bound (n x C d : ℕ) (h : x ≤ C * (n + 2) ^ d) :
    Nat.log2 x + 1 ≤ (C + d + 1) * ell n := by
  by_cases hx : x = 0
  · subst x
    have he := ell_ge_one n
    have hc : 1 ≤ C + d + 1 := by omega
    simpa only [Nat.log2_zero, Nat.zero_add] using Nat.mul_le_mul hc he
  · have hpow : (n + 2) ^ d ≤ (2 ^ ell n) ^ d :=
      Nat.pow_le_pow_left (below_doubling n).le d
    have hc : C < 2 ^ C := Nat.lt_two_pow_self
    have hxpow : x < 2 ^ (C + ell n * d) := by
      calc
        x ≤ C * (n + 2) ^ d := h
        _ ≤ C * (2 ^ ell n) ^ d := Nat.mul_le_mul_left C hpow
        _ < (2 ^ C) * (2 ^ ell n) ^ d :=
          Nat.mul_lt_mul_of_pos_right hc (by positivity)
        _ = _ := by rw [← Nat.pow_mul, ← Nat.pow_add]
    have he : C + ell n * d ≤ (C + d + 1) * ell n := by
      nlinarith [ell_ge_one n, Nat.zero_le (C * (ell n - 1))]
    have hx' : x < 2 ^ ((C + d + 1) * ell n) :=
      hxpow.trans_le (Nat.pow_le_pow_right (by norm_num) he)
    have hl := (Nat.log2_lt hx).mpr hx'
    omega

theorem ell_power_le (n a b : ℕ) (hab : a ≤ b) : ell n ^ a ≤ ell n ^ b :=
  Nat.pow_le_pow_right (ell_pos n) hab

theorem polylog_to_polynomial (n C d : ℕ) :
    C * ell n ^ d ≤ C * (n + 2) ^ d :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (ell_le n) d)

end SteinerUpperBound.EstimatorParameters
