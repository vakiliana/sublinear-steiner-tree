module

public import SteinerUpperBound.ReusableSample.Rational

@[expose] public section

namespace SteinerUpperBound.ReusableSample

open SteinerLowerBound
open scoped BigOperators Classical

/-- Repeated squaring with an arithmetic/comparison operation counter.
Six operations per nonzero iteration conservatively cover halving, parity,
branching, and the two possible multiplications. -/
def binaryPower (z : ℚ) (n : ℕ) : ℚ × ℕ :=
  if hn : n = 0 then (1, 0)
  else
    let v := binaryPower z (n / 2)
    if n % 2 = 0 then (v.1 * v.1, v.2 + 6)
    else (v.1 * v.1 * z, v.2 + 6)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

theorem binaryPower_value (z : ℚ) (n : ℕ) : (binaryPower z n).1 = z ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [binaryPower]
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, ↓reduceDIte]
        have hi := ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))
        by_cases hp : n % 2 = 0
        · simp only [hp, ↓reduceIte, hi]
          rw [← pow_add]
          congr 1
          omega
        · simp only [hp, ↓reduceIte, hi]
          rw [← pow_add, ← pow_succ]
          congr 1
          omega

theorem binaryPower_work (z : ℚ) (n : ℕ) :
    (binaryPower z n).2 ≤ 6 * (Nat.log2 n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · simp [binaryPower, hn]
      · have he : (binaryPower z n).2 = (binaryPower z (n / 2)).2 + 6 := by
          rw [binaryPower]
          simp only [hn, ↓reduceDIte]
          split_ifs <;> rfl
        rw [he]
        by_cases hh : n / 2 = 0
        · rw [hh]
          simp [binaryPower]
        · have hi := ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))
          have hl : Nat.log2 n = Nat.log2 (n / 2) + 1 := by
            simpa only [Nat.shiftRight_one, Nat.succ_eq_add_one] using
              Nat.log2_eq_succ_log2_shiftRight (by simpa only [Nat.shiftRight_one] using hh)
          rw [hl]
          omega

def binaryZPower (z : ℚ) (e : ℤ) : ℚ :=
  if 0 ≤ e then (binaryPower z e.natAbs).1 else (binaryPower z e.natAbs).1⁻¹

theorem binaryZPower_value (z : ℚ) (e : ℤ) : binaryZPower z e = z ^ e := by
  cases e with
  | ofNat n => simp [binaryZPower, binaryPower_value]
  | negSucc n => simp [binaryZPower, binaryPower_value, zpow_negSucc]

/-- Executable rational transition rule, with no real analytic operations. -/
def fastProbability (Lbar Ns t c : ℕ) : ℚ :=
  1 / (1 + binaryZPower (rationalBase Lbar) (integerExponent Ns t c))

theorem fastProbability_eq (Lbar Ns t c : ℕ) :
    fastProbability Lbar Ns t c = rationalProbability Lbar Ns t c := by
  simp only [fastProbability, rationalProbability, binaryZPower_value]

/-- Conservative operation count, including the base, signed exponent,
possible reciprocal, and final rational division. This is not a bit-cost bound. -/
def fastProbabilityWork (Lbar Ns t c : ℕ) : ℕ :=
  (binaryPower (rationalBase Lbar) (integerExponent Ns t c).natAbs).2 + 16

theorem fastProbabilityWork_le (Lbar Ns t c : ℕ) (hc : c ≤ Ns) :
    fastProbabilityWork Lbar Ns t c ≤ 6 * (Nat.log2 (Ns + 1) + 2) + 16 := by
  have hb := binaryPower_work (rationalBase Lbar) (integerExponent Ns t c).natAbs
  have he := integerExponent_natAbs_le Ns t c hc
  have hm : Nat.log2 (integerExponent Ns t c).natAbs ≤ Nat.log2 (2 * (Ns + 1)) := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.log_mono_right (by omega)
  rw [Nat.log2_two_mul (Nat.succ_ne_zero Ns)] at hm
  have hm' : Nat.log2 (integerExponent Ns t c).natAbs ≤ Nat.log2 (Ns + 1) + 1 := by
    simpa only [Nat.succ_eq_add_one] using hm
  dsimp [fastProbabilityWork]
  omega

theorem logistic_eq_fastProbability (Lbar Ns t c : ℕ) (hL : 0 < Lbar) (ht : 0 < t)
    (hdiv : t ∣ Ns) :
    (logistic (calibratedBandwidth Lbar) (2 * Ns / t) c : ℝ) =
      (fastProbability Lbar Ns t c : ℝ) := by
  rw [fastProbability_eq]
  exact logistic_eq_rationalProbability Lbar Ns t c hL ht hdiv

end SteinerUpperBound.ReusableSample
