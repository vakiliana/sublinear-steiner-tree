module

public import SteinerUpperBound.ReusableSample.Parameters

@[expose] public section

namespace SteinerUpperBound.ReusableSample

open SteinerLowerBound
open scoped BigOperators Classical

/-- All data in the transition rule are rational numbers and integers. -/
def rationalBase (Lbar : ℕ) : ℚ := 1 + 1 / (64 * (Lbar : ℚ))

def integerExponent (Ns t c : ℕ) : ℤ := 2 * ((Ns / t : ℕ) : ℤ) - (c : ℤ)

def rationalProbability (Lbar Ns t c : ℕ) : ℚ :=
  1 / (1 + rationalBase Lbar ^ integerExponent Ns t c)

theorem rationalBase_pos (Lbar : ℕ) : 0 < rationalBase Lbar := by
  dsimp [rationalBase]
  positivity

theorem rationalProbability_pos (Lbar Ns t c : ℕ) :
    0 < rationalProbability Lbar Ns t c := by
  dsimp [rationalProbability]
  exact one_div_pos.mpr (by linarith [zpow_pos (rationalBase_pos Lbar) (integerExponent Ns t c)])

theorem rationalProbability_le_one (Lbar Ns t c : ℕ) :
    rationalProbability Lbar Ns t c ≤ 1 := by
  have hz := zpow_pos (rationalBase_pos Lbar) (integerExponent Ns t c)
  apply (div_le_one (by linarith : 0 < 1 + rationalBase Lbar ^ integerExponent Ns t c)).mpr
  linarith

noncomputable def rationalRate (Lbar Ns t c : ℕ) : Rate :=
  ⟨(rationalProbability Lbar Ns t c : ℝ),
    (by exact_mod_cast (rationalProbability_pos Lbar Ns t c).le),
    (by exact_mod_cast rationalProbability_le_one Lbar Ns t c)⟩

/-- The threshold is an integer when the sample size is a multiple of `t`.
The exponent is signed: counts above the threshold use negative powers. -/
theorem logistic_integer_rule (Lbar Ns t c : ℕ) (hL : 0 < Lbar) (ht : 0 < t)
    (hdiv : t ∣ Ns) :
    (logistic (calibratedBandwidth Lbar) (2 * Ns / t) c : ℝ) =
      1 / (1 + (1 + 1 / (64 * (Lbar : ℝ))) ^ integerExponent Ns t c) := by
  have hz : 0 < 1 + 1 / (64 * (Lbar : ℝ)) := by positivity
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have hd : (Ns : ℝ) / t = ((Ns / t : ℕ) : ℝ) := by
    apply (div_eq_iff ht').mpr
    exact_mod_cast (Nat.div_mul_cancel hdiv).symm
  have hh : 2 * (Ns : ℝ) / t = 2 * ((Ns / t : ℕ) : ℝ) := by
    rw [mul_div_assoc, hd]
  have he : Real.exp ((2 * (Ns : ℝ) / t - c) / calibratedBandwidth Lbar) =
      (1 + 1 / (64 * (Lbar : ℝ))) ^ integerExponent Ns t c := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos hz]
    congr 1
    rw [hh]
    simp only [calibratedBandwidth, integerExponent, Int.cast_sub, Int.cast_mul,
      Int.cast_ofNat, Int.cast_natCast, div_eq_mul_inv, one_mul, inv_inv]
    ring
  change 1 / (1 + Real.exp ((2 * (Ns : ℝ) / t - c) / calibratedBandwidth Lbar)) = _
  rw [he]

theorem logistic_eq_rationalProbability (Lbar Ns t c : ℕ) (hL : 0 < Lbar) (ht : 0 < t)
    (hdiv : t ∣ Ns) :
    (logistic (calibratedBandwidth Lbar) (2 * Ns / t) c : ℝ) =
      (rationalProbability Lbar Ns t c : ℝ) := by
  rw [logistic_integer_rule Lbar Ns t c hL ht hdiv]
  simp only [rationalProbability, rationalBase, Rat.cast_div, Rat.cast_add, Rat.cast_one,
    Rat.cast_zpow, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]

theorem logistic_eq_rationalRate (Lbar Ns t c : ℕ) (hL : 0 < Lbar) (ht : 0 < t)
    (hdiv : t ∣ Ns) :
    logistic (calibratedBandwidth Lbar) (2 * Ns / t) c = rationalRate Lbar Ns t c := by
  apply Subtype.ext
  exact logistic_eq_rationalProbability Lbar Ns t c hL ht hdiv

theorem integerExponent_natAbs_le (Ns t c : ℕ) (hc : c ≤ Ns) :
    (integerExponent Ns t c).natAbs ≤ 2 * Ns := by
  have hd := Nat.div_le_self Ns t
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  apply abs_le.mpr
  dsimp [integerExponent]
  have hd' : ((Ns / t : ℕ) : ℤ) ≤ (Ns : ℤ) := by exact_mod_cast hd
  have hd₀ : (0 : ℤ) ≤ ((Ns / t : ℕ) : ℤ) := Int.natCast_nonneg _
  omega

end SteinerUpperBound.ReusableSample
