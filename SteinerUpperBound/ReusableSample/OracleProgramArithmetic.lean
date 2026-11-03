module

public import SteinerUpperBound.ReusableSample.OracleProgramCore

@[expose] public section

namespace SteinerUpperBound.ReusableSample.OracleProgram

open SteinerLowerBound
open SteinerUpperBound.QueryProgram
open scoped BigOperators Classical

variable {M Q : Type*}

/-- Actual halving recursion. Arithmetic is performed in the charged scalar
blocks, not by calling the specification's exponentiation in a pure leaf. -/
def power (z : ℚ) (n : ℕ) : Code M Q ℚ :=
  .tick 3 (if _hn : n = 0 then .pure 1
    else (power z (n / 2)).bind fun v =>
      .tick 3 (.pure (if n % 2 = 0 then v * v else v * v * z)))
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero _hn) (by decide)

theorem power_good (m : M → ℝ) (b : Q → Bool) (z : ℚ) (n : ℕ) :
    Sure m b (power z n) (Good (· = z ^ n) (8 * (Nat.log2 n + 1) + 4) 0) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        rw [power]
        simp only [↓reduceDIte, pow_zero]
        exact good_mono m b _ (good_tick m b _ _ 0 0 3 (good_pure m b 1))
          (by simp) (fun _ h => h)
      · let W := if n / 2 = 0 then 4 else 8 * (Nat.log2 (n / 2) + 1) + 4
        have hr : Sure m b (power z (n / 2))
            (Good (· = z ^ (n / 2)) W 0) := by
          by_cases hh : n / 2 = 0
          · simp only [hh, W, ↓reduceIte, pow_zero]
            rw [power]
            exact good_tick m b _ _ 0 0 3 (good_pure m b 1)
          · simpa only [W, hh, ↓reduceIte] using
              ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))
        have he : (if n % 2 = 0 then z ^ (n / 2) * z ^ (n / 2)
            else z ^ (n / 2) * z ^ (n / 2) * z) = z ^ n := by
          by_cases hp : n % 2 = 0
          · rw [ite_eq_left hp, ← pow_add]
            congr 1
            omega
          · rw [ite_eq_right hp, ← pow_add, ← pow_succ]
            congr 1
            omega
        let k : ℚ → Code M Q ℚ := fun v =>
          .tick 3 (.pure (if n % 2 = 0 then v * v else v * v * z))
        have hk : Sure m b (k (z ^ (n / 2))) (Good (· = z ^ n) 4 0) := by
          dsimp [k]
          rw [he]
          exact good_tick m b _ _ 0 0 3 (good_pure m b _)
        have hs := good_tick m b _ _ _ _ 3
          (good_bind_value m b (power z (n / 2)) k _ (· = z ^ n) W 0 4 0 hr hk)
        rw [power]
        simp only [hn, ↓reduceDIte]
        apply good_mono m b _ hs
        · by_cases hh : n / 2 = 0
          · have h1 : n = 1 := by omega
            subst n
            simp [W]
          · have hl : Nat.log2 n = Nat.log2 (n / 2) + 1 := by
              simpa only [Nat.shiftRight_one, Nat.succ_eq_add_one] using
                Nat.log2_eq_succ_log2_shiftRight (by simpa only [Nat.shiftRight_one] using hh)
            simp only [W, hh, ↓reduceIte, hl]
            omega
        · exact fun _ h => h

/-- Base, signed exponent, reciprocal, and final division are constant-size
charged blocks. `power` performs all nonconstant arithmetic work. -/
def probability (Lbar Ns t c : ℕ) : Code M Q ℚ :=
  .tick 7 ((power (rationalBase Lbar) (integerExponent Ns t c).natAbs).bind fun v =>
    .tick 5 (.pure (1 / (1 + if 0 ≤ integerExponent Ns t c then v else v⁻¹))))

theorem probability_good (m : M → ℝ) (b : Q → Bool) (Lbar Ns t c : ℕ) (hc : c ≤ Ns) :
    Sure m b (probability Lbar Ns t c)
      (Good (· = fastProbability Lbar Ns t c) (8 * Nat.log2 (Ns + 1) + 34) 0) := by
  have he := integerExponent_natAbs_le Ns t c hc
  have hm : Nat.log2 (integerExponent Ns t c).natAbs ≤ Nat.log2 (Ns + 1) + 1 := by
    have hh : Nat.log2 (integerExponent Ns t c).natAbs ≤ Nat.log2 (2 * (Ns + 1)) := by
      simp only [Nat.log2_eq_log_two]
      exact Nat.log_mono_right (by omega)
    rw [Nat.log2_two_mul (Nat.succ_ne_zero Ns)] at hh
    simpa only [Nat.succ_eq_add_one] using hh
  have hp := good_mono m b _
    (power_good m b (rationalBase Lbar) (integerExponent Ns t c).natAbs)
    (show 8 * (Nat.log2 (integerExponent Ns t c).natAbs + 1) + 4 ≤
      8 * Nat.log2 (Ns + 1) + 20 by omega) (fun _ h => h)
  let k : ℚ → Code M Q ℚ := fun v =>
    .tick 5 (.pure (1 / (1 + if 0 ≤ integerExponent Ns t c then v else v⁻¹)))
  have hv : (1 / (1 + if 0 ≤ integerExponent Ns t c then
      rationalBase Lbar ^ (integerExponent Ns t c).natAbs
      else (rationalBase Lbar ^ (integerExponent Ns t c).natAbs)⁻¹)) =
      fastProbability Lbar Ns t c := by
    simp only [fastProbability, binaryZPower, binaryPower_value]
  have hk : Sure m b (k (rationalBase Lbar ^ (integerExponent Ns t c).natAbs))
      (Good (· = fastProbability Lbar Ns t c) 6 0) := by
    dsimp [k]
    rw [hv]
    exact good_tick m b _ _ 0 0 5 (good_pure m b _)
  exact good_mono m b _
    (good_tick m b _ _ _ _ 7
      (good_bind_value m b _ k _ _ (8 * Nat.log2 (Ns + 1) + 20) 0 6 0 hp hk))
    (by omega) (fun _ h => h)

/-- Clipping is only a totality guard. The checked probability computation
always produces a value in `[0,1]`, so the guard never changes a transition. -/
noncomputable def coinRate (p : ℚ) : Rate :=
  ⟨((max 0 (min 1 p) : ℚ) : ℝ),
    (by exact_mod_cast (le_max_left (0 : ℚ) (min 1 p))),
    (by exact_mod_cast (max_le (by norm_num : (0 : ℚ) ≤ 1) (min_le_left (1 : ℚ) p)))⟩

theorem coinRate_fastProbability (Lbar Ns t c : ℕ) :
    coinRate (fastProbability Lbar Ns t c) = rationalRate Lbar Ns t c := by
  apply Subtype.ext
  have h₀ := (rationalProbability_pos Lbar Ns t c).le
  have h₁ := rationalProbability_le_one Lbar Ns t c
  simp only [coinRate, fastProbability_eq, min_eq_right h₁, max_eq_right h₀, rationalRate]

end SteinerUpperBound.ReusableSample.OracleProgram
