module

public import SteinerUpperBound.Matching.Padded.Program

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

structure Arithmetic (A : Type*) where
  value : A
  operations : ℕ

namespace Arithmetic

def fastPow (a : ℚ) (n : ℕ) : Arithmetic ℚ :=
  if hn : n = 0 then ⟨1, 1⟩ else
    let r := fastPow a (n / 2)
    if n % 2 = 0 then ⟨r.value * r.value, r.operations + 8⟩
    else ⟨r.value * r.value * a, r.operations + 8⟩
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

theorem fastPow_value (a : ℚ) (n : ℕ) : (fastPow a n).value = a ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [fastPow]
    split_ifs with hn he
    · subst n
      simp
    · have hsmall := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1 < 2)
      have hv := ih (n / 2) hsmall
      have hrepr : n = n / 2 + n / 2 := by
        have hmod := Nat.div_add_mod n 2
        omega
      change (fastPow a (n / 2)).value * (fastPow a (n / 2)).value = _
      rw [hv, ← pow_add, ← hrepr]
    · have hsmall := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1 < 2)
      have hv := ih (n / 2) hsmall
      have hodd : n % 2 = 1 := (Nat.mod_two_eq_zero_or_one n).resolve_left he
      have hrepr : n = (n / 2 + n / 2) + 1 := by
        have hmod := Nat.div_add_mod n 2
        omega
      change (fastPow a (n / 2)).value * (fastPow a (n / 2)).value * a = _
      rw [hv, ← pow_add, ← pow_succ, ← hrepr]

theorem fastPow_operations (a : ℚ) (n : ℕ) :
    (fastPow a n).operations ≤ 16 * (Nat.log 2 n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp [fastPow]
    · by_cases hone : n = 1
      · subst n
        norm_num [fastPow]
      · have hsmall := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1 < 2)
        have hi := ih (n / 2) hsmall
        have hlog : 1 ≤ Nat.log 2 n :=
          (Nat.le_log_iff_pow_le (by decide) hn).mpr (by simpa using (by omega : 2 ≤ n))
        rw [Nat.log_div_base] at hi
        rw [fastPow]
        simp only [hn, ↓reduceDIte]
        split_ifs <;> dsimp only <;> omega

def run {A : Type*} (r : Arithmetic A) : Program ℕ A :=
  .tick r.operations (.ret r.value)

@[simp] theorem expect_run {A : Type*} (r : Arithmetic A) (f : A → ℝ) :
    r.run.expect f = f r.value := by simp [run]

@[simp] theorem cost_run {A : Type*} (r : Arithmetic A) :
    r.run.expectedCost (fun n => (n : ℝ)) 1 = r.operations := by simp [run]

end Arithmetic

namespace IntegerCoin

def sample (q : ℚ) : Program ℕ Bool :=
  .tick 3 (.draw q.den q.den_pos (fun i => .ret (decide (i.val < q.num.toNat))))

theorem threshold_card (b a : ℕ) (ha : a ≤ b) :
    (Finset.univ.filter fun i : Fin b => i.val < a).card = a := by
  classical
  by_cases hab : a < b
  · have heq : (Finset.univ.filter fun i : Fin b => i.val < a) =
        Finset.Iio (⟨a, hab⟩ : Fin b) := by
      ext i
      simp [Fin.lt_def]
    rw [heq, Fin.card_Iio]
  · have he : a = b := by omega
    subst a
    simp

theorem threshold_sum (b a : ℕ) (ha : a ≤ b) (x y : ℝ) :
    (∑ i : Fin b, if i.val < a then x else y) = (a : ℝ) * x + (b - a : ℕ) * y := by
  classical
  have hno : (Finset.univ.filter fun i : Fin b => ¬ i.val < a).card = b - a := by
    by_cases hab : a < b
    · have heq : (Finset.univ.filter fun i : Fin b => ¬ i.val < a) =
          Finset.Ici (⟨a, hab⟩ : Fin b) := by
        ext i
        simp [Fin.le_def]
      rw [heq, Fin.card_Ici]
    · have he : a = b := by omega
      subst a
      simp
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, threshold_card b a ha, hno]

theorem numerator_le_den (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : q.num.toNat ≤ q.den := by
  have hn : (0 : ℤ) ≤ q.num := Rat.num_nonneg.mpr h0
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hq : (q.num : ℚ) / q.den ≤ 1 := by rw [Rat.num_div_den]; exact h1
  have hh : (q.num : ℚ) ≤ q.den := (div_le_one hd).mp hq
  have hi : q.num ≤ (q.den : ℤ) := by exact_mod_cast hh
  have he : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg hn
  rw [← he] at hi
  exact_mod_cast hi

theorem rational_eq (q : ℚ) (h0 : 0 ≤ q) :
    ((q.num.toNat : ℕ) : ℝ) / q.den = q := by
  have hn := Rat.num_nonneg.mpr h0
  rw [Rat.cast_def]
  congr 1
  exact_mod_cast Int.toNat_of_nonneg hn

/-- A rational Bernoulli is realized by one integer draw and a comparison. -/
theorem expect_sample (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (f : Bool → ℝ) :
    (sample q).expect f = (q : ℝ) * f true + (1 - (q : ℝ)) * f false := by
  have hab := numerator_le_den q h0 h1
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  rw [sample, Program.expect_tick, Program.expect_draw]
  simp only [Program.expect_ret]
  have he (i : Fin q.den) :
      f (decide (i.val < q.num.toNat)) =
        if i.val < q.num.toNat then f true else f false := by
    by_cases h : i.val < q.num.toNat <;> simp [h]
  simp_rw [he]
  rw [← Finset.mul_sum, threshold_sum _ _ hab, Nat.cast_sub hab]
  have hq := rational_eq q h0
  rw [div_eq_mul_inv] at hq
  have hden : (q.den : ℝ) * (q.den : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hd)
  calc
    _ = ((q.num.toNat : ℝ) * (q.den : ℝ)⁻¹) * f true +
        ((q.den : ℝ) * (q.den : ℝ)⁻¹ -
          (q.num.toNat : ℝ) * (q.den : ℝ)⁻¹) * f false := by ring
    _ = _ := by rw [hq, hden]

theorem cost_sample (q : ℚ) (x : (sample q).Outcomes) :
    (sample q).cost (fun n : ℕ => (n : ℝ)) 1 x = 4 := by
  change (3 : ℝ) + (1 + 0) = 4
  norm_num

theorem expectedCost_sample (q : ℚ) :
    (sample q).expectedCost (fun n => (n : ℝ)) 1 = 4 := by
  change (sample q).law.expect (fun x => (sample q).cost (fun n : ℕ => (n : ℝ)) 1 x) = 4
  simp_rw [cost_sample]
  exact Law.expect_const _ _

end IntegerCoin

end SteinerUpperBound.Matching.Padded
