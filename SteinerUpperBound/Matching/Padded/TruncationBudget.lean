module

public import SteinerUpperBound.Matching.Padded.ClosedCost

@[expose] public section

set_option maxHeartbeats 2400000

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E]
    (P : Parameters S)

theorem Account.publicPrice_nonneg (A : Account S) : 0 ≤ Account.publicPrice S A := by
  have hC := A.Cstar_nonneg
  have hW : 0 ≤ ∑ v, A.W v := Finset.sum_nonneg fun v _ => A.W_nonneg v
  unfold Account.publicPrice
  positivity

theorem Account.Cstar_le_publicPrice (A : Account S) : A.Cstar ≤ Account.publicPrice S A := by
  have hC := A.Cstar_nonneg
  have hW : 0 ≤ (∑ v, A.W v) / Fintype.card V :=
    div_nonneg (Finset.sum_nonneg fun v _ => A.W_nonneg v) (Nat.cast_nonneg _)
  have hr : 0 ≤ (Fintype.card E : ℝ) / Fintype.card V := by positivity
  unfold Account.publicPrice
  nlinarith

theorem Account.publicPrice_le [Nonempty V] (A : Account S) :
    Account.publicPrice S A ≤ 4 * A.Cstar * P.Nstar := by
  have hm : (1 : ℝ) ≤ Fintype.card V := by
    exact_mod_cast (show 1 ≤ Fintype.card V from Fintype.card_pos)
  have hC := A.Cstar_nonneg
  have hp : (Fintype.card E : ℝ) ≤ P.Nstar := by
    exact_mod_cast Parameters.copies_le_Nstar S P
  have hr : (Fintype.card E : ℝ) / Fintype.card V ≤ P.Nstar :=
    (div_le_self (Nat.cast_nonneg _) hm).trans hp
  have hW : (∑ v, A.W v) / Fintype.card V ≤ A.Cstar * P.Nstar :=
    (div_le_self (Finset.sum_nonneg fun v _ => A.W_nonneg v) hm).trans
      (Parameters.W_sum_le S P A)
  have hN : (1 : ℝ) ≤ P.Nstar := by exact_mod_cast (show 1 ≤ P.Nstar by have := P.two_le; omega)
  have hrC := mul_le_mul_of_nonneg_left hr hC
  have hnC := mul_le_mul_of_nonneg_left hN hC
  unfold Account.publicPrice
  nlinarith

def Parameters.truncationExponent : ℕ := 100 + 20 * P.logarithm

def Parameters.truncationScale : ℝ := (2 : ℝ) ^ Parameters.truncationExponent S P

def Parameters.truncatedFactor : ℝ := (2 : ℝ) ^ 128 * (P.logarithm : ℝ) ^ 9

noncomputable def Account.truncationLimit (A : Account S) : ℝ :=
  A.Cstar * Parameters.truncationScale S P

theorem Parameters.truncationScale_bounds :
    (2 : ℝ) ^ 100 * (P.Nstar : ℝ) ^ 20 ≤ Parameters.truncationScale S P ∧
      Parameters.truncationScale S P ≤ (2 : ℝ) ^ 120 * (P.Nstar : ℝ) ^ 20 := by
  have hlower : (P.Nstar : ℝ) ≤ (2 : ℝ) ^ P.logarithm := by
    exact_mod_cast (Parameters.Nstar_lt_pow S P).le
  have hupper : (2 : ℝ) ^ P.logarithm ≤ 2 * P.Nstar := by
    have hn : P.Nstar ≠ 0 := by have := P.two_le; omega
    have hp : (2 : ℝ) ^ Nat.log 2 P.Nstar ≤ P.Nstar := by
      exact_mod_cast Nat.pow_log_le_self 2 hn
    unfold Parameters.logarithm
    rw [pow_succ]
    linarith
  have heq : Parameters.truncationScale S P =
      (2 : ℝ) ^ 100 * ((2 : ℝ) ^ P.logarithm) ^ 20 := by
    unfold Parameters.truncationScale Parameters.truncationExponent
    rw [pow_add, Nat.mul_comm 20 P.logarithm, pow_mul]
  rw [heq]
  constructor
  · gcongr
  · calc
      _ ≤ (2 : ℝ) ^ 100 * (2 * P.Nstar) ^ 20 := by gcongr
      _ = _ := by ring

theorem Parameters.costBudget_polynomial [Nonempty V] (A : Account S) :
    Parameters.costFactor S P * Account.publicPrice S A ≤
      (2 : ℝ) ^ 66 * A.Cstar * (P.Nstar : ℝ) ^ 9 := by
  have hh : (P.logarithm : ℝ) ≤ P.Nstar := by
    exact_mod_cast Parameters.logarithm_le_Nstar S P
  have hC := A.Cstar_nonneg
  have hp := mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh 8)
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 64))
    (Account.publicPrice_le S P A) (Account.publicPrice_nonneg S A) (by positivity)
  dsimp only [Parameters.costFactor]
  nlinarith

theorem Parameters.truncation_error_le [Nonempty V] (A : Account S) (hC : 0 < A.Cstar) :
    1 / (P.Nstar : ℝ) ^ 30 +
      Parameters.costFactor S P * Account.publicPrice S A / Account.truncationLimit S P A ≤
        1 / (P.Nstar : ℝ) ^ 3 := by
  let N : ℝ := P.Nstar
  have hN : (2 : ℝ) ≤ N := by dsimp only [N]; exact_mod_cast P.two_le
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hlimit : 0 < Account.truncationLimit S P A := by
    unfold Account.truncationLimit Parameters.truncationScale
    positivity
  have hN27 : (2 : ℝ) ≤ N ^ 27 :=
    (by norm_num : (2 : ℝ) ≤ 2 ^ 27).trans
      (pow_le_pow_left₀ (by norm_num) hN 27)
  have hsmall : (1 : ℝ) / N ^ 30 ≤ 1 / (2 * N ^ 3) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      _ ≤ N ^ 27 * N ^ 3 := by nlinarith [mul_le_mul_of_nonneg_right hN27 (by positivity : (0 : ℝ) ≤ N ^ 3)]
      _ = _ := by ring
  have hbudget :
      Parameters.costFactor S P * Account.publicPrice S A / Account.truncationLimit S P A ≤
        1 / (2 * N ^ 3) := by
    apply (div_le_div_iff₀ hlimit (by positivity)).mpr
    calc
      _ ≤ ((2 : ℝ) ^ 66 * A.Cstar * N ^ 9) * (2 * N ^ 3) :=
        mul_le_mul_of_nonneg_right (Parameters.costBudget_polynomial S P A) (by positivity)
      _ = (2 : ℝ) ^ 67 * A.Cstar * N ^ 12 := by ring
      _ ≤ (2 : ℝ) ^ 100 * A.Cstar * N ^ 20 := by
        have hn := pow_le_pow_right₀ hN1 (by decide : 12 ≤ 20)
        have hc : (2 : ℝ) ^ 67 * A.Cstar ≤ (2 : ℝ) ^ 100 * A.Cstar :=
          mul_le_mul_of_nonneg_right (by norm_num) hC.le
        exact mul_le_mul hc hn (by positivity) (by positivity)
      _ ≤ _ := by
        have hl := mul_le_mul_of_nonneg_left (Parameters.truncationScale_bounds S P).1 hC.le
        dsimp only [Account.truncationLimit]
        nlinarith
  have heq : (1 : ℝ) / (2 * N ^ 3) + 1 / (2 * N ^ 3) = 1 / N ^ 3 := by
    field_simp
    <;> ring
  exact (add_le_add hsmall hbudget).trans heq.le

theorem Parameters.truncated_budget_le (A : Account S) :
    A.Cstar + 2 * (1 / (P.Nstar : ℝ) ^ 30) * A.Cstar * Parameters.truncationScale S P +
        2 * (Parameters.truncationExponent S P : ℝ) *
          (Parameters.costFactor S P * Account.publicPrice S A) ≤
      Parameters.truncatedFactor S P * Account.publicPrice S A := by
  let h : ℝ := P.logarithm
  let N : ℝ := P.Nstar
  let q := Account.publicPrice S A
  have hh : 1 ≤ h := by
    dsimp only [h]
    exact_mod_cast (show 1 ≤ P.logarithm from Parameters.logarithm_pos S P)
  have hN : (1 : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast (show 1 ≤ P.Nstar by have := P.two_le; omega)
  have hC := A.Cstar_nonneg
  have hq := Account.publicPrice_nonneg S A
  have hCq : A.Cstar ≤ q := Account.Cstar_le_publicPrice S A
  have hj : (Parameters.truncationExponent S P : ℝ) ≤ 128 * h := by
    dsimp only [Parameters.truncationExponent, h]
    push_cast
    dsimp only [h] at hh
    linarith
  have hscale : Parameters.truncationScale S P / N ^ 30 ≤ (2 : ℝ) ^ 120 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hs := (Parameters.truncationScale_bounds S P).2
    exact hs.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hN (by decide : 20 ≤ 30)) (by positivity))
  have hrare :
      2 * (1 / (P.Nstar : ℝ) ^ 30) * A.Cstar * Parameters.truncationScale S P ≤
        (2 : ℝ) ^ 121 * A.Cstar := by
    have hm := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 2 * A.Cstar by positivity)
    dsimp only [N] at hm
    convert hm using 1 <;> ring
  have hmain :
      2 * (Parameters.truncationExponent S P : ℝ) *
          (Parameters.costFactor S P * q) ≤ (2 : ℝ) ^ 72 * h ^ 9 * q := by
    have hm := mul_le_mul_of_nonneg_right hj
      (show 0 ≤ 2 * (Parameters.costFactor S P * q) by
        dsimp only [Parameters.costFactor, q]; positivity)
    dsimp only [Parameters.costFactor, h] at *
    nlinarith
  have hpow : 1 ≤ h ^ 9 := one_le_pow₀ hh
  have hC9 : A.Cstar ≤ h ^ 9 * q :=
    hCq.trans (le_mul_of_one_le_left (by exact hq) hpow)
  have hq9 : 0 ≤ h ^ 9 * q := mul_nonneg (by positivity) hq
  have hmain' := hmain
  dsimp only [Parameters.truncatedFactor, h, q] at *
  nlinarith only [hrare, hmain', hC9, hq9]

end SteinerUpperBound.Matching.Padded
