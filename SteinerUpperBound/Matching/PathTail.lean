module

public import SteinerUpperBound.Matching.WindowStacks

@[expose] public section

namespace SteinerUpperBound.Matching

open SteinerLowerBound
open scoped Classical BigOperators

namespace Budget

def halfLength (h : ℕ) : ℕ := 4 * (512 * h) ^ 2
def windowLength (h : ℕ) : ℕ := 2 * halfLength h
def depth (h : ℕ) : ℕ := 4 * h * windowLength h + 1
def degree (p h t : ℕ) : ℕ := 16 * p * h / t + 1

theorem windowLength_pos {h : ℕ} (hh : 0 < h) : 0 < windowLength h := by
  unfold windowLength halfLength
  positivity

theorem windowLength_ge_two {h : ℕ} (hh : 0 < h) : 2 ≤ windowLength h := by
  have : 0 < halfLength h := by unfold halfLength; positivity
  unfold windowLength
  omega

theorem depth_polynomial (h : ℕ) : depth h = 8388608 * h ^ 3 + 1 := by
  unfold depth windowLength halfLength
  ring

theorem factorial_tail_aux (B h : ℕ) (hB : 0 < B) (hbig : 8 * h ≤ 4 * B ^ 2) :
    (B : ℝ) ^ (2 * (4 * B ^ 2)) / (2 * (4 * B ^ 2)).factorial ≤
      Real.exp (-(8 : ℝ) * h) := by
  let q := 4 * B ^ 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hfac : (q : ℝ) ^ q ≤ ((2 * q).factorial : ℝ) := by
    have hn := Nat.factorial_mul_pow_sub_le_factorial (n := q) (m := 2 * q) (by omega)
    have hne : 2 * q - q = q := by omega
    rw [hne] at hn
    have hnR : (q.factorial : ℝ) * (q : ℝ) ^ q ≤ (2 * q).factorial := by
      exact_mod_cast hn
    have hpos : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
    exact (le_mul_of_one_le_left (pow_nonneg (le_of_lt hqR) _) hpos).trans hnR
  have hratio : (B : ℝ) ^ (2 * q) / (q : ℝ) ^ q = (1 / 4 : ℝ) ^ q := by
    rw [pow_mul, ← div_pow]
    congr 1
    apply (div_eq_iff (ne_of_gt hqR)).mpr
    have hqeq : (q : ℝ) = 4 * (B : ℝ) ^ 2 := by dsimp [q]; push_cast; rfl
    rw [hqeq]
    ring
  have hequarter : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    have he : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_three]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos 1) he
  calc
    _ ≤ (B : ℝ) ^ (2 * q) / (q : ℝ) ^ q :=
      div_le_div_of_nonneg_left (pow_nonneg hBR.le _) (pow_pos hqR _) hfac
    _ = (1 / 4 : ℝ) ^ q := hratio
    _ ≤ Real.exp (-1) ^ q := pow_le_pow_left₀ (by norm_num) hequarter _
    _ = Real.exp (-(q : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-(8 : ℝ) * h) := by
      apply Real.exp_le_exp.mpr
      have hh : (8 : ℝ) * h ≤ q := by exact_mod_cast hbig
      linarith

theorem factorial_tail (h : ℕ) (hh : 0 < h) :
    (512 * (h : ℝ)) ^ windowLength h / (windowLength h).factorial ≤
      Real.exp (-(8 : ℝ) * h) := by
  have hb : 0 < 512 * h := by positivity
  have hbig : 8 * h ≤ 4 * (512 * h) ^ 2 := by nlinarith
  simpa only [windowLength, halfLength, Nat.cast_mul, Nat.cast_ofNat] using
    factorial_tail_aux (512 * h) h hb hbig

theorem degree_mul_le (p h t : ℕ) (hh : 0 < h) (ht : t ≤ p) :
    degree p h t * t ≤ 17 * p * h := by
  have hd := Nat.div_mul_le_self (16 * p * h) t
  have hph : t ≤ p * h := by
    calc
      t ≤ p := ht
      _ ≤ p * h := Nat.le_mul_of_pos_right _ hh
  unfold degree
  nlinarith

theorem quarter_pos_and_reserve (p h t : ℕ) (hh : 0 < h)
    (ht : 2 * t ≤ p) (hp : 4 * windowLength h ≤ p) :
    0 < p / 4 ∧ p / 4 + t + windowLength h ≤ p ∧ p ≤ 8 * (p / 4) := by
  have hL := windowLength_ge_two hh
  have hd := Nat.div_mul_le_self p 4
  have hd' := Nat.lt_mul_div_succ p (by decide : 0 < 4)
  omega

theorem scaled_degree_le (p h t : ℕ) (hh : 0 < h)
    (ht : 2 * t ≤ p) (hp : 4 * windowLength h ≤ p) :
    ((3 * t : ℕ) : ℝ) * ((degree p h t : ℝ) / (p / 4 : ℕ)) ≤ 512 * h := by
  have hquarter := quarter_pos_and_reserve p h t hh ht hp
  have hr : (0 : ℝ) < (p / 4 : ℕ) := by exact_mod_cast hquarter.1
  have hprod : (degree p h t : ℝ) * t ≤ 17 * (p : ℝ) * h := by
    exact_mod_cast degree_mul_le p h t hh (by omega)
  have hpr : (p : ℝ) ≤ 8 * (p / 4 : ℕ) := by exact_mod_cast hquarter.2.2
  have hmul := mul_le_mul_of_nonneg_right hpr (Nat.cast_nonneg h : (0 : ℝ) ≤ h)
  push_cast
  rw [← mul_div_assoc, div_le_iff₀ hr]
  nlinarith

end Budget

namespace Graph

variable {V E : Type*} [Fintype E]
variable (G : Graph V E)

theorem windowPath_polylog_tail (h t : ℕ) (hh : 0 < h)
    (ht : 2 * t ≤ Fintype.card E) (hp : 4 * Budget.windowLength h ≤ Fintype.card E) :
    (Rank.uniform (E := E)).prob {ρ | G.HasWindowPath t (3 * t)
      (Budget.degree (Fintype.card E) h t) (Budget.windowLength h) ρ} ≤
      2 * Fintype.card E * Real.exp (-(8 : ℝ) * h) := by
  have hquarter := Budget.quarter_pos_and_reserve (Fintype.card E) h t hh ht hp
  have hh' : (1 : ℝ) ≤ 512 * h := by exact_mod_cast (show 1 ≤ 512 * h by omega)
  have hscale := Budget.scaled_degree_le (Fintype.card E) h t hh ht hp
  have hb : ((3 * t : ℕ) : ℝ) ≤ 2 * Fintype.card E := by exact_mod_cast (by omega : 3 * t ≤ 2 * Fintype.card E)
  have hbase : 0 ≤ ((3 * t : ℕ) : ℝ) *
      ((Budget.degree (Fintype.card E) h t : ℝ) / (Fintype.card E / 4 : ℕ)) := by positivity
  have hpow : (((3 * t : ℕ) : ℝ) *
      ((Budget.degree (Fintype.card E) h t : ℝ) / (Fintype.card E / 4 : ℕ))) ^
        (Budget.windowLength h - 1) ≤ (512 * (h : ℝ)) ^ Budget.windowLength h :=
    (pow_le_pow_left₀ hbase hscale _).trans (pow_le_pow_right₀ hh' (Nat.sub_le _ _))
  have hfac : (0 : ℝ) < (Budget.windowLength h).factorial := by
    exact_mod_cast Nat.factorial_pos _
  calc
    _ ≤ ((3 * t : ℕ) : ℝ) *
        (((3 * t : ℕ) : ℝ) *
          ((Budget.degree (Fintype.card E) h t : ℝ) / (Fintype.card E / 4 : ℕ))) ^
            (Budget.windowLength h - 1) / (Budget.windowLength h).factorial :=
      G.hasWindowPath_factorial_tail t (3 * t) _ _ _ (Budget.windowLength_pos hh)
        hquarter.1 hquarter.2.1
    _ ≤ (2 * Fintype.card E : ℝ) *
        ((512 * (h : ℝ)) ^ Budget.windowLength h / (Budget.windowLength h).factorial) := by
      rw [mul_div_assoc]
      exact mul_le_mul hb (div_le_div_of_nonneg_right hpow hfac.le)
        (by positivity) (by positivity)
    _ ≤ (2 * Fintype.card E : ℝ) * Real.exp (-(8 : ℝ) * h) :=
      mul_le_mul_of_nonneg_left (Budget.factorial_tail h hh) (by positivity)

theorem degreeGood_polylog_tail (h t : ℕ) (ht : 0 < t)
    (htp : t ≤ Fintype.card E) :
    (Rank.uniform (E := E)).prob {ρ |
      ¬ G.DegreeGood t (Budget.degree (Fintype.card E) h t) ρ} ≤
      Fintype.card E * Real.exp (-(8 : ℝ) * h) := by
  have hp : (0 : ℝ) < Fintype.card E := by exact_mod_cast ht.trans_le htp
  have hdiv := Nat.lt_mul_div_succ (16 * Fintype.card E * h) ht
  have hprod : (16 : ℝ) * Fintype.card E * h ≤
      (((Budget.degree (Fintype.card E) h t + 1 : ℕ) : ℝ) * t) := by
    have hn : 16 * Fintype.card E * h ≤
        (Budget.degree (Fintype.card E) h t + 1) * t := by
      unfold Budget.degree
      nlinarith
    exact_mod_cast hn
  have hexp : -((Budget.degree (Fintype.card E) h t + 1 : ℕ) : ℝ) * t /
      Fintype.card E ≤ -(8 : ℝ) * h := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
  exact (G.degreeGood_failure t _).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (Nat.cast_nonneg _))

end Graph

end SteinerUpperBound.Matching
