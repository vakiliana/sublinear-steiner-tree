module

public import SteinerUpperBound.Covers.Tapes

@[expose] public section

namespace SteinerUpperBound.Covers.FiniteSampling

open SteinerLowerBound
open scoped Classical BigOperators

variable {U S : Type*} [Fintype U] [Nonempty U]

def hits [DecidableEq U] (target : S → U) (step : S → U → S) :
    (B : ℕ) → S → (Fin B → U) → ℕ
  | 0, _, _ => 0
  | B + 1, s, w =>
      (if w 0 = target s then 1 else 0) + hits target step B (step s (w 0)) (Fin.tail w)

theorem uniform_exp_hit (x : U) :
    (Law.uniform U).expect (fun y => Real.exp (-(if y = x then (1 : ℝ) else 0))) =
      1 - (1 - Real.exp (-1)) / Fintype.card U := by
  classical
  rw [uniform_expect]
  have hf (y : U) : Real.exp (-(if y = x then (1 : ℝ) else 0)) =
      if y = x then Real.exp (-1) else 1 := by by_cases hy : y = x <;> simp [hy]
  simp_rw [hf]
  have hs := sum_three ({x} : Finset U) x (by simp) (Real.exp (-1)) 1 1
  simp only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one, sub_self,
    zero_mul, add_zero, mul_one, ite_self] at hs
  rw [hs]
  have hk : (Fintype.card U : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  <;> ring

/-- Targets can depend on the complete past state, but not on the next draw. -/
theorem exp_hits (target : S → U) (step : S → U → S) (B : ℕ) (s : S) :
    (tape (Law.uniform U) B).expect
      (fun w => Real.exp (-(hits target step B s w : ℝ))) =
        (1 - (1 - Real.exp (-1)) / Fintype.card U) ^ B := by
  classical
  induction B generalizing s with
  | zero => simp [tape, hits]
  | succ B ih =>
    rw [expect_tape_succ]
    have hf (x : U) (w : Fin B → U) :
        Real.exp (-(hits target step (B + 1) s (Fin.cons x w) : ℝ)) =
          Real.exp (-(if x = target s then (1 : ℝ) else 0)) *
            Real.exp (-(hits target step B (step s x) w : ℝ)) := by
      simp only [hits, Fin.cons_zero, Fin.tail_cons, Nat.cast_add]
      split_ifs <;> simp [Real.exp_add, add_comm, add_left_comm, add_assoc,
        neg_add, Real.exp_neg]
    simp_rw [hf, Law.expect_const_mul, ih, Law.expect_mul_const, uniform_exp_hit]
    rw [pow_succ]
    ring

theorem exp_neg_one_le_half : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
  have hm : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (1 : ℝ))
    (Real.exp_pos (-1)).le
  linarith

theorem exp_hits_le (target : S → U) (step : S → U → S) (B : ℕ) (s : S) :
    (tape (Law.uniform U) B).expect
      (fun w => Real.exp (-(hits target step B s w : ℝ))) ≤
        Real.exp (-(B : ℝ) / (2 * Fintype.card U)) := by
  classical
  rw [exp_hits]
  have hk : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hk1 : (1 : ℝ) ≤ Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hb : 0 ≤ 1 - (1 - Real.exp (-1)) / Fintype.card U := by
    apply sub_nonneg.mpr
    apply (div_le_one hk).mpr
    linarith [Real.exp_pos (-1)]
  have hbase : 1 - (1 - Real.exp (-1)) / Fintype.card U ≤
      Real.exp (-(1 : ℝ) / (2 * Fintype.card U)) := by
    have hd : (1 / 2 : ℝ) / Fintype.card U ≤
        (1 - Real.exp (-1)) / Fintype.card U :=
      div_le_div_of_nonneg_right (by linarith [exp_neg_one_le_half]) hk.le
    have he := Real.add_one_le_exp (-(1 : ℝ) / (2 * Fintype.card U))
    have heq : (1 / 2 : ℝ) / Fintype.card U = 1 / (2 * Fintype.card U) := by ring
    rw [heq] at hd
    simp only [neg_div] at he ⊢
    linarith
  have hp := pow_le_pow_left₀ hb hbase B
  rw [← Real.exp_nat_mul] at hp
  convert hp using 1 <;> congr 1 <;> ring

theorem hit_lower_tail (target : S → U) (step : S → U → S) (B : ℕ) (s : S)
    (a : ℝ) :
    (tape (Law.uniform U) B).prob {w | (hits target step B s w : ℝ) ≤ a} ≤
      Real.exp (a - (B : ℝ) / (2 * Fintype.card U)) := by
  classical
  have hs : {w | (hits target step B s w : ℝ) ≤ a} ⊆
      {w | Real.exp (-a) ≤ Real.exp (-(hits target step B s w : ℝ))} := by
    intro w hw
    exact Real.exp_le_exp.mpr (neg_le_neg hw)
  calc
    _ ≤ (tape (Law.uniform U) B).prob
        {w | Real.exp (-a) ≤ Real.exp (-(hits target step B s w : ℝ))} :=
      Law.prob_mono _ hs
    _ ≤ (tape (Law.uniform U) B).expect
        (fun w => Real.exp (-(hits target step B s w : ℝ))) / Real.exp (-a) :=
      Law.markov _ (fun _ => (Real.exp_pos _).le) (Real.exp_pos _)
    _ ≤ Real.exp (-(B : ℝ) / (2 * Fintype.card U)) / Real.exp (-a) :=
      div_le_div_of_nonneg_right (exp_hits_le target step B s) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

end SteinerUpperBound.Covers.FiniteSampling
