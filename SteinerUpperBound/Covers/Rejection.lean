module

public import SteinerUpperBound.Covers.AdaptiveHits

@[expose] public section

namespace SteinerUpperBound.Covers.Rejection

open SteinerLowerBound
open scoped Classical BigOperators
open FiniteSampling

variable {U : Type*} [Fintype U] [Nonempty U]

noncomputable def retained (b : U → Bool) : Finset U := CategoricalCoupling.selected b

noncomputable def hitRate (b : U → Bool) : ℝ :=
  ((retained b).card : ℝ) / Fintype.card U

theorem hitRate_nonneg (b : U → Bool) : 0 ≤ hitRate b := by
  unfold hitRate
  positivity

theorem hitRate_le_one (b : U → Bool) : hitRate b ≤ 1 := by
  have hk : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  exact (div_le_one hk).mpr (by exact_mod_cast Finset.card_le_univ (retained b))

theorem hitRate_pos (b : U → Bool) (hb : (retained b).Nonempty) : 0 < hitRate b := by
  unfold hitRate
  exact div_pos (by exact_mod_cast Finset.card_pos.mpr hb)
    (by exact_mod_cast Fintype.card_pos)

theorem hitRate_ge_inverse (b : U → Bool) (hb : (retained b).Nonempty) :
    1 / (Fintype.card U : ℝ) ≤ hitRate b := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_pos.mpr hb

noncomputable def uniformRetained (b : U → Bool) (hb : (retained b).Nonempty) :
    Law U where
  mass x := if b x = true then ((retained b).card : ℝ)⁻¹ else 0
  nonneg x := by split_ifs <;> positivity
  total := by
    rw [← Finset.sum_filter (fun x => b x = true)]
    change (∑ _x ∈ retained b, ((retained b).card : ℝ)⁻¹) = 1
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Finset.card_pos.mpr hb).ne')

theorem uniform_hit_prob (b : U → Bool) :
    (Law.uniform U).prob {x | b x = true} = hitRate b := by
  have he : {x : U | b x = true} = (retained b : Set U) := by
    ext x
    simp [retained, CategoricalCoupling.selected]
  rw [he, uniform_prob]
  rfl

theorem uniform_split (b : U → Bool) (hb : (retained b).Nonempty)
    (f : U → ℝ) (c : ℝ) :
    (Law.uniform U).expect (fun x => if b x = true then f x else c) =
      hitRate b * (uniformRetained b hb).expect f + (1 - hitRate b) * c := by
  classical
  have hhit :
      (Law.uniform U).expect (fun x => if b x = true then f x else 0) =
        hitRate b * (uniformRetained b hb).expect f := by
    unfold Law.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : b x = true
    · have hg : ((retained b).card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_pos.mpr hb).ne'
      simp only [hx, ↓reduceIte, Law.uniform, uniformRetained, hitRate]
      field_simp
    · simp [hx, uniformRetained]
  have hmiss :
      (Law.uniform U).expect (fun x => if b x = true then (0 : ℝ) else 1) =
        1 - hitRate b := by
    have he := (Law.uniform U).prob_compl {x | b x = true}
    rw [uniform_hit_prob, Law.prob_eq_expect] at he
    convert he using 1
    apply congrArg (Law.uniform U).expect
    funext x
    by_cases hx : b x = true <;> simp [hx]
  have hf (x : U) : (if b x = true then f x else c) =
      (if b x = true then f x else 0) + (if b x = true then 0 else 1) * c := by
    by_cases hx : b x = true <;> simp [hx]
  simp_rw [hf, Law.expect_add, Law.expect_mul_const, hhit, hmiss]

/-- This procedure uses only membership answers, never the unknown retained
cardinality. -/
def first (b : U → Bool) : (C : ℕ) → (Fin C → U) → Option U
  | 0, _ => none
  | C + 1, w => if b (w 0) then some (w 0) else first b C (Fin.tail w)

def waiting (b : U → Bool) : (C : ℕ) → (Fin C → U) → ℕ
  | 0, _ => 0
  | C + 1, w => if b (w 0) then 1 else 1 + waiting b C (Fin.tail w)

theorem waiting_le (b : U → Bool) (C : ℕ) (w : Fin C → U) : waiting b C w ≤ C := by
  induction C with
  | zero => simp [waiting]
  | succ C ih =>
    simp only [waiting]
    split_ifs
    · omega
    · have h := ih (Fin.tail w)
      omega

noncomputable def firstLaw (b : U → Bool) : ℕ → Law (Option U)
  | 0 => Law.pure none
  | C + 1 => (Law.uniform U).bind (fun x =>
      if b x then Law.pure (some x) else firstLaw b C)

theorem first_law (b : U → Bool) (C : ℕ) :
    (tape (Law.uniform U) C).map (first b C) = firstLaw b C := by
  induction C with
  | zero =>
    simpa only [first, firstLaw] using map_const (tape (Law.uniform U) 0) (none : Option U)
  | succ C ih =>
    rw [map_tape_succ]
    simp only [firstLaw]
    congr 1
    funext x
    cases hx : b x
    · simpa only [first, Fin.cons_zero, Fin.tail_cons, hx, Bool.false_eq_true,
        ↓reduceIte] using ih
    · simp only [first, Fin.cons_zero, hx, ↓reduceIte]
      exact map_const _ _

theorem first_mass (b : U → Bool) (hb : (retained b).Nonempty) (C : ℕ) (z : Option U) :
    (firstLaw b C).mass z =
      (1 - (1 - hitRate b) ^ C) * ((uniformRetained b hb).map some).mass z +
        (1 - hitRate b) ^ C * (Law.pure none).mass z := by
  classical
  induction C with
  | zero => simp [firstLaw]
  | succ C ih =>
    change (Law.uniform U).expect (fun x =>
      (if b x then Law.pure (some x) else firstLaw b C).mass z) = _
    have he : (fun x => (if b x then Law.pure (some x) else firstLaw b C).mass z) =
        (fun x => if b x = true then (Law.pure (some x)).mass z else (firstLaw b C).mass z) := by
      funext x
      cases b x <;> rfl
    rw [he, uniform_split b hb, ih]
    have hm : (uniformRetained b hb).expect (fun x => (Law.pure (some x)).mass z) =
        ((uniformRetained b hb).map some).mass z := by
      unfold Law.expect Law.pure Law.map
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : z = some x
      · subst z
        simp
      · simp [hx, Ne.symm hx]
    rw [hm, pow_succ]
    ring

theorem first_failure (b : U → Bool) (hb : (retained b).Nonempty) (C : ℕ) :
    (tape (Law.uniform U) C).prob {w | first b C w = none} =
      (1 - hitRate b) ^ C := by
  calc
    _ = ((tape (Law.uniform U) C).map (first b C)).prob {none} :=
      (Law.prob_map _ _ _).symm
    _ = _ := by
      rw [first_law, CategoricalCoupling.probability_atom, first_mass b hb]
      simp [Law.map, Law.pure]

theorem first_success_atom (b : U → Bool) (hb : (retained b).Nonempty)
    (C : ℕ) (x : U) :
    (tape (Law.uniform U) C).prob {w | first b C w = some x} =
      (1 - (1 - hitRate b) ^ C) * (uniformRetained b hb).mass x := by
  calc
    _ = ((tape (Law.uniform U) C).map (first b C)).prob {some x} :=
      (Law.prob_map _ _ _).symm
    _ = _ := by
      rw [first_law, CategoricalCoupling.probability_atom, first_mass b hb]
      simp [Law.map, Law.pure]

theorem first_failure_exp (b : U → Bool) (hb : (retained b).Nonempty) (C : ℕ) :
    (tape (Law.uniform U) C).prob {w | first b C w = none} ≤
      Real.exp (-(C : ℝ) / Fintype.card U) := by
  rw [first_failure b hb]
  apply (survival_exp (hitRate_nonneg b) (hitRate_le_one b) C).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (hitRate_ge_inverse b hb) (Nat.cast_nonneg C)
  simpa only [div_eq_mul_inv, one_mul, neg_mul] using neg_le_neg h

theorem waiting_mean (b : U → Bool) (hb : (retained b).Nonempty) (C : ℕ) :
    (tape (Law.uniform U) C).expect (fun w => hitRate b * waiting b C w) =
      1 - (1 - hitRate b) ^ C := by
  induction C with
  | zero => simp [tape, waiting]
  | succ C ih =>
    rw [expect_tape_succ]
    have hf (x : U) :
        (tape (Law.uniform U) C).expect (fun w =>
          hitRate b * waiting b (C + 1) (Fin.cons x w)) =
            if b x = true then hitRate b
            else hitRate b + (1 - (1 - hitRate b) ^ C) := by
      cases hx : b x
      · simp only [waiting, Fin.cons_zero, Fin.tail_cons, hx, Bool.false_eq_true,
          ↓reduceIte, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
        rw [Law.expect_add, Law.expect_const, ih]
      · simp [waiting, hx]
    simp_rw [hf]
    rw [uniform_split b hb, Law.expect_const, pow_succ]
    ring

theorem waiting_mean_le_one (b : U → Bool) (hb : (retained b).Nonempty) (C : ℕ) :
    (tape (Law.uniform U) C).expect (fun w => hitRate b * waiting b C w) ≤ 1 := by
  rw [waiting_mean b hb]
  linarith [pow_nonneg (sub_nonneg.mpr (hitRate_le_one b)) C]

theorem waiting_second_moment (b : U → Bool) (hb : (retained b).Nonempty) (C : ℕ) :
    (tape (Law.uniform U) C).expect (fun w => (hitRate b * waiting b C w) ^ 2) ≤ 2 := by
  induction C with
  | zero => simp [tape, waiting]
  | succ C ih =>
    rw [expect_tape_succ]
    have hf (x : U) :
        (tape (Law.uniform U) C).expect (fun w =>
          (hitRate b * waiting b (C + 1) (Fin.cons x w)) ^ 2) =
            if b x = true then (hitRate b) ^ 2
            else (hitRate b) ^ 2 +
              2 * hitRate b * (1 - (1 - hitRate b) ^ C) +
                (tape (Law.uniform U) C).expect
                  (fun w => (hitRate b * waiting b C w) ^ 2) := by
      cases hx : b x
      · have he (w : Fin C → U) :
            (hitRate b * waiting b (C + 1) (Fin.cons x w)) ^ 2 =
              (hitRate b) ^ 2 + 2 * hitRate b * (hitRate b * waiting b C w) +
                (hitRate b * waiting b C w) ^ 2 := by
          simp only [waiting, Fin.cons_zero, Fin.tail_cons, hx, Bool.false_eq_true,
            ↓reduceIte, Nat.cast_add, Nat.cast_one]
          ring
        simp only [hx, Bool.false_eq_true, ↓reduceIte]
        simp_rw [he, Law.expect_add, Law.expect_const]
        rw [Law.expect_const_mul, waiting_mean b hb]
      · simp [waiting, hx]
    simp_rw [hf]
    rw [uniform_split b hb, Law.expect_const]
    have hp0 := hitRate_nonneg b
    have hp1 := hitRate_le_one b
    have hm : 1 - (1 - hitRate b) ^ C ≤ 1 := by
      linarith [pow_nonneg (sub_nonneg.mpr hp1) C]
    have hi := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hp1)
    have him := mul_le_mul_of_nonneg_left hm
      (mul_nonneg (by positivity : 0 ≤ 2 * hitRate b) (sub_nonneg.mpr hp1))
    nlinarith [sq_nonneg (hitRate b)]

end SteinerUpperBound.Covers.Rejection
