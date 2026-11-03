module

public import SteinerUpperBound.Matching.Padded.CollectionCost

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

namespace LowerCount

variable {A E : Type*} [Fintype A] [Fintype E]

theorem exp_indicator (μ : Law A) (P : A → Prop) :
    μ.expect (fun a => Real.exp (if P a then -1 else 0)) =
      1 + (Real.exp (-1) - 1) * μ.prob {a | P a} := by
  have h (a : A) : Real.exp (if P a then -1 else 0) =
      1 + (Real.exp (-1) - 1) * (if P a then 1 else 0) := by
    by_cases ha : P a <;> simp [ha]
  simp_rw [h, Law.expect_add, Law.expect_const, Law.expect_const_mul]
  have hp : μ.expect (fun a => if P a then 1 else 0) = μ.prob {a | P a} := by
    simpa only [Set.mem_ofPred_eq] using (Law.prob_eq_expect μ {a | P a}).symm
  rw [hp]

theorem exp_count (μ : E → Law A) (P : E → A → Prop) :
    (Law.pi μ).expect (fun w => Real.exp (-(IndependentTrials.count P w : ℝ))) =
      ∏ e, (1 + (Real.exp (-1) - 1) * (μ e).prob {a | P e a}) := by
  have hc (w : E → A) : (IndependentTrials.count P w : ℝ) =
      ∑ e, if P e (w e) then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp [IndependentTrials.count]
  have he (w : E → A) : Real.exp (-(IndependentTrials.count P w : ℝ)) =
      ∏ e, Real.exp (if P e (w e) then -1 else 0) := by
    rw [hc, ← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro e _
    split_ifs <;> simp
  simp_rw [he]
  rw [Law.expect_pi_product μ (fun e a => Real.exp (if P e a then -1 else 0))]
  exact Finset.prod_congr rfl fun e _ => exp_indicator (μ e) (P e)

theorem exp_count_le (μ : E → Law A) (P : E → A → Prop) :
    (Law.pi μ).expect (fun w => Real.exp (-(IndependentTrials.count P w : ℝ))) ≤
      Real.exp (-(IndependentTrials.mean μ P) / 2) := by
  have hhalf : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) Real.exp_one_gt_two.le
  rw [exp_count]
  calc
    _ ≤ ∏ e, Real.exp (-((μ e).prob {a | P e a}) / 2) := by
      apply Finset.prod_le_prod₀
      · intro e _
        have h0 := (μ e).prob_nonneg {a | P e a}
        have h1 := (μ e).prob_le_one {a | P e a}
        have he := (Real.exp_pos (-1)).le
        nlinarith
      · intro e _
        have hp := (μ e).prob_nonneg {a | P e a}
        have hm := mul_le_mul_of_nonneg_right hhalf hp
        have he := Real.one_sub_le_exp_neg ((μ e).prob {a | P e a} / 2)
        have he' : 1 - (μ e).prob {a | P e a} / 2 ≤
            Real.exp (-((μ e).prob {a | P e a}) / 2) := by simpa only [neg_div] using he
        nlinarith [he']
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [← Finset.sum_div, ← Finset.sum_neg_distrib, IndependentTrials.mean]

theorem tail (μ : E → Law A) (P : E → A → Prop) (z : ℝ) :
    (Law.pi μ).prob {w | IndependentTrials.mean μ P >
      2 * ((IndependentTrials.count P w : ℝ) + z)} ≤ Real.exp (-z) := by
  let M := IndependentTrials.mean μ P
  have hsub : {w | M > 2 * ((IndependentTrials.count P w : ℝ) + z)} ⊆
      {w | Real.exp (-M / 2 + z) ≤ Real.exp (-(IndependentTrials.count P w : ℝ))} := by
    intro w hw
    apply Real.exp_le_exp.mpr
    dsimp only [Set.mem_ofPred_eq] at hw
    linarith
  calc
    _ ≤ (Law.pi μ).prob {w |
        Real.exp (-M / 2 + z) ≤ Real.exp (-(IndependentTrials.count P w : ℝ))} :=
      Law.prob_mono _ hsub
    _ ≤ (Law.pi μ).expect (fun w => Real.exp (-(IndependentTrials.count P w : ℝ))) /
        Real.exp (-M / 2 + z) :=
      Law.markov _ (fun w => (Real.exp_pos _).le) (Real.exp_pos _)
    _ ≤ Real.exp (-M / 2) / Real.exp (-M / 2 + z) :=
      div_le_div_of_nonneg_right (exp_count_le μ P) (Real.exp_pos _).le
    _ = Real.exp (-z) := by
      rw [← Real.exp_sub]
      congr 1
      ring

end LowerCount

namespace UniformRanks

variable (Q : ℕ) (hQ : 0 < Q)

theorem mass (r : Fin Q) : (Range.law Q hQ 0 Q).mass r = (Q : ℝ)⁻¹ := by
  rw [Range.mass Q hQ 0 Q ⟨hQ, le_refl _⟩]
  simp [r.isLt]

theorem lt_probability (x : ℕ) (hx : x ≤ Q) :
    (Range.law Q hQ 0 Q).prob {r | r.val < x} = (x : ℝ) / Q := by
  unfold Law.prob
  simp only [Set.mem_ofPred_eq, mass]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, IntegerCoin.threshold_card Q x hx]
  rw [div_eq_mul_inv]

variable {V E : Type*} [Fintype E]

noncomputable def law : Law (E → Fin Q) := Law.pi fun _ : E => Range.law Q hQ 0 Q

noncomputable def Count (G : Graph V E) (v : V) (x : ℕ) (ranks : E → Fin Q) : ℕ :=
  IndependentTrials.count (fun e r => G.Incident e v ∧ r.val < x) ranks

theorem mean (G : Graph V E) (v : V) (x : ℕ) (hx : x ≤ Q) :
    IndependentTrials.mean (fun _ : E => Range.law Q hQ 0 Q)
      (fun e r => G.Incident e v ∧ r.val < x) = (x : ℝ) / Q * G.degree v := by
  classical
  have he (e : E) :
      (Range.law Q hQ 0 Q).prob {r | G.Incident e v ∧ r.val < x} =
        if G.Incident e v then (x : ℝ) / Q else 0 := by
    by_cases hi : G.Incident e v
    · simpa only [hi, true_and, ↓reduceIte] using lt_probability Q hQ x hx
    · simp [hi]
  unfold IndependentTrials.mean
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp [Graph.degree, mul_comm]

theorem lower_tail (G : Graph V E) (v : V) (x : ℕ) (hx : x ≤ Q) (z : ℝ) :
    (law Q hQ (E := E)).prob {ranks |
      (x : ℝ) / Q * G.degree v > 2 * ((Count Q G v x ranks : ℝ) + z)} ≤ Real.exp (-z) := by
  have hh := LowerCount.tail (fun _ : E => Range.law Q hQ 0 Q)
    (fun e r => G.Incident e v ∧ r.val < x) z
  rw [mean Q hQ G v x hx] at hh
  exact hh

theorem pair_collision (e f : E) (hef : e ≠ f) :
    (law Q hQ (E := E)).prob {ranks | ranks e = ranks f} = (Q : ℝ)⁻¹ := by
  letI : DecidableEq (Fin Q) := Classical.decEq _
  rw [Law.prob_eq_expect]
  change (Law.pi fun _ : E => Range.law Q hQ 0 Q).expect
    (fun w => if w e = w f then (1 : ℝ) else 0) = _
  rw [Law.expect_adaptive_coordinate (fun _ : E => Range.law Q hQ 0 Q) e
    (fun a w => if a = w f then 1 else 0)
    (fun a w b => by rw [Function.update_of_ne hef.symm])]
  have hi (a : Fin Q) :
      (Law.pi fun _ : E => Range.law Q hQ 0 Q).expect
        (fun w => if a = w f then (1 : ℝ) else 0) = (Q : ℝ)⁻¹ := by
    rw [Law.expect_pi_coordinate (fun _ : E => Range.law Q hQ 0 Q)
      (fun r => if a = r then 1 else 0) f]
    unfold Law.expect
    simp [mass, mul_ite]
  simp_rw [hi]
  rw [← Finset.sum_mul, (Range.law Q hQ 0 Q).total, one_mul]

theorem collision_bound :
    (law Q hQ (E := E)).prob {ranks | ¬ Function.Injective ranks} ≤
      (Fintype.card E : ℝ) ^ 2 / Q := by
  classical
  have heq : {ranks : E → Fin Q | ¬ Function.Injective ranks} =
      {ranks | ∃ ef : E × E, ef.1 ≠ ef.2 ∧ ranks ef.1 = ranks ef.2} := by
    ext ranks
    simp only [Function.Injective, Set.mem_ofPred_eq, Prod.exists]
    push Not
    constructor
    · rintro ⟨e, f, he, hne⟩
      exact ⟨e, f, hne, he⟩
    · rintro ⟨e, f, hne, he⟩
      exact ⟨e, f, he, hne⟩
  rw [heq]
  calc
    _ ≤ ∑ ef : E × E, (law Q hQ (E := E)).prob
        {ranks | ef.1 ≠ ef.2 ∧ ranks ef.1 = ranks ef.2} := Law.finite_union_bound _ _
    _ ≤ ∑ _ef : E × E, (Q : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro ef _
      by_cases h : ef.1 ≠ ef.2
      · have heq : {ranks : E → Fin Q | ef.1 ≠ ef.2 ∧ ranks ef.1 = ranks ef.2} =
            {ranks | ranks ef.1 = ranks ef.2} := by
          apply Set.ext
          intro ranks
          exact ⟨fun hh => hh.2, fun hh => ⟨h, hh⟩⟩
        rw [heq, pair_collision Q hQ ef.1 ef.2 h]
      · simp [h]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
        Nat.cast_mul]
      rw [div_eq_mul_inv, pow_two]

end UniformRanks

end SteinerUpperBound.Matching.Padded
