module

public import SteinerUpperBound.Covers.Tapes

@[expose] public section

namespace SteinerUpperBound.ScoreSampling

open SteinerLowerBound
open Covers.FiniteSampling
open scoped Classical BigOperators

variable {Ω : Type*} [Fintype Ω]

noncomputable def empirical (f : Ω → ℝ) (n : ℕ) (w : Fin n → Ω) : ℝ :=
  (∑ i, f (w i)) / n

theorem mean_bounds (μ : Law Ω) (f : Ω → ℝ) (hf₀ : ∀ x, 0 ≤ f x)
    (hf₁ : ∀ x, f x ≤ 1) : 0 ≤ μ.expect f ∧ μ.expect f ≤ 1 := by
  refine ⟨μ.expect_nonneg hf₀, ?_⟩
  simpa only [Law.expect_const] using μ.expect_mono hf₁

theorem centered_square_le_one (μ : Law Ω) (f : Ω → ℝ)
    (hf₀ : ∀ x, 0 ≤ f x) (hf₁ : ∀ x, f x ≤ 1) :
    μ.expect (fun x => (f x - μ.expect f) ^ 2) ≤ 1 := by
  have hm := mean_bounds μ f hf₀ hf₁
  have hpoint (x : Ω) : (f x - μ.expect f) ^ 2 ≤ 1 := by
    have h : |f x - μ.expect f| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hf₀ x], by linarith [hf₁ x]⟩
    have hs := mul_self_le_mul_self (abs_nonneg (f x - μ.expect f)) h
    nlinarith [sq_abs (f x - μ.expect f)]
  simpa only [Law.expect_const] using μ.expect_mono hpoint

theorem empirical_centered_square (μ : Law Ω) (f : Ω → ℝ)
    (n : ℕ) (hn : 0 < n) :
    (tape μ n).expect (fun w => (empirical f n w - μ.expect f) ^ 2) =
      μ.expect (fun x => (f x - μ.expect f) ^ 2) / n := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hf : μ.expect (fun x => f x - μ.expect f) = 0 := by
    rw [Law.expect_sub, Law.expect_const, sub_self]
  have hw (w : Fin n → Ω) :
      (empirical f n w - μ.expect f) ^ 2 =
        (∑ j, (f (w j) - μ.expect f)) ^ 2 * ((n : ℝ) ^ 2)⁻¹ := by
    simp only [empirical, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    <;> ring
  simp_rw [hw, Law.expect_mul_const, centered_sum_square μ _ hf n]
  field_simp
  <;> ring

theorem empirical_second_moment (μ : Law Ω) (f : Ω → ℝ)
    (hf₀ : ∀ x, 0 ≤ f x) (hf₁ : ∀ x, f x ≤ 1) (n : ℕ) (hn : 0 < n) :
    (tape μ n).expect (fun w => (empirical f n w - μ.expect f) ^ 2) ≤ 1 / n := by
  rw [empirical_centered_square μ f n hn]
  exact div_le_div_of_nonneg_right (centered_square_le_one μ f hf₀ hf₁)
    (Nat.cast_nonneg n)

theorem empirical_deviation (μ : Law Ω) (f : Ω → ℝ)
    (hf₀ : ∀ x, 0 ≤ f x) (hf₁ : ∀ x, f x ≤ 1)
    (n : ℕ) (hn : 0 < n) (accuracy : ℝ) (ha : 0 < accuracy) :
    (tape μ n).prob {w | accuracy ≤ |empirical f n w - μ.expect f|} ≤
      1 / ((n : ℝ) * accuracy ^ 2) := by
  have hset :
      {w : Fin n → Ω | accuracy ≤ |empirical f n w - μ.expect f|} ⊆
        {w | accuracy ^ 2 ≤ (empirical f n w - μ.expect f) ^ 2} := by
    intro w hw
    change accuracy ≤ |empirical f n w - μ.expect f| at hw
    change accuracy ^ 2 ≤ (empirical f n w - μ.expect f) ^ 2
    have h := mul_self_le_mul_self ha.le hw
    simpa only [← sq, sq_abs] using h
  calc
    _ ≤ (tape μ n).prob {w | accuracy ^ 2 ≤ (empirical f n w - μ.expect f) ^ 2} :=
      (tape μ n).prob_mono hset
    _ ≤ (tape μ n).expect (fun w => (empirical f n w - μ.expect f) ^ 2) / accuracy ^ 2 :=
      (tape μ n).markov (fun _ => sq_nonneg _) (sq_pos_of_pos ha)
    _ ≤ (1 / (n : ℝ)) / accuracy ^ 2 :=
      div_le_div_of_nonneg_right (empirical_second_moment μ f hf₀ hf₁ n hn)
        (sq_nonneg accuracy)
    _ = _ := div_div _ _ _

theorem empirical_deviation_of_budget (μ : Law Ω) (f : Ω → ℝ)
    (hf₀ : ∀ x, 0 ≤ f x) (hf₁ : ∀ x, f x ≤ 1)
    (n : ℕ) (hn : 0 < n) (accuracy beta : ℝ) (ha : 0 < accuracy)
    (hbudget : 1 ≤ beta * ((n : ℝ) * accuracy ^ 2)) :
    (tape μ n).prob {w | accuracy < |empirical f n w - μ.expect f|} ≤ beta := by
  have hset : {w : Fin n → Ω | accuracy < |empirical f n w - μ.expect f|} ⊆
      {w | accuracy ≤ |empirical f n w - μ.expect f|} := by
    intro w hw
    change accuracy < |empirical f n w - μ.expect f| at hw
    change accuracy ≤ |empirical f n w - μ.expect f|
    exact hw.le
  apply ((tape μ n).prob_mono hset).trans
  apply (empirical_deviation μ f hf₀ hf₁ n hn accuracy ha).trans
  exact (div_le_iff₀ (mul_pos (by exact_mod_cast hn) (sq_pos_of_pos ha))).mpr hbudget

end SteinerUpperBound.ScoreSampling
