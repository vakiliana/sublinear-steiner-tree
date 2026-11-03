module

public import SteinerUpperBound.QueryProgram

@[expose] public section

namespace SteinerUpperBound.ProbabilityAccounting

open SteinerLowerBound
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

theorem expect_of_good (mu : Law Ω) (G : Set Ω) (f : Ω → ℝ) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (hf : ∀ x, 0 ≤ f x)
    (hgood : ∀ x ∈ G, 1 - epsilon ≤ f x) :
    1 - epsilon - mu.prob Gᶜ ≤ mu.expect f := by
  have hp (x : Ω) : (1 - epsilon) - (if x ∈ G then 0 else 1) ≤ f x := by
    by_cases hx : x ∈ G
    · simpa only [hx, ite_true, sub_zero] using hgood x hx
    · simp only [hx, ite_false]
      linarith [hf x]
  have hm := mu.expect_mono hp
  have hind : mu.expect (fun x => if x ∈ G then 0 else (1 : ℝ)) = mu.prob Gᶜ := by
    rw [Law.prob_eq_expect]
    apply congrArg mu.expect
    funext x
    by_cases hx : x ∈ G <;> simp [hx]
  simpa only [Law.expect_sub, Law.expect_const, hind] using hm

theorem truncated_tail (mu : Law Ω) (G : Set Ω) (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x) (a : ℝ) (ha : 0 < a) :
    mu.prob {x | a < f x} ≤ mu.prob Gᶜ +
      mu.expect (fun x => if x ∈ G then f x else 0) / a := by
  have hpoint (x : Ω) :
      (if a < f x then (1 : ℝ) else 0) ≤
        (if x ∈ G then 0 else 1) + (if x ∈ G then f x else 0) / a := by
    by_cases hx : x ∈ G <;> by_cases hg : a < f x
    · simp only [hx, hg, ite_true, zero_add]
      exact (le_div_iff₀ ha).mpr (by linarith)
    · simp only [hx, hg, ite_true, ite_false, zero_add]
      exact div_nonneg (hf x) ha.le
    · simp only [hx, hg, ite_true, ite_false, zero_div, add_zero, le_refl]
    · simp only [hx, hg, ite_false, zero_div, add_zero]
      norm_num
  have hm := mu.expect_mono hpoint
  have hind : mu.expect (fun x => if x ∈ G then 0 else (1 : ℝ)) = mu.prob Gᶜ := by
    rw [Law.prob_eq_expect]
    apply congrArg mu.expect
    funext x
    by_cases hx : x ∈ G <;> simp [hx]
  have hdiv :
      mu.expect (fun x => (if x ∈ G then f x else 0) / a) =
        mu.expect (fun x => if x ∈ G then f x else 0) / a := by
    simp only [div_eq_mul_inv, Law.expect_mul_const]
  rw [Law.expect_add, hind, hdiv] at hm
  simpa only [Law.prob_eq_expect, Set.mem_ofPred_eq] using hm

end SteinerUpperBound.ProbabilityAccounting
