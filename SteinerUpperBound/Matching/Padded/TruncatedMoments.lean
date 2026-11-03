module

public import SteinerUpperBound.Matching.Padded.Moments

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

theorem indicator_expect {Ω : Type*} [Fintype Ω] (μ : Law Ω) (P : Ω → Prop) :
    μ.expect (fun ω => if P ω then (1 : ℝ) else 0) = μ.prob {ω | P ω} := by
  classical
  unfold Law.expect Law.prob
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P ω <;> simp [h]

theorem expect_two_bad {Ω : Type*} [Fintype Ω] (μ : Law Ω) (X Y : Ω → ℝ)
    (P Q : Ω → Prop) (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hY : ∀ ω, 0 ≤ Y ω) (hX : ∀ ω, X ω ≤ M)
    (hgood : ∀ ω, P ω → Q ω → X ω ≤ C * Y ω) :
    μ.expect X ≤ C * μ.expect (fun ω => if P ω then Y ω else 0) +
      M * (μ.prob {ω | ¬ P ω} + μ.prob {ω | ¬ Q ω}) := by
  classical
  have hp (ω : Ω) : X ω ≤ C * (if P ω then Y ω else 0) +
      M * ((if ¬ P ω then 1 else 0) + if ¬ Q ω then 1 else 0) := by
    by_cases hP : P ω <;> by_cases hQ : Q ω
    · simpa only [hP, hQ, not_true_eq_false, ↓reduceIte, add_zero, mul_zero] using hgood ω hP hQ
    · simp only [hP, hQ, not_true_eq_false, not_false_eq_true, ↓reduceIte, zero_add, mul_one]
      linarith [hX ω, mul_nonneg hC (hY ω)]
    · simp only [hP, hQ, not_true_eq_false, not_false_eq_true, ↓reduceIte, add_zero, mul_zero, mul_one, zero_add]
      exact hX ω
    · simp only [hP, hQ, not_false_eq_true, ↓reduceIte, mul_zero, zero_add]
      linarith [hX ω]
  have hh := μ.expect_mono hp
  rw [Law.expect_add, Law.expect_const_mul, Law.expect_const_mul, Law.expect_add] at hh
  have hP : μ.expect (fun ω => if ¬ P ω then (1 : ℝ) else 0) = μ.prob {ω | ¬ P ω} := by
    unfold Law.expect Law.prob
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : P ω <;> simp [h]
  have hQ : μ.expect (fun ω => if ¬ Q ω then (1 : ℝ) else 0) = μ.prob {ω | ¬ Q ω} := by
    unfold Law.expect Law.prob
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : Q ω <;> simp [h]
  rw [hP, hQ] at hh
  exact hh

theorem expect_one_bad {Ω : Type*} [Fintype Ω] (μ : Law Ω) (X Y : Ω → ℝ)
    (P : Ω → Prop) (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hY : ∀ ω, 0 ≤ Y ω) (hX : ∀ ω, X ω ≤ M)
    (hgood : ∀ ω, P ω → X ω ≤ C * Y ω) :
    μ.expect X ≤ C * μ.expect (fun ω => if P ω then Y ω else 0) +
      M * μ.prob {ω | ¬ P ω} := by
  have hh := expect_two_bad μ X Y P (fun _ => True) C M hC hM hY hX (fun ω h _ => hgood ω h)
  simpa only [not_true_eq_false, Set.setOf_false, Law.prob_empty, add_zero] using hh

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E] (P : Parameters S)

theorem Cache.requestValue_nonneg (u : V → ℝ) (hu : ∀ v, 0 ≤ u v) (s : Cache S P.rankCard) :
    0 ≤ Cache.requestValue S P.rankCard u s :=
  Finset.sum_nonneg fun v _ => mul_nonneg (hu v) (Nat.cast_nonneg _)

theorem Oracle.boundary_moment (A : Account S) (v : V) (z : ℝ) (hz : 0 ≤ z) :
    (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).expect
        (fun ranks => Cache.boundaryValue S P.rankCard A (Oracle.idealVertex S P v ranks).cache) ≤
      (8 * z + 10) * (Execution.law S P v).expect (fun x =>
        if Function.Injective x.2 then
          Cache.requestValue S P.rankCard (densityWeight S A)
            ((Oracle.vertex S P v).output x.1).cache else 0) +
        (∑ u, A.W u) *
          ((Fintype.card E : ℝ) ^ 2 / P.rankCard +
            Fintype.card V * (P.rankExponent + 2) * Real.exp (-z)) := by
  classical
  let μ := UniformRanks.law P.rankCard P.rankCard_pos (E := E)
  have hh := expect_two_bad μ
    (fun ranks => Cache.boundaryValue S P.rankCard A (Oracle.idealVertex S P v ranks).cache)
    (fun ranks => Cache.requestValue S P.rankCard (densityWeight S A)
      (Oracle.idealVertex S P v ranks).cache)
    Function.Injective (DensityGood S P z) (8 * z + 10) (∑ u, A.W u)
    (by linarith) (Finset.sum_nonneg fun u _ => A.W_nonneg u)
    (fun ranks => Cache.requestValue_nonneg S P (densityWeight S A) (densityWeight_nonneg S A) _)
    (fun ranks => Cache.boundaryValue_le_sum S P A _
      (Oracle.idealVertex_safe S P v ranks).invariant.legal)
    (fun ranks hn hg => boundaryValue_le S P A _ ranks hn
      (Oracle.idealVertex_safe S P v ranks).invariant
      (Oracle.idealVertex_accounted S P v ranks hn).1 z hz hg)
  have hstat := Execution.expect_ideal S P v (fun r ranks => if Function.Injective ranks then
    Cache.requestValue S P.rankCard (densityWeight S A) r.cache else 0)
  have hh' :
      μ.expect (fun ranks => Cache.boundaryValue S P.rankCard A (Oracle.idealVertex S P v ranks).cache) ≤
        (8 * z + 10) * (Execution.law S P v).expect (fun x => if Function.Injective x.2 then
          Cache.requestValue S P.rankCard (densityWeight S A)
            ((Oracle.vertex S P v).output x.1).cache else 0) +
          (∑ u, A.W u) * (μ.prob {ranks | ¬ Function.Injective ranks} +
            μ.prob {ranks | ¬ DensityGood S P z ranks}) := by
    convert hh using 1
    rw [hstat]
    congr 2
    apply congrArg μ.expect
    funext ranks
    by_cases hn : Function.Injective ranks <;> simp [hn]
  have ht := UniformRanks.collision_bound P.rankCard P.rankCard_pos (E := E)
  have hd := density_failure_le S P z
  exact hh'.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left (add_le_add ht hd)
      (show 0 ≤ (∑ u : V, A.W u) from Finset.sum_nonneg fun u _ => A.W_nonneg u)))

end SteinerUpperBound.Matching.Padded
