module

public import SteinerUpperBound.ReusableSample.Paths

@[expose] public section

namespace SteinerUpperBound.ReusableSample

open SteinerLowerBound
open scoped BigOperators Classical

variable {U I : Type*} [Fintype I]

def Margins (X : I → Option U) {n : ℕ} (R : Fin n → Finset U)
    (t : ℕ) (C : Finset U) (lo hi : ℝ) (T : Fin n → Bool) : Prop :=
  ∀ j, tested t T j →
    if T j then lo ≤ liveCount X (fresh R T C j)
      else liveCount X (fresh R T C j) ≤ hi

theorem margins_zero (X : I → Option U) {n : ℕ} (R : Fin n → Finset U)
    (C : Finset U) (lo hi : ℝ) (T : Fin n → Bool) :
    Margins X R 0 C lo hi T := by
  intro j hj
  exact (not_tested_zero T j hj).elim

theorem margins_succ (X : I → Option U) {n : ℕ} (R : Fin (n + 1) → Finset U)
    (t : ℕ) (C : Finset U) (lo hi : ℝ) (T : Fin (n + 1) → Bool) :
    Margins X R t C lo hi T ↔
      ((t ≠ 0 → if T 0 then lo ≤ liveCount X (R 0 \ C)
        else liveCount X (R 0 \ C) ≤ hi) ∧
      Margins X (fun j => R j.succ) (if T 0 then t - 1 else t)
        (if T 0 then C ∪ R 0 else C) lo hi (fun j => T j.succ)) := by
  simp only [Margins, Fin.forall_fin_succ, tested, Fin.cases_zero, Fin.cases_succ,
    fresh, previousUnion]

private theorem prob_not_and {A : Type*} [Fintype A] (μ : Law A) (P : Prop) (Q : A → Prop) :
    μ.prob {v | ¬ (P ∧ Q v)} ≤ (if P then 0 else 1) + μ.prob {v | ¬ Q v} := by
  by_cases hp : P
  · simp [hp]
  · simp only [hp, false_and, not_false_eq_true, Set.ofPred_true, Law.prob_univ, ↓reduceIte]
    linarith [μ.prob_nonneg {v | ¬ Q v}]

/-- Conditional on any fixed dataset, a union bound over the actual tests.
There is no independence assumption about the live counts. -/
theorem pool_margins (b : ℝ) (hb : 0 < b) (H d : ℝ) (X : I → Option U)
    {n : ℕ} (R : Fin n → Finset U) (t : ℕ) (C : Finset U) :
    (poolTree b H X R t C).law.prob {T | ¬ Margins X R t C (H - d) (H + d) T} ≤
      2 * n * Real.exp (-d / b) := by
  induction n generalizing t C with
  | zero =>
      have he : {T : Fin 0 → Bool | ¬ Margins X R t C (H - d) (H + d) T} = ∅ := by
        ext T
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
        intro j
        exact Fin.elim0 j
      rw [he, Law.prob_empty]
      simp
  | succ n ih =>
      by_cases ht : t = 0
      · subst t
        have he : {T : Fin (n + 1) → Bool |
            ¬ Margins X R 0 C (H - d) (H + d) T} = ∅ := by
          ext T
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
          exact margins_zero _ _ _ _ _ _
        rw [he, Law.prob_empty]
        positivity
      · let c := liveCount X (R 0 \ C)
        let p := logistic b H c
        let η := Real.exp (-d / b)
        have hη : 0 ≤ η := (Real.exp_pos _).le
        have ha : (p : ℝ) * (if H - d ≤ c then 0 else 1) ≤ η := by
          by_cases hc : H - d ≤ c
          · simp only [hc, ↓reduceIte, mul_zero]
            exact hη
          · simp only [hc, ↓reduceIte, mul_one]
            exact (logistic_accept_bound b H c).trans (Real.exp_le_exp.mpr
              (div_le_div_of_nonneg_right (by linarith : -(H - c) ≤ -d) hb.le))
        have hr : (1 - (p : ℝ)) * (if c ≤ H + d then 0 else 1) ≤ η := by
          by_cases hc : c ≤ H + d
          · simp only [hc, ↓reduceIte, mul_zero]
            exact hη
          · simp only [hc, ↓reduceIte, mul_one]
            exact (logistic_reject_bound b H c).trans (Real.exp_le_exp.mpr
              (div_le_div_of_nonneg_right (by linarith : H - c ≤ -d) hb.le))
        have he₁ : Tree.prepend true ⁻¹'
            {T | ¬ Margins X R t C (H - d) (H + d) T} =
            {v | ¬ (H - d ≤ c ∧
              Margins X (fun j => R j.succ) (t - 1) (C ∪ R 0)
                (H - d) (H + d) v)} := by
          ext v
          simp [margins_succ, Tree.prepend, ht, c]
        have he₀ : Tree.prepend false ⁻¹'
            {T | ¬ Margins X R t C (H - d) (H + d) T} =
            {v | ¬ (c ≤ H + d ∧ Margins X (fun j => R j.succ) t C
                (H - d) (H + d) v)} := by
          ext v
          simp [margins_succ, Tree.prepend, ht, c]
        have h₁ := (prob_not_and
          (poolTree b H X (fun j => R j.succ) (t - 1) (C ∪ R 0)).law
          (H - d ≤ c) (Margins X (fun j => R j.succ) (t - 1) (C ∪ R 0)
            (H - d) (H + d))).trans
          (add_le_add (le_refl _) (ih (fun j => R j.succ) (t - 1) (C ∪ R 0)))
        have h₀ := (prob_not_and
          (poolTree b H X (fun j => R j.succ) t C).law
          (c ≤ H + d) (Margins X (fun j => R j.succ) t C (H - d) (H + d))).trans
          (add_le_add (le_refl _) (ih (fun j => R j.succ) t C))
        rw [poolTree, ite_eq_right ht, Tree.prob_node, he₁, he₀]
        have hw₁ := mul_le_mul_of_nonneg_left h₁ p.property.1
        have hw₀ := mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr p.property.2)
        change (p : ℝ) * _ + (1 - (p : ℝ)) * _ ≤ _
        push_cast
        dsimp [η] at ha hr
        nlinarith

end SteinerUpperBound.ReusableSample
