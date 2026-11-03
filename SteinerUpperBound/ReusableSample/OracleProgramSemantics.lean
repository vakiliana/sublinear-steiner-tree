module

public import SteinerUpperBound.ReusableSample.OracleProgramMatrix

@[expose] public section

namespace SteinerUpperBound.ReusableSample.OracleProgram

open SteinerLowerBound
open SteinerUpperBound.QueryProgram
open scoped BigOperators Classical

variable {M Q : Type*}

theorem evaluate_bind_good {R S : Type*} (m : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (k : R → Code M Q S) (r : R) (w q : ℕ)
    (h : Sure m b p (Good (· = r) w q)) (F : S → ℝ) :
    (p.bind k).evaluate m b (fun o => F o.value) =
      (k r).evaluate m b (fun o => F o.value) := by
  rw [evaluate_bind_value]
  exact evaluate_value_of_good m b p r w q h
    (fun r => (k r).evaluate m b (fun o => F o.value))

theorem rejectAll_expect (n : ℕ) (F : (Fin n → Bool) → ℝ) :
    (rejectAll n).law.expect F = F (fun _ => false) := by
  induction n with
  | zero =>
      simp only [rejectAll, Tree.law, Law.expect_pure]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      simp only [rejectAll, Tree.law, Law.expect_mix, Law.expect_map, zeroRate,
        zero_mul, sub_zero, one_mul, zero_add]
      rw [ih]
      congr 1
      funext i
      refine Fin.cases rfl (fun _ => rfl) i

private theorem bernoulli_expect (p : Rate) (F : Bool → ℝ) :
    (CategoricalCoupling.bernoulli p).expect F =
      (p : ℝ) * F true + (1 - (p : ℝ)) * F false := by
  simp [Law.expect, CategoricalCoupling.bernoulli]

/-- Semantics of the instrumented code, not a certificate assumed by it. -/
theorem loop_evaluate (m : M → ℝ) (b : Q → Bool) (Lbar Ns t : ℕ)
    {n : ℕ} (B : Fin n → Fin Ns → Bool) (quota : ℕ) (live : Fin Ns → Bool)
    (F : (Fin n → Bool) → ℝ) :
    (loop Lbar Ns t B quota live).evaluate m b (fun o => F o.value) =
      (matrixTree (rationalRate Lbar Ns t) B quota (flagSet live)).law.expect F := by
  induction n generalizing quota live with
  | zero =>
      simp [loop, matrixTree, Code.evaluate, Outcome.add, Outcome.pure, Tree.law]
  | succ n ih =>
      by_cases hq : quota = 0
      · rw [loop, ite_eq_left hq]
        simp only [Code.evaluate, Outcome.add]
        rw [evaluate_value_of_good m b (fill (n + 1) false) _
          (3 * (n + 1) + 1) 0 (fill_good m b _ _)]
        rw [matrixTree, ite_eq_left hq, rejectAll_expect]
      · rw [loop, ite_eq_right hq]
        simp only [Code.evaluate, Outcome.add]
        rw [evaluate_bind_good m b (scan live (B 0)) _
          (count live (B 0), deleted live (B 0)) (16 * Ns + 1) 0 (scan_good m b _ _)]
        dsimp only [Prod.fst, Prod.snd]
        rw [evaluate_bind_good m b (probability Lbar Ns t (count live (B 0))) _
          (fastProbability Lbar Ns t (count live (B 0))) _
          0 (probability_good m b _ _ _ _ (count_le _ _))]
        simp only [Code.evaluate, Outcome.add, coinRate_fastProbability, bernoulli_expect,
          evaluate_bind_value, Outcome.pure, Bool.false_eq_true, ↓reduceIte]
        rw [ih (fun j => B j.succ) (quota - 1) (deleted live (B 0))
            (fun tail => F (Tree.prepend true tail)),
          ih (fun j => B j.succ) quota live (fun tail => F (Tree.prepend false tail))]
        rw [matrixTree, ite_eq_right hq]
        simp only [Tree.law, Law.expect_mix, Law.expect_map, ← count_eq_card,
          flagSet_deleted]

end SteinerUpperBound.ReusableSample.OracleProgram
