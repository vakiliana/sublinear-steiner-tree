module

public import SteinerUpperBound.SavingEstimator.Program

@[expose] public section

namespace SteinerUpperBound.SavingEstimator.Resources

open SteinerLowerBound QueryProgram EstimatorParameters
open scoped Classical

def workBudget (K d n : ℕ) : ℕ := K * (n + 1) * t n * ell n ^ d
def positiveBudget (K d n : ℕ) : ℕ := K * t n * ell n ^ d

/-- The performance property is about the original actual saving-scale code.
It is a statement to be proved by the resource implementation, not a VO or
whole-program certificate supplied to that implementation. -/
structure Performance (K d : ℕ) : Prop where
  positive : 0 < K
  accounts : ∀ {Q : Type} {n k : ℕ} (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ),
    terminals.toList.toFinset = I.terminals → terminals.toList.Nodup →
    ∀ cache : Cache Q, Cache.Correct bits cache → bits (key (terminals.get root)) = true →
    let raw := SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache
    ∃ Good : (raw.compile I.weight).Seed → Prop,
      (raw.compile I.weight).law.prob {seed | ¬ Good seed} ≤ 10 * beta n ∧
      (raw.compile I.weight).law.expect (fun seed => if Good seed then
        (((raw.compile I.weight).tree seed).output bits).work else (0 : ℝ)) ≤ workBudget K d n ∧
      (raw.compile I.weight).law.expect (fun seed => if Good seed then
        (((raw.compile I.weight).tree seed).output bits).positiveReplies else (0 : ℝ)) ≤ positiveBudget K d n

end SteinerUpperBound.SavingEstimator.Resources
