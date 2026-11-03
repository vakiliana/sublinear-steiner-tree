module

public import SteinerUpperBound.Algorithm
public import SteinerUpperBound.ConcreteEstimator.Correctness

@[expose] public section

namespace SteinerUpperBound

open SteinerLowerBound QueryProgram
open scoped Classical

/-- The actual public-input metric-query algorithm beats factor two on every
finite metric. Its optimization objective is the genuine Steiner minimum. -/
theorem upper_bound {n length : ℕ} (I : Instance (Fin n))
    (terminals : Vector (Fin n) length) (hinj : Function.Injective terminals.get)
    (hT : Finset.univ.image terminals.get = I.terminals) :
    (2 : ℝ) / 3 ≤ Code.valueProbability I.weight Code.emptyBits (algorithm terminals)
      (GoodEstimate (2 - eta0) I.optimum) := by
  have h := ConcreteEstimator.Correctness.closed_program_success I terminals hinj hT
  exact (by norm_num : (2 : ℝ) / 3 ≤ 9 / 10).trans h

/-- The same guarantee under the original compiled program's own finite seed law. -/
theorem upper_bound_original_probability {n length : ℕ} (I : Instance (Fin n))
    (terminals : Vector (Fin n) length) (hinj : Function.Injective terminals.get)
    (hT : Finset.univ.image terminals.get = I.terminals) :
    let p := algorithm terminals
    (2 : ℝ) / 3 ≤ (p.compile I.weight).law.prob {seed |
      GoodEstimate (2 - eta0) I.optimum
        ((((p.compile I.weight).tree seed).output Code.emptyBits).value)} := by
  have h := ConcreteEstimator.Correctness.closed_program_original_probability I terminals hinj hT
  exact (by norm_num : (2 : ℝ) / 3 ≤ 9 / 10).trans h

end SteinerUpperBound
