module

public import SteinerUpperBound.ConcreteEstimator.Correctness.Accounts
public import SteinerUpperBound.SavingEstimator.Resources

@[expose] public section

noncomputable section

set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

namespace SteinerUpperBound.ConcreteEstimator.Correctness

open SteinerLowerBound QueryProgram EstimatorParameters
open scoped Classical

variable {n K d : ℕ}

def eta0 : ℝ := c / 2

theorem eta0_bounds : 0 < eta0 ∧ eta0 < 1 := by
  norm_num [eta0, c, cQ]

/-- Correctness of the literal outer-capped program, conditional only on the
named original-seed saving performance property. This is not the final
unconditional upper-bound theorem. -/
theorem program_success (performance : SavingEstimator.Resources.Performance K d)
    {length : ℕ} (I : Instance (Fin n)) (label : Vector (Fin n) length)
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals) :
    (9 : ℝ) / 10 ≤ Code.valueProbability I.weight Code.emptyBits
      (ConcreteEstimator.program K (ConcreteEstimator.frontendFactor K) d label)
      (GoodEstimate (2 - eta0) I.optimum) := by
  cases length with
  | zero =>
      change (9 : ℝ) / 10 ≤ Code.valueProbability I.weight Code.emptyBits
        (.pure (0 : ℝ)) (GoodEstimate (2 - eta0) I.optimum)
      rw [pure_zero_success I label hT (by omega) (2 - eta0)]
      norm_num
  | succ length =>
      cases length with
      | zero =>
          change (9 : ℝ) / 10 ≤ Code.valueProbability I.weight Code.emptyBits
            (.pure (0 : ℝ)) (GoodEstimate (2 - eta0) I.optimum)
          rw [pure_zero_success I label hT (by omega) (2 - eta0)]
          norm_num
      | succ j =>
          have hcard : I.terminals.card = j + 2 :=
            LabelledCovers.terminal_card (k := j + 1) I label hinj (terminals_image_eq I label hT _)
          have hk : 2 ≤ I.terminals.card := by omega
          exact runner_success performance I label hinj hT hk (0 : Fin (j + 2))

theorem program_original_probability (performance : SavingEstimator.Resources.Performance K d)
    {length : ℕ} (I : Instance (Fin n)) (label : Vector (Fin n) length)
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals) :
    let p := ConcreteEstimator.program K (ConcreteEstimator.frontendFactor K) d label
    (9 : ℝ) / 10 ≤ (p.compile I.weight).law.prob {seed |
      GoodEstimate (2 - eta0) I.optimum ((((p.compile I.weight).tree seed).output Code.emptyBits).value)} := by
  intro p
  rw [Law.prob_eq_expect]
  have he := Code.compile_expect I.weight Code.emptyBits p
    (fun o => if GoodEstimate (2 - eta0) I.optimum o.value then (1 : ℝ) else 0)
  have hp := program_success performance I label hinj hT
  exact hp.trans_eq he.symm

theorem closed_program_success
    {length : ℕ} (I : Instance (Fin n)) (label : Vector (Fin n) length)
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals) :
    (9 : ℝ) / 10 ≤ Code.valueProbability I.weight Code.emptyBits
      (ConcreteEstimator.program SavingEstimator.Resources.resourceConstant
        (ConcreteEstimator.frontendFactor SavingEstimator.Resources.resourceConstant) 64 label)
      (GoodEstimate (2 - c / 2) I.optimum) :=
  program_success SavingEstimator.Resources.performance I label hinj hT

theorem closed_program_original_probability
    {length : ℕ} (I : Instance (Fin n)) (label : Vector (Fin n) length)
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals) :
    let p := ConcreteEstimator.program SavingEstimator.Resources.resourceConstant
      (ConcreteEstimator.frontendFactor SavingEstimator.Resources.resourceConstant) 64 label
    (9 : ℝ) / 10 ≤ (p.compile I.weight).law.prob {seed |
      GoodEstimate (2 - c / 2) I.optimum ((((p.compile I.weight).tree seed).output Code.emptyBits).value)} :=
  program_original_probability SavingEstimator.Resources.performance I label hinj hT

end SteinerUpperBound.ConcreteEstimator.Correctness
