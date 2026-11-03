module

public import SteinerUpperBound.ConcreteEstimator.Correctness.Prepared

@[expose] public section

noncomputable section

set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

namespace SteinerUpperBound.ConcreteEstimator.Correctness

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

variable {n k K L d : ℕ}

theorem runner_success_of_mixed (performance : SavingEstimator.Resources.Performance K d)
    (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1))
    (hwork :
      ∀ phase, mixedWork (observedInstance I label root) label root
        (SavingEstimator.Resources.workBudget K d n) (SavingEstimator.Resources.positiveBudget K d n)
        (observedRadius I label root) (observed_radius_pos I label hinj hT hk root) phase ≤
          (EstimatorRunner.budget n (k + 1) K L d).frontendWork)
    (hpositive :
      ∀ phase, mixedPositive (observedInstance I label root) label root
        (SavingEstimator.Resources.workBudget K d n) (SavingEstimator.Resources.positiveBudget K d n)
        (observedRadius I label root) (observed_radius_pos I label hinj hT hk root) phase ≤
          (EstimatorRunner.budget n (k + 1) K L d).frontendPositive) :
    (9 : ℝ) / 10 ≤ Code.valueProbability I.weight Code.emptyBits
      (EstimatorRunner.program label root K L d (ConcreteEstimator.family label root))
      (GoodEstimate (2 - c / 2) I.optimum) := by
  have hbootstrap := bootstrap_success_of_mixed performance I label hinj hT hk root
    (EstimatorRunner.budget n (k + 1) K L d).frontendWork
    (EstimatorRunner.budget n (k + 1) K L d).frontendPositive hwork hpositive
  have hraw : (49 : ℝ) / 50 ≤ Code.valueProbability I.weight Code.emptyBits
      (EstimatorRunner.raw label root K L d (ConcreteEstimator.family label root))
      (GoodEstimate (2 - c / 2) I.optimum) := by
    rw [raw_probability]
    exact hbootstrap
  have hout := EstimatorRunner.program_success label root hinj K L d
    (ConcreteEstimator.family label root) I.weight (GoodEstimate (2 - c / 2) I.optimum)
  linarith

end SteinerUpperBound.ConcreteEstimator.Correctness
