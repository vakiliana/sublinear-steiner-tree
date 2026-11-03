module

public import SteinerUpperBound.ConcreteEstimator.Correctness.Runner
public import SteinerUpperBound.ConcreteEstimator.Resources

@[expose] public section

noncomputable section

set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

namespace SteinerUpperBound.ConcreteEstimator.Correctness

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

variable {n k K d : ℕ}

theorem mixed_accounts (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (root : Fin (k + 1)) (K d : ℕ) (R : ℝ) (hR : 0 < R) (phase : Fin FinitePhase.count) :
    mixedWork I label root (SavingEstimator.Resources.workBudget K d n)
        (SavingEstimator.Resources.positiveBudget K d n) R hR phase ≤
      (ConcreteEstimator.frontendFactor K * (n + 1) * t n * ell n ^ (d + 140) : ℕ) ∧
      mixedPositive I label root (SavingEstimator.Resources.workBudget K d n)
          (SavingEstimator.Resources.positiveBudget K d n) R hR phase ≤
        (ConcreteEstimator.frontendFactor K * t n * ell n ^ (d + 140) : ℕ) := by
  let tables := (RuntimeGrids.result (k + 1) (by omega) R hR phase).value
  let inverse := (PublicTerminals.inverseResult label root).value
  have hlength := RuntimeGrids.length_bound n (k + 1) (by omega)
    (PublicTerminals.length_le label hinj) R hR phase
  change tables.coarse.intervals + tables.fine.intervals + 2 ≤ heightBudget n at hlength
  have hcoarse : tables.coarse.intervals + 1 ≤ heightBudget n := by omega
  have hfine : tables.fine.intervals ≤ heightBudget n := by omega
  exact ConcreteEstimator.frontend_mixed_expected I label hinj (terminals_image_eq I label hT _) root tables inverse
    (PublicTerminals.inverse_left label hinj root) K d hcoarse hfine

theorem prepared_success (performance : SavingEstimator.Resources.Performance K d)
    (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1)) :
    (49 : ℝ) / 50 ≤ Code.valueProbability (observedInstance I label root).weight Code.emptyBits
      (EstimatorBootstrap.prepared label root
        (EstimatorRunner.budget n (k + 1) K (ConcreteEstimator.frontendFactor K) d).factory.clock.workBudget
        (EstimatorRunner.budget n (k + 1) K (ConcreteEstimator.frontendFactor K) d).factory.clock.disclosureBudget
        (ConcreteEstimator.frontend label root
          (SavingEstimator.Resources.workBudget K d n) (SavingEstimator.Resources.positiveBudget K d n))
        (observedRadius I label root) (observed_radius_pos I label hinj hT hk root))
      (GoodEstimate (2 - c / 2) I.optimum) := by
  apply prepared_success_of_mixed performance I label hinj hT hk root
    (EstimatorRunner.budget n (k + 1) K (ConcreteEstimator.frontendFactor K) d).frontendWork
    (EstimatorRunner.budget n (k + 1) K (ConcreteEstimator.frontendFactor K) d).frontendPositive
  · intro phase
    exact (mixed_accounts (observedInstance I label root) label hinj hT root K d _ _ phase).1
  · intro phase
    exact (mixed_accounts (observedInstance I label root) label hinj hT root K d _ _ phase).2

theorem runner_success (performance : SavingEstimator.Resources.Performance K d)
    (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1)) :
    (9 : ℝ) / 10 ≤ Code.valueProbability I.weight Code.emptyBits
      (EstimatorRunner.program label root K (ConcreteEstimator.frontendFactor K) d (ConcreteEstimator.family label root))
      (GoodEstimate (2 - c / 2) I.optimum) := by
  apply runner_success_of_mixed performance I label hinj hT hk root
  · intro phase
    exact (mixed_accounts (observedInstance I label root) label hinj hT root K d _ _ phase).1
  · intro phase
    exact (mixed_accounts (observedInstance I label root) label hinj hT root K d _ _ phase).2

end SteinerUpperBound.ConcreteEstimator.Correctness
