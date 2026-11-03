module

public import SteinerUpperBound.ConcreteEstimator.Step.Contract
public import SteinerUpperBound.SavingEstimator.Resources.Specification

@[expose] public section

namespace SteinerUpperBound.ConcreteEstimator.Step

open QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

variable {n k K d : ℕ} {tables : Tables}

theorem performance_of_global (P : SavingEstimator.Resources.Performance K d)
    (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n) (hp : p = parameters n (k + 1))
    (hT : label.toList.toFinset = I.terminals) (hnd : label.toList.Nodup)
    (hroot : ∀ i : EstimatorFrontend.Index tables,
      bits (RuntimeWorld.coarseKey tables inverse i.val (label.get root)) = true) :
    Performance I bits label root p inverse
      (SavingEstimator.Resources.workBudget K d n) (SavingEstimator.Resources.positiveBudget K d n)
      (10 * beta n) := by
  subst p
  intro i cache hc
  exact P.accounts I bits label root (RuntimeWorld.coarseKey tables inverse i.val) (tables.coarse.scale i.val)
    hT hnd cache hc (hroot i)

end SteinerUpperBound.ConcreteEstimator.Step
