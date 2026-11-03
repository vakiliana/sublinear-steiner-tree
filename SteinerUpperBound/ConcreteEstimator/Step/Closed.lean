module

public import SteinerUpperBound.ConcreteEstimator.Step.Performance
public import SteinerUpperBound.ConcreteEstimator.Step.Resources
public import SteinerUpperBound.SavingEstimator.Resources

@[expose] public section

namespace SteinerUpperBound.ConcreteEstimator.Step

open QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

variable {n k : ℕ} {tables : Tables}

theorem closed_error (n : ℕ) :
    error n (10 * beta n) = 14 * beta n +
      5 / (EstimatorClocks.amplification * ((heightBudget n : ℝ) + 1)) := by
  unfold error
  ring

theorem closed_performance (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n) (hp : p = parameters n (k + 1))
    (hT : label.toList.toFinset = I.terminals) (hnd : label.toList.Nodup)
    (hroot : ∀ i : EstimatorFrontend.Index tables,
      bits (RuntimeWorld.coarseKey tables inverse i.val (label.get root)) = true) :
    Performance I bits label root p inverse
      (SavingEstimator.Resources.workBudget SavingEstimator.Resources.resourceConstant 64 n)
      (SavingEstimator.Resources.positiveBudget SavingEstimator.Resources.resourceConstant 64 n)
      (10 * beta n) :=
  performance_of_global SavingEstimator.Resources.performance I bits label root p inverse hp hT hnd hroot

theorem closed_performance_of_le (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n) (hp : p = parameters n (k + 1))
    (hT : label.toList.toFinset = I.terminals) (hnd : label.toList.Nodup)
    (hroot : ∀ i : EstimatorFrontend.Index tables,
      bits (RuntimeWorld.coarseKey tables inverse i.val (label.get root)) = true)
    (AW AP : ℕ)
    (hAW : SavingEstimator.Resources.workBudget SavingEstimator.Resources.resourceConstant 64 n ≤ AW)
    (hAP : SavingEstimator.Resources.positiveBudget SavingEstimator.Resources.resourceConstant 64 n ≤ AP) :
    Performance I bits label root p inverse AW AP (10 * beta n) := by
  intro i cache hc
  obtain ⟨Good, hbad, hw, hp'⟩ := closed_performance I bits label root p inverse hp hT hnd hroot i cache hc
  exact ⟨Good, hbad, hw.trans (Nat.cast_le.mpr hAW), hp'.trans (Nat.cast_le.mpr hAP)⟩

theorem closed_saving_contract (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n)
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hp : p = parameters n (k + 1))
    (hroot : ∀ i : EstimatorFrontend.Index tables,
      bits (RuntimeWorld.coarseKey tables inverse i.val (label.get root)) = true) :
    EstimatorFrontend.Analysis.SavingContract I tables inverse bits
      (ConcreteEstimator.step label root p inverse tables
        (SavingEstimator.Resources.workBudget SavingEstimator.Resources.resourceConstant 64 n)
        (SavingEstimator.Resources.positiveBudget SavingEstimator.Resources.resourceConstant 64 n))
      (error n (10 * beta n)) :=
  saving_contract I bits label root p inverse _ _ _ hinj hT hp hroot
    (closed_performance I bits label root p inverse hp
      ((PublicTerminals.toList_toFinset label).trans hT) (PublicTerminals.toList_nodup label hinj) hroot)

theorem closed_saving_contract_of_geometry (I : Instance (Fin n))
    (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n) (R : ℝ)
    (G : EstimatorFrontend.Analysis.Geometry I label root tables inverse bits R)
    (hp : p = parameters n (k + 1)) :
    EstimatorFrontend.Analysis.SavingContract I tables inverse bits
      (ConcreteEstimator.step label root p inverse tables
        (SavingEstimator.Resources.workBudget SavingEstimator.Resources.resourceConstant 64 n)
        (SavingEstimator.Resources.positiveBudget SavingEstimator.Resources.resourceConstant 64 n))
      (error n (10 * beta n)) := by
  have hT : Finset.univ.image label.get = I.terminals := by
    ext x
    simpa only [Finset.mem_image, Finset.mem_univ, true_and] using Finset.ext_iff.mp G.terminals x
  exact closed_saving_contract I bits label root p inverse G.injective hT hp G.coarse_root

theorem closed_saving_contract_of_geometry_of_le (I : Instance (Fin n))
    (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n) (R : ℝ)
    (G : EstimatorFrontend.Analysis.Geometry I label root tables inverse bits R)
    (hp : p = parameters n (k + 1)) (AW AP : ℕ)
    (hAW : SavingEstimator.Resources.workBudget SavingEstimator.Resources.resourceConstant 64 n ≤ AW)
    (hAP : SavingEstimator.Resources.positiveBudget SavingEstimator.Resources.resourceConstant 64 n ≤ AP) :
    EstimatorFrontend.Analysis.SavingContract I tables inverse bits
      (ConcreteEstimator.step label root p inverse tables AW AP) (error n (10 * beta n)) := by
  have hT : Finset.univ.image label.get = I.terminals := by
    ext x
    simpa only [Finset.mem_image, Finset.mem_univ, true_and] using Finset.ext_iff.mp G.terminals x
  exact saving_contract_of_geometry I bits label root p inverse AW AP (10 * beta n) R G hp
    (closed_performance_of_le I bits label root p inverse hp
      ((PublicTerminals.toList_toFinset label).trans hT) (PublicTerminals.toList_nodup label G.injective)
      G.coarse_root AW AP hAW hAP)

end SteinerUpperBound.ConcreteEstimator.Step
