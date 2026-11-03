module

public import SteinerUpperBound.ConcreteEstimator.Correctness.Frontend
public import SteinerUpperBound.EstimatorBootstrap.Probability

@[expose] public section

noncomputable section

set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

namespace SteinerUpperBound.ConcreteEstimator.Correctness

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

variable {n k K d : ℕ}

noncomputable local instance preparedCoordinateDecEq (tables : Tables) :
    DecidableEq (RuntimeWorld.Coordinate tables k) := Classical.decEq _

def mixedWork (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (AW AP : ℕ) (R : ℝ) (hR : 0 < R) (phase : Fin FinitePhase.count) : ℝ :=
  let tables := (RuntimeGrids.result (k + 1) (by omega) R hR phase).value
  (Covers.OracleProgram.bits (RuntimeWorld.configuration (parameters n (k + 1)) label tables)
      I.weight (LabelledFactory.initialCache root)).expect (fun bits =>
    (ConcreteEstimator.frontend label root AW AP (parameters n (k + 1))
      (PublicTerminals.inverseResult label root).value tables (LabelledFactory.initialCache root)).evaluate
        I.weight bits (fun o => (o.work : ℝ)))

def mixedPositive (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (AW AP : ℕ) (R : ℝ) (hR : 0 < R) (phase : Fin FinitePhase.count) : ℝ :=
  let tables := (RuntimeGrids.result (k + 1) (by omega) R hR phase).value
  (Covers.OracleProgram.bits (RuntimeWorld.configuration (parameters n (k + 1)) label tables)
      I.weight (LabelledFactory.initialCache root)).expect (fun bits =>
    (ConcreteEstimator.frontend label root AW AP (parameters n (k + 1))
      (PublicTerminals.inverseResult label root).value tables (LabelledFactory.initialCache root)).evaluate
        I.weight bits (fun o => (o.positiveReplies : ℝ)))

theorem prepared_radius_success_of_mixed (performance : SavingEstimator.Resources.Performance K d)
    (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1)) (R : ℝ) (hR : 0 < R)
    (hRL : R ≤ I.mst) (hmin : floorScale (k + 1) R ≤ Structural.minimumTerminalDistance I)
    (hdiam : TreeGeometry.terminalDiameter I ≤ 2 * R)
    (P : ℝ → Prop) (hP : ∀ z, GoodEstimate (2 - c) I.optimum z → P z)
    (ordinary positive : ℕ)
    (hwork : ∀ phase, mixedWork I label root (SavingEstimator.Resources.workBudget K d n)
      (SavingEstimator.Resources.positiveBudget K d n) R hR phase ≤ ordinary)
    (hpositive : ∀ phase, mixedPositive I label root (SavingEstimator.Resources.workBudget K d n)
      (SavingEstimator.Resources.positiveBudget K d n) R hR phase ≤ positive) :
    (49 : ℝ) / 50 ≤ Code.valueProbability I.weight Code.emptyBits
      (EstimatorBootstrap.prepared label root
        (EstimatorClocks.factory (k + 1) ordinary positive).clock.workBudget
        (EstimatorClocks.factory (k + 1) ordinary positive).clock.disclosureBudget
        (ConcreteEstimator.frontend label root
          (SavingEstimator.Resources.workBudget K d n) (SavingEstimator.Resources.positiveBudget K d n)) R hR) P := by
  let front := ConcreteEstimator.frontend label root
    (SavingEstimator.Resources.workBudget K d n) (SavingEstimator.Resources.positiveBudget K d n)
  let fac := EstimatorClocks.factory (k + 1) ordinary positive
  have hfront : ∀ phase ∈ EstimatorBootstrap.PhaseGood (k := k) I R hR,
      let tables := (RuntimeGrids.result (k + 1) (by omega) R hR phase).value
      ∀ bits, 0 < (Covers.OracleProgram.bits
          (RuntimeWorld.configuration (parameters n (k + 1)) label tables) I.weight
          (LabelledFactory.initialCache root)).mass bits →
        RuntimeWorld.Good I label tables bits →
        1 - (1 : ℝ) / 100 ≤ Code.valueProbability I.weight bits
          (front (parameters n (k + 1)) (PublicTerminals.inverseResult label root).value tables
            (LabelledFactory.initialCache root)) (Code.SomeGood P) := by
    intro phase hphase
    exact generated_frontend_success performance I label hinj hT hk root R hR hRL hmin hdiam phase hphase P hP
  have hs := EstimatorBootstrap.prepared_success I label hinj (terminals_image_eq I label hT _) root
    fac.clock.workBudget fac.clock.disclosureBudget ordinary positive fac.positiveThreshold
    (EstimatorBudget.factory_threshold_pos (k + 1) ordinary positive)
    front R hR P (EstimatorBootstrap.PhaseGood (k := k) I R hR) (1 / 1000) (1 / 100) (by norm_num)
    (EstimatorBootstrap.phase_failure I label (terminals_image_eq I label hT _) root R hR hRL)
    hfront hwork hpositive
  have hm := prepared_margin (k + 1) ordinary positive (by omega) (1 / 100) (le_refl _)
  rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by simp] at hm
  exact hm.trans hs

theorem prepared_success_of_mixed (performance : SavingEstimator.Resources.Performance K d)
    (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1)) (ordinary positive : ℕ)
    (hwork :
      ∀ phase, mixedWork (observedInstance I label root) label root
        (SavingEstimator.Resources.workBudget K d n) (SavingEstimator.Resources.positiveBudget K d n)
        (observedRadius I label root) (observed_radius_pos I label hinj hT hk root) phase ≤ ordinary)
    (hpositive :
      ∀ phase, mixedPositive (observedInstance I label root) label root
        (SavingEstimator.Resources.workBudget K d n) (SavingEstimator.Resources.positiveBudget K d n)
        (observedRadius I label root) (observed_radius_pos I label hinj hT hk root) phase ≤ positive) :
    (49 : ℝ) / 50 ≤ Code.valueProbability (observedInstance I label root).weight Code.emptyBits
      (EstimatorBootstrap.prepared label root
        (EstimatorClocks.factory (k + 1) ordinary positive).clock.workBudget
        (EstimatorClocks.factory (k + 1) ordinary positive).clock.disclosureBudget
        (ConcreteEstimator.frontend label root
          (SavingEstimator.Resources.workBudget K d n) (SavingEstimator.Resources.positiveBudget K d n))
        (observedRadius I label root) (observed_radius_pos I label hinj hT hk root))
      (GoodEstimate (2 - c / 2) I.optimum) := by
  have h := observed_geometry I label hinj hT hk root
  exact prepared_radius_success_of_mixed performance (observedInstance I label root) label hinj hT hk root
    (observedRadius I label root) (observed_radius_pos I label hinj hT hk root) h.2.2.2.1 h.2.2.1 h.2.2.2.2
    (GoodEstimate (2 - c / 2) I.optimum) (flooring_transfer I label hinj hT hk root)
    ordinary positive hwork hpositive

theorem bootstrap_probability (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1)) (W D : ℕ)
    (front : EstimatorBootstrap.Frontend n k) (P : ℝ → Prop) :
    Code.valueProbability I.weight Code.emptyBits (EstimatorBootstrap.program label root W D front) P =
      Code.valueProbability (observedInstance I label root).weight Code.emptyBits
        (EstimatorBootstrap.prepared label root W D front (observedRadius I label root)
          (observed_radius_pos I label hinj hT hk root)) P := by
  have h := EstimatorBootstrap.program_value I label hinj (terminals_image_eq I label hT _) hk root W D front
    (fun z => if P z then (1 : ℝ) else 0)
  simpa only [Code.valueProbability, observedInstance, observedRadius, Vector.length_toList] using h

theorem bootstrap_success_of_mixed (performance : SavingEstimator.Resources.Performance K d)
    (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1)) (ordinary positive : ℕ)
    (hwork :
      ∀ phase, mixedWork (observedInstance I label root) label root
        (SavingEstimator.Resources.workBudget K d n) (SavingEstimator.Resources.positiveBudget K d n)
        (observedRadius I label root) (observed_radius_pos I label hinj hT hk root) phase ≤ ordinary)
    (hpositive :
      ∀ phase, mixedPositive (observedInstance I label root) label root
        (SavingEstimator.Resources.workBudget K d n) (SavingEstimator.Resources.positiveBudget K d n)
        (observedRadius I label root) (observed_radius_pos I label hinj hT hk root) phase ≤ positive) :
    (49 : ℝ) / 50 ≤ Code.valueProbability I.weight Code.emptyBits
      (EstimatorBootstrap.program label root
        (EstimatorClocks.factory (k + 1) ordinary positive).clock.workBudget
        (EstimatorClocks.factory (k + 1) ordinary positive).clock.disclosureBudget
        (ConcreteEstimator.frontend label root
          (SavingEstimator.Resources.workBudget K d n) (SavingEstimator.Resources.positiveBudget K d n)))
      (GoodEstimate (2 - c / 2) I.optimum) := by
  rw [bootstrap_probability I label hinj hT hk root]
  exact prepared_success_of_mixed performance I label hinj hT hk root ordinary positive hwork hpositive

theorem raw_probability (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (K L d : ℕ)
    (m : Sym2 (Fin n) → ℝ) (P : ℝ → Prop) :
    Code.valueProbability m Code.emptyBits (EstimatorRunner.raw label root K L d (ConcreteEstimator.family label root)) P =
      Code.valueProbability m Code.emptyBits
        (EstimatorBootstrap.program label root
          (EstimatorRunner.budget n (k + 1) K L d).factory.clock.workBudget
          (EstimatorRunner.budget n (k + 1) K L d).factory.clock.disclosureBudget
          (ConcreteEstimator.frontend label root
            (SavingEstimator.Resources.workBudget K d n) (SavingEstimator.Resources.positiveBudget K d n))) P := by
  rw [EstimatorRunner.raw, Code.valueProbability_bind, EstimatorBudget.program_evaluates]
  rfl

end SteinerUpperBound.ConcreteEstimator.Correctness
