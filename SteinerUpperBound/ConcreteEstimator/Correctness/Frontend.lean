module

public import SteinerUpperBound.ConcreteEstimator.Correctness.Ledger
public import SteinerUpperBound.ConcreteEstimator.Step
public import SteinerUpperBound.SavingEstimator.Resources.Specification

@[expose] public section

noncomputable section

set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

namespace SteinerUpperBound.ConcreteEstimator.Correctness

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

variable {n k K d : ℕ} {tables : Tables}

noncomputable local instance frontendCorrectnessCoordinateDecEq (tables : Tables) :
    DecidableEq (RuntimeWorld.Coordinate tables k) := Classical.decEq _

theorem saving_contract (performance : SavingEstimator.Resources.Performance K d)
    (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (inverse : Vector (Fin (k + 1)) n) (R : ℝ)
    (G : EstimatorFrontend.Analysis.Geometry I label root tables inverse bits R) :
    EstimatorFrontend.Analysis.SavingContract I tables inverse bits
      (ConcreteEstimator.step label root (parameters n (k + 1)) inverse tables
        (SavingEstimator.Resources.workBudget K d n) (SavingEstimator.Resources.positiveBudget K d n))
      (Step.error n (10 * beta n)) := by
  have hT : Finset.univ.image label.get = I.terminals := by
    ext x
    simpa only [Finset.mem_image] using Finset.ext_iff.mp G.terminals x
  exact Step.saving_contract_of_geometry I bits label root _ inverse _ _ _ R G rfl
    (Step.performance_of_global performance I bits label root _ inverse rfl
      (terminals_list_eq I label hT _) (PublicTerminals.toList_nodup label G.injective) G.coarse_root)

theorem frontend_success (performance : SavingEstimator.Resources.Performance K d)
    (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (inverse : Vector (Fin (k + 1)) n) (R : ℝ)
    (G : EstimatorFrontend.Analysis.Geometry I label root tables inverse bits R)
    (cache : Cache (RuntimeWorld.Coordinate tables k)) (hc : Cache.Correct bits cache) :
    1 - (1 : ℝ) / 100 ≤ Code.valueProbability I.weight bits
      (ConcreteEstimator.frontend label root (SavingEstimator.Resources.workBudget K d n)
        (SavingEstimator.Resources.positiveBudget K d n) (parameters n (k + 1)) inverse tables cache)
      (Code.SomeGood (GoodEstimate (2 - c) I.optimum)) := by
  have hδ : 0 ≤ 10 * beta n := mul_nonneg (by norm_num) (beta_bounds n).1.le
  have hledger := failureLedger_small n tables (10 * beta n) 10 hδ (by decide)
    (le_refl _) G.fine_height G.coarse_height
  have hfront := EstimatorFrontend.Analysis.program_success G
    (ConcreteEstimator.step label root (parameters n (k + 1)) inverse tables
      (SavingEstimator.Resources.workBudget K d n) (SavingEstimator.Resources.positiveBudget K d n))
    (Step.error n (10 * beta n)) (Step.error_nonneg _ _ hδ)
    (saving_contract performance I bits label root inverse R G) cache hc
  exact (sub_le_sub_left hledger 1).trans hfront

theorem frontend_original_success (performance : SavingEstimator.Resources.Performance K d)
    (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1))
    (tables : Tables) (inverse : Vector (Fin (k + 1)) n) (R : ℝ)
    (bits : RuntimeWorld.Coordinate tables k → Bool)
    (G : EstimatorFrontend.Analysis.Geometry (observedInstance I label root) label root tables inverse bits R)
    (cache : Cache (RuntimeWorld.Coordinate tables k)) (hc : Cache.Correct bits cache) :
    1 - (1 : ℝ) / 100 ≤ Code.valueProbability (observedInstance I label root).weight bits
      (ConcreteEstimator.frontend label root (SavingEstimator.Resources.workBudget K d n)
        (SavingEstimator.Resources.positiveBudget K d n) (parameters n (k + 1)) inverse tables cache)
      (Code.SomeGood (GoodEstimate (2 - c / 2) I.optimum)) := by
  have hs := frontend_success performance (observedInstance I label root) bits label root inverse R G cache hc
  exact hs.trans (valueProbability_mono _ bits _ _ _
    (someGood_mono _ _ (flooring_transfer I label hinj hT hk root)))

theorem frontend_predicate_success (performance : SavingEstimator.Resources.Performance K d)
    (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (inverse : Vector (Fin (k + 1)) n) (R : ℝ)
    (G : EstimatorFrontend.Analysis.Geometry I label root tables inverse bits R)
    (cache : Cache (RuntimeWorld.Coordinate tables k)) (hc : Cache.Correct bits cache)
    (P : ℝ → Prop) (hP : ∀ z, GoodEstimate (2 - c) I.optimum z → P z) :
    1 - (1 : ℝ) / 100 ≤ Code.valueProbability I.weight bits
      (ConcreteEstimator.frontend label root (SavingEstimator.Resources.workBudget K d n)
        (SavingEstimator.Resources.positiveBudget K d n) (parameters n (k + 1)) inverse tables cache)
      (Code.SomeGood P) :=
  (frontend_success performance I bits label root inverse R G cache hc).trans
    (valueProbability_mono _ bits _ _ _ (someGood_mono _ _ hP))

theorem supported_frontend_success (performance : SavingEstimator.Resources.Performance K d)
    (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (tables : Tables) (inverse : Vector (Fin (k + 1)) n) (R : ℝ)
    (bits : RuntimeWorld.Coordinate tables k → Bool)
    (G : EstimatorFrontend.Analysis.Geometry I label root tables inverse bits R)
    (hb : 0 < (Covers.OracleProgram.bits
      (RuntimeWorld.configuration (parameters n (k + 1)) label tables) I.weight
      (LabelledFactory.initialCache root)).mass bits)
    (P : ℝ → Prop) (hP : ∀ z, GoodEstimate (2 - c) I.optimum z → P z) :
    1 - (1 : ℝ) / 100 ≤ Code.valueProbability I.weight bits
      (ConcreteEstimator.frontend label root (SavingEstimator.Resources.workBudget K d n)
        (SavingEstimator.Resources.positiveBudget K d n) (parameters n (k + 1))
        inverse tables (LabelledFactory.initialCache root)) (Code.SomeGood P) :=
  frontend_predicate_success performance I bits label root inverse R G (LabelledFactory.initialCache root)
    (RuntimeWorld.cache_on_support (parameters n (k + 1)) label tables root I.weight bits hb) P hP

/-- Keep the entire support implication behind the abstract-table boundary. -/
theorem table_frontend_success (performance : SavingEstimator.Resources.Performance K d)
    (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (tables : Tables) (inverse : Vector (Fin (k + 1)) n) (R : ℝ)
    (geometry : ∀ bits, 0 < (Covers.OracleProgram.bits
        (RuntimeWorld.configuration (parameters n (k + 1)) label tables) I.weight
        (LabelledFactory.initialCache root)).mass bits →
      RuntimeWorld.Good I label tables bits →
      EstimatorFrontend.Analysis.Geometry I label root tables inverse bits R)
    (P : ℝ → Prop) (hP : ∀ z, GoodEstimate (2 - c) I.optimum z → P z) :
    ∀ bits, 0 < (Covers.OracleProgram.bits
        (RuntimeWorld.configuration (parameters n (k + 1)) label tables) I.weight
        (LabelledFactory.initialCache root)).mass bits →
      RuntimeWorld.Good I label tables bits →
      1 - (1 : ℝ) / 100 ≤ Code.valueProbability I.weight bits
        (ConcreteEstimator.frontend label root (SavingEstimator.Resources.workBudget K d n)
          (SavingEstimator.Resources.positiveBudget K d n) (parameters n (k + 1))
          inverse tables (LabelledFactory.initialCache root)) (Code.SomeGood P) := by
  intro bits hb hg
  exact supported_frontend_success performance I label root tables inverse R bits (geometry bits hb hg) hb P hP

theorem generated_frontend_success (performance : SavingEstimator.Resources.Performance K d)
    (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1)) (R : ℝ) (hR : 0 < R)
    (hRL : R ≤ I.mst) (hmin : floorScale (k + 1) R ≤ Structural.minimumTerminalDistance I)
    (hdiam : TreeGeometry.terminalDiameter I ≤ 2 * R)
    (phase : Fin FinitePhase.count) (hphase : phase ∈ EstimatorBootstrap.PhaseGood (k := k) I R hR)
    (P : ℝ → Prop) (hP : ∀ z, GoodEstimate (2 - c) I.optimum z → P z) :
    let tables := (RuntimeGrids.result (k + 1) (by omega) R hR phase).value
    ∀ bits, 0 < (Covers.OracleProgram.bits
        (RuntimeWorld.configuration (parameters n (k + 1)) label tables) I.weight
        (LabelledFactory.initialCache root)).mass bits →
      RuntimeWorld.Good I label tables bits →
      1 - (1 : ℝ) / 100 ≤ Code.valueProbability I.weight bits
        (ConcreteEstimator.frontend label root (SavingEstimator.Resources.workBudget K d n)
          (SavingEstimator.Resources.positiveBudget K d n) (parameters n (k + 1))
          (PublicTerminals.inverseResult label root).value tables (LabelledFactory.initialCache root))
        (Code.SomeGood P) := by
  exact table_frontend_success performance I label root (RuntimeGrids.result (k + 1) (by omega) R hR phase).value
    (PublicTerminals.inverseResult label root).value R
    (EstimatorBootstrap.generated_geometry I label hinj (terminals_image_eq I label hT _) hk root R hR
      hRL hmin hdiam phase hphase) P hP

end SteinerUpperBound.ConcreteEstimator.Correctness
