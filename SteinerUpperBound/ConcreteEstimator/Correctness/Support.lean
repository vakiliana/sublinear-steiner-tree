module

public import SteinerUpperBound.ConcreteEstimator
public import SteinerUpperBound.EstimatorBootstrap.Geometry
public import SteinerUpperBound.EstimatorBudget.Failure
public import SteinerUpperBound.EstimatorAnalysis

@[expose] public section

noncomputable section

set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

namespace SteinerUpperBound.ConcreteEstimator.Correctness

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

variable {n k : ℕ}

noncomputable local instance supportCoordinateDecEq (tables : Tables) :
    DecidableEq (RuntimeWorld.Coordinate tables k) := Classical.decEq _

theorem terminals_list_eq (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hT : Finset.univ.image label.get = I.terminals) (decider : DecidableEq (Fin n)) :
    @List.toFinset (Fin n) decider label.toList = I.terminals := by
  have h := (@PublicTerminals.toList_toFinset (Fin n) (instDecidableEqFin n) (k + 1) label).trans hT
  ext x
  simpa only [List.mem_toFinset] using Finset.ext_iff.mp h x

theorem terminals_image_eq (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hT : Finset.univ.image label.get = I.terminals) (decider : DecidableEq (Fin n)) :
    @Finset.image (Fin (k + 1)) (Fin n) decider label.get Finset.univ = I.terminals := by
  ext x
  simpa only [Finset.mem_image] using Finset.ext_iff.mp hT x

def observedRadius (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) : ℝ :=
  rowValue I.weight (label.get root) label.toList 0

def observedInstance (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) :
    Instance (Fin n) :=
  TreeGeometry.Flooring.floored I (floorScale (k + 1) (observedRadius I label root))

theorem root_mem (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hT : Finset.univ.image label.get = I.terminals) (root : Fin (k + 1)) :
    label.get root ∈ I.terminals :=
  hT ▸ Finset.mem_image.mpr ⟨root, Finset.mem_univ _, rfl⟩

theorem observed_geometry (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1)) :
    0 < observedRadius I label root ∧
      0 < floorScale (k + 1) (observedRadius I label root) ∧
      floorScale (k + 1) (observedRadius I label root) ≤
        Structural.minimumTerminalDistance (observedInstance I label root) ∧
      observedRadius I label root ≤ (observedInstance I label root).mst ∧
      TreeGeometry.terminalDiameter (observedInstance I label root) ≤ 2 * observedRadius I label root := by
  have h := RuntimeGeometry.observed_geometry I (label.get root) label.toList
    (PublicTerminals.toList_nodup label hinj) (terminals_list_eq I label hT _)
    (root_mem I label hT root) hk
  simpa only [Vector.length_toList, observedRadius, observedInstance] using
    (show 0 < rowValue I.weight (label.get root) label.toList 0 ∧
      0 < floorScale label.toList.length (rowValue I.weight (label.get root) label.toList 0) ∧
      floorScale label.toList.length (rowValue I.weight (label.get root) label.toList 0) ≤
        Structural.minimumTerminalDistance
          (TreeGeometry.Flooring.floored I
            (floorScale label.toList.length (rowValue I.weight (label.get root) label.toList 0))) ∧
      rowValue I.weight (label.get root) label.toList 0 ≤
        (TreeGeometry.Flooring.floored I
          (floorScale label.toList.length (rowValue I.weight (label.get root) label.toList 0))).mst ∧
      TreeGeometry.terminalDiameter
          (TreeGeometry.Flooring.floored I
            (floorScale label.toList.length (rowValue I.weight (label.get root) label.toList 0))) ≤
        2 * rowValue I.weight (label.get root) label.toList 0 from
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩)

theorem observed_radius_pos (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1)) : 0 < observedRadius I label root :=
  (observed_geometry I label hinj hT hk root).1

theorem observed_phase_failure (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1)) :
    FinitePhase.law.prob
      (EstimatorBootstrap.PhaseGood (k := k) (observedInstance I label root) (observedRadius I label root)
        (observed_radius_pos I label hinj hT hk root))ᶜ ≤ 1 / 1000 :=
  EstimatorBootstrap.phase_failure (observedInstance I label root) label (terminals_image_eq I label hT _) root _ _
    (observed_geometry I label hinj hT hk root).2.2.2.1

theorem observed_frontend_geometry (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1)) :
    let F := observedInstance I label root
    let R := observedRadius I label root
    let hR := observed_radius_pos I label hinj hT hk root
    ∀ phase ∈ EstimatorBootstrap.PhaseGood (k := k) F R hR,
      let tables := (RuntimeGrids.result (k + 1) (by omega) R hR phase).value
      ∀ bits, 0 < (Covers.OracleProgram.bits
          (RuntimeWorld.configuration (parameters n (k + 1)) label tables) F.weight
          (LabelledFactory.initialCache root)).mass bits →
        RuntimeWorld.Good F label tables bits →
        EstimatorFrontend.Analysis.Geometry F label root tables
          (PublicTerminals.inverseResult label root).value bits R := by
  intro F R hR phase hphase
  have h := observed_geometry I label hinj hT hk root
  exact EstimatorBootstrap.generated_geometry F label hinj (terminals_image_eq I label hT _) hk root R hR
    h.2.2.2.1 h.2.2.1 h.2.2.2.2 phase hphase

theorem flooring_transfer (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1)) (estimate : ℝ)
    (hgood : GoodEstimate (2 - c) (observedInstance I label root).optimum estimate) :
    GoodEstimate (2 - c / 2) I.optimum estimate := by
  apply EstimatorAnalysis.observed_flooring_transfer I (label.get root) label.toList
    (PublicTerminals.toList_nodup label hinj) (terminals_list_eq I label hT _)
    (root_mem I label hT root) hk estimate
  simpa only [observedInstance, observedRadius, Vector.length_toList] using hgood

theorem someGood_mono {A : Type*} (P P' : A → Prop) (h : ∀ a, P a → P' a) :
    ∀ r, Code.SomeGood P r → Code.SomeGood P' r := by
  intro r hr
  obtain ⟨a, rfl, ha⟩ := hr
  exact ⟨a, rfl, h a ha⟩

theorem valueProbability_mono {M Q A : Type*} (m : M → ℝ) (bits : Q → Bool)
    (code : Code M Q A) (P P' : A → Prop) (h : ∀ a, P a → P' a) :
    Code.valueProbability m bits code P ≤ Code.valueProbability m bits code P' := by
  apply Code.evaluate_mono
  intro o
  by_cases hp : P o.value
  · simp only [hp, h o.value hp, ↓reduceIte, le_refl]
  · simp only [hp, ↓reduceIte]
    split_ifs <;> norm_num

theorem pure_zero_success {length : ℕ} (I : Instance (Fin n)) (label : Vector (Fin n) length)
    (hT : Finset.univ.image label.get = I.terminals) (hlen : length ≤ 1)
    (ratio : ℝ) :
    Code.valueProbability I.weight Code.emptyBits
      (Code.pure (M := Sym2 (Fin n)) (Q := Empty) (0 : ℝ)) (GoodEstimate ratio I.optimum) = 1 := by
  have hcard : I.terminals.card ≤ length := by
    rw [← hT]
    simpa only [Finset.card_univ, Fintype.card_fin] using (Finset.card_image_le (f := label.get) (s := Finset.univ))
  have hopt := I.optimum_eq_zero (hcard.trans hlen)
  simp only [Code.valueProbability, Code.evaluate, Outcome.pure, hopt, GoodEstimate, mul_zero,
    le_refl, and_self, ↓reduceIte]

end SteinerUpperBound.ConcreteEstimator.Correctness
