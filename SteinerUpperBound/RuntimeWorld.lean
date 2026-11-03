module

public import SteinerUpperBound.RuntimeGeometry

@[expose] public section

noncomputable section

namespace SteinerUpperBound.RuntimeWorld

open SteinerLowerBound QueryProgram EstimatorParameters
open RuntimeGrids LabelledMetricWorld
open scoped Classical

variable {n k : ℕ}

abbrev Scales (t : Tables) := Fin (t.coarse.intervals + t.fine.intervals + 2)
abbrev Coordinate (t : Tables) (k : ℕ) := Scales t × Fin (k + 1)

noncomputable local instance : DecidableEq (Fin n) := Classical.decEq _
noncomputable local instance : DecidableEq (Fin (k + 1)) := Classical.decEq _
noncomputable local instance (t : Tables) : DecidableEq (Scales t) := Classical.decEq _
noncomputable local instance (t : Tables) : DecidableEq (Coordinate t k) := Classical.decEq _

def configuration (p : PublicParameters) (label : Vector (Fin n) (k + 1)) (t : Tables) :
    Covers.OracleProgram.Config (Fin n) (Coordinate t k) k :=
  LabelledFactory.config label t.radii p.coordinateCap p.trials

abbrev rhoTable (t : Tables) : Vector ℝ (t.coarse.intervals + t.fine.intervals + 2) :=
  Vector.ofFn (rho t)

theorem rhoTable_get (t : Tables) (i : Scales t) : (rhoTable t).get i = rho t i := by
  simp [rhoTable, Vector.get]
  congr 1

def Good (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1)) (t : Tables)
    (bits : Coordinate t k → Bool) : Prop :=
  LabelledCovers.Good I label (rhoTable t) bits

def coarseIndex (t : Tables) (i : Fin (t.coarse.intervals + 1)) : Scales t :=
  ⟨i.val, by omega⟩

def fineIndex (t : Tables) (i : Fin (t.fine.intervals + 1)) : Scales t :=
  ⟨t.coarse.intervals + 1 + i.val, by omega⟩

def coarseKey (t : Tables) (inverse : Vector (Fin (k + 1)) n) :
    ℕ → Fin n → Coordinate t k :=
  LabelledFactory.natKey inverse

def fineKey (t : Tables) (inverse : Vector (Fin (k + 1)) n) :
    ℕ → Fin n → Coordinate t k :=
  fun i => LabelledFactory.natKey inverse (t.coarse.intervals + 1 + i)

theorem coarse_key_eq (t : Tables) (inverse : Vector (Fin (k + 1)) n)
    (i : Fin (t.coarse.intervals + 1)) :
    coarseKey t inverse i.val = LabelledFactory.key inverse (coarseIndex t i) := by
  have hi : i.val < t.coarse.intervals + t.fine.intervals + 1 + 1 := by omega
  funext x
  simp only [coarseKey, LabelledFactory.natKey, LabelledFactory.key,
    Nat.mod_eq_of_lt hi, coarseIndex]

theorem fine_key_eq (t : Tables) (inverse : Vector (Fin (k + 1)) n)
    (i : Fin (t.fine.intervals + 1)) :
    fineKey t inverse i.val = LabelledFactory.key inverse (fineIndex t i) := by
  have hi : t.coarse.intervals + 1 + i.val < t.coarse.intervals + t.fine.intervals + 1 + 1 := by
    omega
  funext x
  simp only [fineKey, LabelledFactory.natKey, LabelledFactory.key,
    Nat.mod_eq_of_lt hi, fineIndex]

theorem rho_coarse (t : Tables) (i : Fin (t.coarse.intervals + 1)) :
    (rhoTable t).get (coarseIndex t i) = deltaCoarse * t.coarse.scale i.val := by
  rw [rhoTable_get]
  simp only [rho, coarseIndex]
  simp only [i.isLt, ite_true]

theorem rho_fine (t : Tables) (i : Fin (t.fine.intervals + 1)) :
    (rhoTable t).get (fineIndex t i) = deltaFine * t.fine.scale i.val := by
  have hn : ¬ t.coarse.intervals + 1 + i.val < t.coarse.intervals + 1 := by omega
  rw [rhoTable_get]
  simp only [rho, fineIndex, hn, ite_false, Nat.add_sub_cancel_left]

theorem retained_coarse (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hT : Finset.univ.image label.get = I.terminals) (t : Tables)
    (inverse : Vector (Fin (k + 1)) n) (hleft : ∀ j, inverse.get (label.get j) = j)
    (bits : Coordinate t k → Bool) (i : Fin (t.coarse.intervals + 1)) :
    ComponentExplore.retained bits (coarseKey t inverse i.val) I.terminals =
      retainedLabels label (fun j => bits (coarseIndex t i, j)) := by
  rw [coarse_key_eq, ← hT]
  exact retained_key label inverse hleft (coarseIndex t i) bits

theorem retained_fine (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hT : Finset.univ.image label.get = I.terminals) (t : Tables)
    (inverse : Vector (Fin (k + 1)) n) (hleft : ∀ j, inverse.get (label.get j) = j)
    (bits : Coordinate t k → Bool) (i : Fin (t.fine.intervals + 1)) :
    ComponentExplore.retained bits (fineKey t inverse i.val) I.terminals =
      retainedLabels label (fun j => bits (fineIndex t i, j)) := by
  rw [fine_key_eq, ← hT]
  exact retained_key label inverse hleft (fineIndex t i) bits

theorem coarse_good (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hT : Finset.univ.image label.get = I.terminals) (t : Tables)
    (inverse : Vector (Fin (k + 1)) n) (hleft : ∀ j, inverse.get (label.get j) = j)
    (bits : Coordinate t k → Bool) (hg : Good I label t bits) (i : Fin (t.coarse.intervals + 1)) :
    let N := ComponentExplore.retained bits (coarseKey t inverse i.val) I.terminals
    Covers.Geometry.CoverOn I I.terminals N (deltaCoarse * t.coarse.scale i.val) ∧
      ((N.card : ℕ) : ℝ) ≤ Hc n +
        6 * coverTrials n * hopBudget n * I.mst / (deltaCoarse * t.coarse.scale i.val) := by
  have hrow := hg (coarseIndex t i)
  have hr : 0 < (rhoTable t).get (coarseIndex t i) := by
    rw [rho_coarse]
    exact mul_pos metric_scale_constants.1 (t.coarse.scale_pos i.val)
  have hs := LabelledCovers.goodRow_size I label _ hr _ hrow
  rw [rho_coarse] at hrow hs
  dsimp only
  rw [retained_coarse I label hT t inverse hleft bits i]
  exact ⟨hrow.1, hs⟩

theorem fine_good (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hT : Finset.univ.image label.get = I.terminals) (t : Tables)
    (inverse : Vector (Fin (k + 1)) n) (hleft : ∀ j, inverse.get (label.get j) = j)
    (bits : Coordinate t k → Bool) (hg : Good I label t bits) (i : Fin (t.fine.intervals + 1)) :
    let N := ComponentExplore.retained bits (fineKey t inverse i.val) I.terminals
    Covers.Geometry.CoverOn I I.terminals N (deltaFine * t.fine.scale i.val) ∧
      ((N.card : ℕ) : ℝ) ≤ Hc n +
        6 * coverTrials n * hopBudget n * I.mst / (deltaFine * t.fine.scale i.val) := by
  have hrow := hg (fineIndex t i)
  have hr : 0 < (rhoTable t).get (fineIndex t i) := by
    rw [rho_fine]
    exact mul_pos metric_scale_constants.2.2.1 (t.fine.scale_pos i.val)
  have hs := LabelledCovers.goodRow_size I label _ hr _ hrow
  rw [rho_fine] at hrow hs
  dsimp only
  rw [retained_fine I label hT t inverse hleft bits i]
  exact ⟨hrow.1, hs⟩

theorem factory_failure (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (R : ℝ) (hR : 0 < R) (phase : Fin FinitePhase.count) (root : Fin (k + 1)) :
    let t := (RuntimeGrids.result (k + 1) (by omega) R hR phase).value
    (Covers.OracleProgram.bits (configuration (parameters n (k + 1)) label t) I.weight
      (LabelledFactory.initialCache root)).prob {bits | ¬ Good I label t bits} ≤ 1 / 4000000 := by
  dsimp only
  apply LabelledCovers.factory_failure I label hinj hT
    (rhoTable _) _ (fun i => ?_) (RuntimeGrids.length_bound n (k + 1) (by omega)
      (PublicTerminals.length_le label hinj) R hR phase) (fun i => ?_) root
  · rw [rhoTable_get]
    exact RuntimeGrids.rho_pos (RuntimeGrids.result (k + 1) (by omega) R hR phase).value i
  · rw [rhoTable_get]
    exact RuntimeGrids.get_radii (k + 1) (by omega) R hR phase i

theorem cache_on_support (p : PublicParameters) (label : Vector (Fin n) (k + 1)) (t : Tables)
    (root : Fin (k + 1)) (w : Sym2 (Fin n) → ℝ) (bits : Coordinate t k → Bool)
    (hb : 0 < (Covers.OracleProgram.bits (configuration p label t) w
      (LabelledFactory.initialCache root)).mass bits) :
    Cache.Correct bits (LabelledFactory.initialCache root) :=
  LabelledCovers.cache_correct_on_support label t.radii p.coordinateCap p.trials root w bits hb

theorem coarse_root (p : PublicParameters) (label : Vector (Fin n) (k + 1)) (t : Tables)
    (inverse : Vector (Fin (k + 1)) n) (hleft : ∀ j, inverse.get (label.get j) = j)
    (root : Fin (k + 1)) (w : Sym2 (Fin n) → ℝ) (bits : Coordinate t k → Bool)
    (hb : 0 < (Covers.OracleProgram.bits (configuration p label t) w
      (LabelledFactory.initialCache root)).mass bits) (i : ℕ) :
    bits (coarseKey t inverse i (label.get root)) = true := by
  apply cache_on_support p label t root w bits hb _ true
  simp [LabelledFactory.initialCache, coarseKey, LabelledFactory.natKey, hleft]

theorem fine_root (p : PublicParameters) (label : Vector (Fin n) (k + 1)) (t : Tables)
    (inverse : Vector (Fin (k + 1)) n) (hleft : ∀ j, inverse.get (label.get j) = j)
    (root : Fin (k + 1)) (w : Sym2 (Fin n) → ℝ) (bits : Coordinate t k → Bool)
    (hb : 0 < (Covers.OracleProgram.bits (configuration p label t) w
      (LabelledFactory.initialCache root)).mass bits) (i : ℕ) :
    bits (fineKey t inverse i (label.get root)) = true := by
  apply cache_on_support p label t root w bits hb _ true
  simp [LabelledFactory.initialCache, fineKey, LabelledFactory.natKey, hleft]

theorem coarse_mass (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hT : Finset.univ.image label.get = I.terminals) (t : Tables)
    (inverse : Vector (Fin (k + 1)) n) (hleft : ∀ j, inverse.get (label.get j) = j)
    (bits : Coordinate t k → Bool) (hg : Good I label t bits)
    (R : ℝ) (hR : 0 ≤ R) (hRL : R ≤ I.mst)
    (hq : t.coarse.q = Structural.omega) (hn : t.coarse.intervals + 1 ≤ heightBudget n)
    (hcap : t.coarse.scale t.coarse.intervals ≤ 4 * t.coarse.q * R) :
    EstimatorAnalysis.mass (t.coarse.toStructural hq)
      (fun i => ComponentExplore.retained bits (coarseKey t inverse i.val) I.terminals) ≤
        (A n : ℝ) * I.mst := by
  exact RuntimeGeometry.full_mass I t.coarse _ n R hq hR hRL hn hcap
    (fun i => (coarse_good I label hT t inverse hleft bits hg i).2)

end SteinerUpperBound.RuntimeWorld
