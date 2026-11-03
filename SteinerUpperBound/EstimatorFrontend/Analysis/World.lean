module

public import SteinerUpperBound.EstimatorFrontend
public import SteinerUpperBound.EstimatorAnalysis.Parameters

@[expose] public section

namespace SteinerUpperBound.EstimatorFrontend.Analysis

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids Covers.Geometry
open scoped Classical BigOperators
open BandCompleteness

variable {n k : ℕ}

noncomputable local instance worldVertexDecEq : DecidableEq (Fin n) := Classical.decEq _
noncomputable local instance worldLabelDecEq : DecidableEq (Fin (k + 1)) := Classical.decEq _

noncomputable abbrev coarseRetained (I : Instance (Fin n)) (t : Tables)
    (inverse : Vector (Fin (k + 1)) n) (bits : RuntimeWorld.Coordinate t k → Bool) :
    Index t → Finset (Fin n) :=
  fun i => ComponentExplore.retained bits (RuntimeWorld.coarseKey t inverse i.val) I.terminals

/-- Only concrete geometry, retained-cover events, and public enumeration facts.
No MST interval, band estimate, or final numerical correctness is a field. -/
structure Geometry (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (root : Fin (k + 1)) (t : Tables) (inverse : Vector (Fin (k + 1)) n)
    (bits : RuntimeWorld.Coordinate t k → Bool) (R : ℝ) : Prop where
  injective : Function.Injective label.get
  terminals : Finset.univ.image label.get = I.terminals
  inverse_left : ∀ j, inverse.get (label.get j) = j
  world : RuntimeWorld.Good I label t bits
  coarse_root : ∀ i : Index t, bits (RuntimeWorld.coarseKey t inverse i.val (label.get root)) = true
  fine_root : ∀ i < t.fine.intervals, bits (RuntimeWorld.fineKey t inverse i (label.get root)) = true
  coarse_ratio : t.coarse.q = Structural.omega
  fine_ratio : t.fine.q = MSTApproximation.fineRatio nu
  coarse_height : t.coarse.intervals + 1 ≤ heightBudget n
  fine_height : t.fine.intervals ≤ heightBudget n
  radius_nonneg : 0 ≤ R
  radius_le : R ≤ I.mst
  coarse_last : t.coarse.scale t.coarse.intervals ≤ 4 * t.coarse.q * R
  fine_last : t.fine.scale t.fine.intervals ≤ 4 * t.fine.q * R
  fine_first : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, x ≠ y → t.fine.first ≤ I.distance x y
  fine_diameter : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, I.distance x y ≤ t.fine.scale t.fine.intervals
  covers : (t.coarse.toStructural coarse_ratio).Covers I
  phase : weightedPhaseBad I (t.coarse.toStructural coarse_ratio)
    (EstimatorAnalysis.radii (t.coarse.toStructural coarse_ratio)) ≤ I.mst / 200

variable {I : Instance (Fin n)} {label : Vector (Fin n) (k + 1)}
  {root : Fin (k + 1)} {t : Tables} {inverse : Vector (Fin (k + 1)) n}
  {bits : RuntimeWorld.Coordinate t k → Bool} {R : ℝ}

theorem terminals_list (hT : Finset.univ.image label.get = I.terminals) :
    label.toList.toFinset = I.terminals :=
  (PublicTerminals.toList_toFinset label).trans hT

theorem labels_list (label : Vector (Fin n) (k + 1)) :
    FiniteMST.labels label.get = label.toList.toFinset := by
  simpa only [FiniteMST.labels] using (PublicTerminals.toList_toFinset label).symm

theorem labels_list_native (label : Vector (Fin n) (k + 1)) :
    FiniteMST.labels label.get = @List.toFinset (Fin n) (instDecidableEqFin n) label.toList := by
  calc
    FiniteMST.labels label.get = label.toList.toFinset := labels_list label
    _ = _ := by ext x; simp only [List.mem_toFinset]

theorem retained_subset (i : Index t) : coarseRetained I t inverse bits i ⊆ I.terminals :=
  Finset.filter_subset _ _

theorem retained_cover (G : Geometry I label root t inverse bits R) (i : Index t) :
    CoverOn I I.terminals (coarseRetained I t inverse bits i)
      (EstimatorAnalysis.radii (t.coarse.toStructural G.coarse_ratio) i) := by
  exact (RuntimeWorld.coarse_good I label G.terminals t inverse G.inverse_left bits G.world i).1

theorem retained_mass (G : Geometry I label root t inverse bits R) :
    EstimatorAnalysis.mass (t.coarse.toStructural G.coarse_ratio) (coarseRetained I t inverse bits) ≤
      (A n : ℝ) * I.mst :=
  RuntimeWorld.coarse_mass I label G.terminals t inverse G.inverse_left bits G.world R
    G.radius_nonneg G.radius_le G.coarse_ratio G.coarse_height G.coarse_last

theorem band_retained_eq (hT : Finset.univ.image label.get = I.terminals) (i : Index t) :
    BandEstimator.retained bits t.coarse (fun j => RuntimeWorld.coarseKey t inverse j.val) label.toList i =
      coarseRetained I t inverse bits i := by
  unfold BandEstimator.retained BandEvaluation.retainedSet
  rw [terminals_list hT]

theorem band_mass_eq (hT : Finset.univ.image label.get = I.terminals)
    (hq : t.coarse.q = Structural.omega) :
    BandEstimator.mass bits t.coarse (fun j => RuntimeWorld.coarseKey t inverse j.val) label.toList =
      EstimatorAnalysis.mass (t.coarse.toStructural hq) (coarseRetained I t inverse bits) := by
  unfold BandEstimator.mass EstimatorAnalysis.mass
  apply Finset.sum_congr rfl
  intro i _
  rw [band_retained_eq hT]

theorem band_score_eq (hT : Finset.univ.image label.get = I.terminals)
    (hq : t.coarse.q = Structural.omega) :
    BandEstimator.totalSmallScore I bits t.coarse (fun j => RuntimeWorld.coarseKey t inverse j.val)
        label.toList (BandEstimator.publicData n (k + 1)) =
      totalSmallScore I (t.coarse.toStructural hq) (coarseRetained I t inverse bits)
        (EstimatorAnalysis.radii (t.coarse.toStructural hq)) (BQ n) := by
  unfold BandEstimator.totalSmallScore totalSmallScore
  apply Finset.sum_congr rfl
  intro i _
  unfold BandEstimator.target
  rw [band_retained_eq hT]
  change BandEvaluation.smallBandSum I (coarseRetained I t inverse bits i)
      (t.coarse.scale i.val) (deltaCoarse * t.coarse.scale i.val) tau (BQ n) =
    smallScore I (coarseRetained I t inverse bits i) (t.coarse.scale i.val)
      (deltaCoarse * t.coarse.scale i.val) (BQ n)
  simp only [BandEvaluation.smallBandSum, smallScore, smallRetained, ratio_casts.2.2.2]

theorem band_world (G : Geometry I label root t inverse bits R) :
    BandEstimator.WorldGood bits t.coarse label.get
      (fun i => RuntimeWorld.coarseKey t inverse i.val) label.toList I.mst := by
  constructor
  · intro i
    refine ⟨root, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, G.coarse_root i⟩
  · rw [band_mass_eq G.terminals G.coarse_ratio]
    exact retained_mass G

noncomputable def SavingBounds (I : Instance (Fin n)) (t : Tables)
    (inverse : Vector (Fin (k + 1)) n) (bits : RuntimeWorld.Coordinate t k → Bool)
    (i : Index t) (z : ℝ) : Prop :=
  0 ≤ z ∧ z ≤ savingOn I (coarseRetained I t inverse bits i)
      (t.coarse.scale i.val) (5 * t.coarse.scale i.val / 8) ∧
    savingOn I (coarseRetained I t inverse bits i)
        (t.coarse.scale i.val) (5 * t.coarse.scale i.val / 8) / 2 -
      eps n * (coarseRetained I t inverse bits i).card ≤ z

/-- The sole statistical/runtime assumption: the actual saving code succeeds
uniformly over every correct incoming cache and returns its updated correct cache. -/
def SavingContract (I : Instance (Fin n)) (t : Tables)
    (inverse : Vector (Fin (k + 1)) n) (bits : RuntimeWorld.Coordinate t k → Bool)
    (saving : Saving n k t) (epsilon : ℝ) : Prop :=
  ∀ i cache, Cache.Correct bits cache →
    1 - epsilon ≤ Code.valueProbability I.weight bits (saving i cache)
      (Code.SomeGood (fun zc => Cache.Correct bits zc.2 ∧ SavingBounds I t inverse bits i zc.1))

noncomputable def failureLedger (n : ℕ) (t : Tables) (epsilon : ℝ) : ℝ :=
  ((t.fine.intervals + 3 * (t.coarse.intervals + 1) : ℕ) : ℝ) * beta n +
    ((t.coarse.intervals + 1 : ℕ) : ℝ) * epsilon

end SteinerUpperBound.EstimatorFrontend.Analysis
