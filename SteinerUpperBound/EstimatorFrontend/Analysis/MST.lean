module

public import SteinerUpperBound.EstimatorFrontend.Analysis.Probability

@[expose] public section

namespace SteinerUpperBound.EstimatorFrontend.Analysis

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids Covers.Geometry
open scoped Classical

variable {n k : ℕ} {I : Instance (Fin n)} {label : Vector (Fin n) (k + 1)}
  {root : Fin (k + 1)} {t : Tables} {inverse : Vector (Fin (k + 1)) n}
  {bits : RuntimeWorld.Coordinate t k → Bool} {R : ℝ}

noncomputable local instance mstVertexDecEq : DecidableEq (Fin n) := Classical.decEq _
noncomputable local instance mstLabelDecEq : DecidableEq (Fin (k + 1)) := Classical.decEq _

theorem mst_success (G : Geometry I label root t inverse bits R)
    (cache : Cache (RuntimeWorld.Coordinate t k)) (hc : Cache.Correct bits cache) :
    1 - (t.fine.intervals : ℝ) * beta n ≤
      Code.valueProbability I.weight bits
        (EstimatorMST.withParameters (parameters n (k + 1)) label.get (RuntimeWorld.fineKey t inverse)
          t.fine label.toList root cache)
        (fun mst => MSTApproximation.CorrectInterval I nu mst ∧ Cache.Correct bits mst.cache) := by
  have henum : Finset.univ.image label.get = label.toList.toFinset :=
    (PublicTerminals.toList_toFinset label).symm
  have hf i (hi : i < t.fine.intervals) :=
    RuntimeWorld.fine_good I label G.terminals t inverse G.inverse_left bits G.world
      ⟨i, by omega⟩
  have hcover : ∀ i < t.fine.intervals, CoverOn I I.terminals
      (ComponentExplore.retained bits (RuntimeWorld.fineKey t inverse i) label.toList.toFinset)
        (deltaFine * t.fine.scale i) := by
    intro i hi
    simpa only [terminals_list G.terminals] using (hf i hi).1
  have hsize : ∀ i < t.fine.intervals,
      ((ComponentExplore.retained bits (RuntimeWorld.fineKey t inverse i) label.toList.toFinset).card : ℝ) ≤
        Hc n + 6 * coverTrials n * hopBudget n * I.mst / (deltaFine * t.fine.scale i) := by
    intro i hi
    simpa only [terminals_list G.terminals] using (hf i hi).2
  have hinterval := EstimatorMST.interval_failure I bits n label.get G.injective
    (RuntimeWorld.fineKey t inverse) t.fine R label.toList root cache hc henum
    (terminals_list G.terminals) (PublicTerminals.length_le label G.injective) G.fine_root
    G.fine_ratio G.fine_height G.radius_nonneg G.radius_le G.fine_last hcover hsize
    G.fine_first G.fine_diameter
  have hcache := EstimatorMST.cache_failure_zero I bits n label.get (RuntimeWorld.fineKey t inverse)
    t.fine label.toList root cache hc henum G.fine_root
  exact success_and_zero_failure I.weight bits
    (EstimatorMST.program n label.get (RuntimeWorld.fineKey t inverse) t.fine label.toList root cache)
    (MSTApproximation.CorrectInterval I nu) (fun mst => Cache.Correct bits mst.cache)
    ((t.fine.intervals : ℝ) * beta n) hinterval hcache

end SteinerUpperBound.EstimatorFrontend.Analysis
