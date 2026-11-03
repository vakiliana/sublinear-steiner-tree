module

public import SteinerUpperBound.EstimatorFrontend.Analysis.World

@[expose] public section

namespace SteinerUpperBound.EstimatorFrontend.Analysis

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids Covers.Geometry
open scoped Classical BigOperators
open BandCompleteness

variable {n k : ℕ} {I : Instance (Fin n)} {label : Vector (Fin n) (k + 1)}
  {root : Fin (k + 1)} {t : Tables} {inverse : Vector (Fin (k + 1)) n}
  {bits : RuntimeWorld.Coordinate t k → Bool} {R : ℝ}

noncomputable local instance recordsVertexDecEq : DecidableEq (Fin n) := Classical.decEq _
noncomputable local instance recordsLabelDecEq : DecidableEq (Fin (k + 1)) := Classical.decEq _

theorem records_correct (G : Geometry I label root t inverse bits R)
    (saved : EstimatorLoop.State (Index t) (RuntimeWorld.Coordinate t k))
    (hlog : saved.records.map EstimatorLoop.ScaleRecord.index =
      (List.finRange (t.coarse.intervals + 1)).reverse)
    (hrecords : ∀ r ∈ saved.records, SavingBounds I t inverse bits r.index r.saving)
    (upper That : ℝ) (hu : I.mst ≤ upper ∧ upper ≤ (1 + nu) * I.mst)
    (hb : 0 ≤ That ∧
      That ≤ totalSmallScore I (t.coarse.toStructural G.coarse_ratio) (coarseRetained I t inverse bits)
        (EstimatorAnalysis.radii (t.coarse.toStructural G.coarse_ratio)) (BQ n) ∧
      totalSmallScore I (t.coarse.toStructural G.coarse_ratio) (coarseRetained I t inverse bits)
        (EstimatorAnalysis.radii (t.coarse.toStructural G.coarse_ratio)) (BQ n) - That ≤
          Structural.sigma0 * I.mst / 1000) :
    GoodEstimate (2 - c) I.optimum
      (Estimation.output upper (EstimatorFrontend.summed t.coarse saved.records).value That QS QQ) := by
  obtain ⟨Z, _T, hZ, hsum, _hband⟩ := EstimatorLoop.complete_records saved.records hlog
    (fun i z _ => SavingBounds I t inverse bits i z) hrecords (fun i => t.coarse.scale i.val)
  have hg := EstimatorAnalysis.parameter_good_run I (t.coarse.toStructural G.coarse_ratio) G.covers
    (coarseRetained I t inverse bits) n (fun i => retained_subset i) (retained_cover G)
    (retained_mass G) G.phase Z hZ That upper hb hu
  have hs : (EstimatorFrontend.summed t.coarse saved.records).value =
      EstimatorAnalysis.savingEstimate (t.coarse.toStructural G.coarse_ratio) Z :=
    (EstimatorFrontend.totals_value t.coarse saved.records).trans hsum
  rw [hs]
  exact hg

theorem finish_value (m : Sym2 (Fin n) → ℝ) (bits : RuntimeWorld.Coordinate t k → Bool)
    (upper That : ℝ) (saved : EstimatorLoop.State (Index t) (RuntimeWorld.Coordinate t k))
    (F : Option ℝ → ℝ) :
    (EstimatorFrontend.finish t upper That saved).evaluate m bits (fun o => F o.value) =
      F (some (Estimation.output upper (EstimatorFrontend.summed t.coarse saved.records).value That QS QQ)) := by
  rw [EstimatorFrontend.finish, Code.evaluate_bind, EstimatorFrontend.totals_evaluates]
  rfl

theorem finish_success (G : Geometry I label root t inverse bits R)
    (saved : EstimatorLoop.State (Index t) (RuntimeWorld.Coordinate t k))
    (hlog : saved.records.map EstimatorLoop.ScaleRecord.index =
      (List.finRange (t.coarse.intervals + 1)).reverse)
    (hrecords : ∀ r ∈ saved.records, SavingBounds I t inverse bits r.index r.saving)
    (upper That : ℝ) (hu : I.mst ≤ upper ∧ upper ≤ (1 + nu) * I.mst)
    (hb : 0 ≤ That ∧
      That ≤ totalSmallScore I (t.coarse.toStructural G.coarse_ratio) (coarseRetained I t inverse bits)
        (EstimatorAnalysis.radii (t.coarse.toStructural G.coarse_ratio)) (BQ n) ∧
      totalSmallScore I (t.coarse.toStructural G.coarse_ratio) (coarseRetained I t inverse bits)
        (EstimatorAnalysis.radii (t.coarse.toStructural G.coarse_ratio)) (BQ n) - That ≤
          Structural.sigma0 * I.mst / 1000) :
    Code.valueProbability I.weight bits (EstimatorFrontend.finish t upper That saved)
      (Code.SomeGood (GoodEstimate (2 - c) I.optimum)) = 1 := by
  have hp : Code.SomeGood (GoodEstimate (2 - c) I.optimum)
      (some (Estimation.output upper (EstimatorFrontend.summed t.coarse saved.records).value That QS QQ)) :=
    ⟨_, rfl, records_correct G saved hlog hrecords upper That hu hb⟩
  unfold Code.valueProbability
  rw [EstimatorFrontend.finish, Code.evaluate_bind, EstimatorFrontend.totals_evaluates]
  simp only [Code.evaluate, Outcome.combine, Outcome.add, Outcome.pure, hp, ite_true]

end SteinerUpperBound.EstimatorFrontend.Analysis
