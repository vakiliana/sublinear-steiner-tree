module

public import SteinerUpperBound.EstimatorFrontend.Analysis.Probability
public import SteinerUpperBound.EstimatorFrontend.Analysis.Loop
public import SteinerUpperBound.EstimatorFrontend.Analysis.MST

/-!
# Probability correctness of the executed frontend

`Analysis.program_success` analyzes `EstimatorFrontend.program` with the actual
public integer parameters. `Geometry` contains only enumeration/inverse facts,
the genuine `RuntimeWorld.Good` event, retained-root bits, and first/last/grid/phase
geometry. The only subroutine assumption is `SavingContract`: the supplied saving
CODE returns its primitive saving bounds and a correct cache, uniformly over every
correct incoming cache. No accurate MST interval, band estimate, or final numerical
correctness is supplied.

The proof invokes `EstimatorMST.interval_failure` and `cache_failure_zero`, derives
the actual all-coarse-level mass using `RuntimeWorld.coarse_mass`, identifies the
band module's retained sets and `totalSmallScore`, and invokes the actual
`BandEstimator.fromParameters_success`. `EstimatorLoop.complete_records` converts
the executed reversed FinRange log into finite-indexed primitive observations.
The charged totals are their actual weighted sum; `EstimatorAnalysis.parameter_good_run`
then proves the emitted estimate is good.

All stages are composed causally through correct incoming caches. Fine MST uses
`t.fine.intervals` levels, whereas saving and band use all `t.coarse.intervals+1`
levels. Writing these counts as `HF,HC`, the exact failure ledger is
`(HF+3*HC)*beta n + HC*epsilonSaving`. `program_failure` counts both `none` and
incorrect returned values; `withParameters_success` accepts an already-computed
record equal to `parameters n (k+1)`.
-/

@[expose] public section

namespace SteinerUpperBound.EstimatorFrontend.Analysis

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

variable {n k : ℕ} {I : Instance (Fin n)} {label : Vector (Fin n) (k + 1)}
  {root : Fin (k + 1)} {t : Tables} {inverse : Vector (Fin (k + 1)) n}
  {bits : RuntimeWorld.Coordinate t k → Bool} {R : ℝ}

noncomputable local instance analysisVertexDecEq : DecidableEq (Fin n) := Classical.decEq _
noncomputable local instance analysisLabelDecEq : DecidableEq (Fin (k + 1)) := Classical.decEq _

/-- Actual causal frontend success. Fine-MST and band correctness are derived from
their executed integer-parameter programs; only the per-scale saving CODE contract
is supplied. No incoming cache is sampled independently of previous stages. -/
theorem program_success (G : Geometry I label root t inverse bits R)
    (saving : Saving n k t) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hs : SavingContract I t inverse bits saving epsilon)
    (cache : Cache (RuntimeWorld.Coordinate t k)) (hc : Cache.Correct bits cache) :
    1 - failureLedger n t epsilon ≤
      Code.valueProbability I.weight bits
        (EstimatorFrontend.program (parameters n (k + 1)) label root t inverse saving cache)
        (Code.SomeGood (GoodEstimate (2 - c) I.optimum)) := by
  have hm := mst_success G cache hc
  have hn (mst : MSTApproximation.IntervalAnswer (RuntimeWorld.Coordinate t k))
      (hg : MSTApproximation.CorrectInterval I nu mst ∧ Cache.Correct bits mst.cache) :
      1 - (((t.coarse.intervals + 1 : ℕ) : ℝ) * epsilon +
        3 * beta n * ((t.coarse.intervals + 1 : ℕ) : ℝ)) ≤
      Code.valueProbability I.weight bits
        (EstimatorFrontend.afterMST (parameters n (k + 1)) label root t inverse saving mst)
        (Code.SomeGood (GoodEstimate (2 - c) I.optimum)) := by
    simpa only [sub_add_eq_sub_sub] using afterMST_success G saving epsilon he hs mst hg
  have h := Code.bind_success I.weight bits
    (EstimatorMST.withParameters (parameters n (k + 1)) label.get (RuntimeWorld.fineKey t inverse)
      t.fine label.toList root cache)
    (EstimatorFrontend.afterMST (parameters n (k + 1)) label root t inverse saving)
    (fun mst => MSTApproximation.CorrectInterval I nu mst ∧ Cache.Correct bits mst.cache)
    (Code.SomeGood (GoodEstimate (2 - c) I.optimum))
    ((t.fine.intervals : ℝ) * beta n)
    (((t.coarse.intervals + 1 : ℕ) : ℝ) * epsilon +
      3 * beta n * ((t.coarse.intervals + 1 : ℕ) : ℝ))
    (by have hb := (beta_bounds n).1; positivity)
    (by have hb := (beta_bounds n).1; positivity) hm hn
  change _ ≤ Code.valueProbability I.weight bits
    ((EstimatorMST.withParameters (parameters n (k + 1)) label.get (RuntimeWorld.fineKey t inverse)
      t.fine label.toList root cache).bind
      (EstimatorFrontend.afterMST (parameters n (k + 1)) label root t inverse saving)) _
  convert h using 1
  unfold failureLedger
  push_cast
  ring

theorem program_failure (G : Geometry I label root t inverse bits R)
    (saving : Saving n k t) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hs : SavingContract I t inverse bits saving epsilon)
    (cache : Cache (RuntimeWorld.Coordinate t k)) (hc : Cache.Correct bits cache) :
    (EstimatorFrontend.program (parameters n (k + 1)) label root t inverse saving cache).probability
      I.weight bits {o | ¬ Code.SomeGood (GoodEstimate (2 - c) I.optimum) o.value} ≤
        failureLedger n t epsilon :=
  failure_of_success I.weight bits _ _ _ (program_success G saving epsilon he hs cache hc)

theorem withParameters_success (G : Geometry I label root t inverse bits R)
    (p : PublicParameters) (hp : p = parameters n (k + 1))
    (saving : Saving n k t) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hs : SavingContract I t inverse bits saving epsilon)
    (cache : Cache (RuntimeWorld.Coordinate t k)) (hc : Cache.Correct bits cache) :
    1 - failureLedger n t epsilon ≤
      Code.valueProbability I.weight bits (EstimatorFrontend.program p label root t inverse saving cache)
        (Code.SomeGood (GoodEstimate (2 - c) I.optimum)) := by
  subst p
  exact program_success G saving epsilon he hs cache hc

end SteinerUpperBound.EstimatorFrontend.Analysis
