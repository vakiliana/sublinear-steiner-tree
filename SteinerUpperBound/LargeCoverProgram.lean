module

public import SteinerUpperBound.LargeCoverProgram.Cache
public import SteinerUpperBound.LargeCoverProgram.Statistics
public import SteinerUpperBound.LargeCoverProgram.PoolLaw
public import SteinerUpperBound.LargeCoverProgram.Saving
public import SteinerUpperBound.LargeCoverProgram.Confidence
public import SteinerUpperBound.LargeCoverProgram.PoolResidual
public import SteinerUpperBound.LargeCoverProgram.PointResources
public import SteinerUpperBound.LargeCoverProgram.MeanResources
public import SteinerUpperBound.LargeCoverProgram.SmallResources
public import SteinerUpperBound.LargeCoverProgram.CanonicalCache
public import SteinerUpperBound.LargeCoverProgram.Shape
public import SteinerUpperBound.LargeCoverProgram.Concrete
public import SteinerUpperBound.LargeCoverProgram.CausalCache
public import SteinerUpperBound.LargeCoverProgram.Normalization
public import SteinerUpperBound.LargeCoverProgram.PointCounters
public import SteinerUpperBound.LargeCoverProgram.PointNormalization

@[expose] public section

/-!
# Actual per-scale saving frontend

Namespace `SteinerUpperBound.LargeCoverProgram`.

`program p terminals root key a vo cache` has type
`Code (Sym2 (Fin n)) Q (Answer Q n)`. Parameters are public integer/rational
budgets; `vo D d frame cache` is actual causal matching code, with the newly
observed deletion bitmap `D`. No instance,
retained set, partition, optimum, or saving-function callback is a runtime
argument.

The program calibrates with the checked cached sampler. Its observed upper
estimate chooses between guarded full revelation/small-cover greedy and a
fresh sample/reusable-pool/D-bitmap/actual point-mean computation. Failed
rejection rows and proposal aborts return `none`. The small-size guard and
incidence-cap clamp are executable and prevent bad calibrations from causing
unbounded allocations.

Stable interfaces:
* `program_cache` / `program_cache_canonical`: optional stronger all-`Runs`
  cache wrappers. The actual runtime uses the positive-support guarantees below,
  so zero-mass counterfactual branches impose no extra invariant obligation.
* `point_value`, `point_kernelSpec`: actual conditional score law.
* `point_approxKernelSpec`: explicit per-call VO TV/bad-call error.
* `afterCovered_confidence`: actual empirical confidence, including `s*delta`.
* `program_saving_confidence`: actual scalar soundness/half-approximation with
  explicit calibration, sampler-cap, reusable-pool, VO-TV and mean failures.
  Its only algorithmic refinement premise is a one-call Boolean VO law.
* `program_concrete_saving_confidence`: discharges even that premise using the
  ACTUAL `PortGraph.RuntimeAdapter.builder` and its checked `Runtime.answer`.
  The rank law retains every physical parallel port copy; explicit tie/TV
  loss is `meanSamples*concreteVOError`.
* `program_concrete_cache_ensures` / `program_concrete_cache_failure_zero`:
  actual returned-cache correctness on positive support. Neither assumes an
  invariant on zero-mass counterfactual branches.
* `calibrated_large_budget`: proves the public incidence clamp inactive.
* `deletion_pool_failure`: real sampler cap error plus the checked pool error.
* `poolGood_residual`: transports the pool to TRUE ambient residual cardinality.
  `poolGood_accepted_fresh` likewise proves every accepted TRUE fresh size.
* `deletion_cache_resources`: actual sample/pool/compaction/D resources.
* `program_shape`: pathwise selection count <=t, list/count agreement,
  uniqueness and exact D fidelity, without any VO refinement assumption.
* `small_contract`: the actual guarded small-cover saving contract.
* `small_resources`: public guarded work and true-retained-size disclosures.
* `point_expected`: ACTUAL initiation-weighted VO resource account; no assumed
  point-work certificate. `mean_expected_cache` composes actual callback costs
  without assuming exact value kernels.
* `point_clipped_expected`: the analogous paired min(work,T)/min(positives,T)
  bounds for genuine clipped/original-Good resource composition. Arbitrary joint
  counter tests are transported by `point_counter_test`, without seed matching.
  `point_clipped_average` converts genuine arbitrary-root-cache VO clipped
  bounds into ACTUAL uniform-retained-point bounds, including eager caches.
* `initiatedRootCharge_mean(_uniform)`: exact component-to-point normalization,
  multiplying by m/g only AFTER uniform residual-root averaging. Empty residual
  vertex types contribute zero without a fictitious uniform law.
* `initiatedPointCharge_family_bound`: the same normalization for arbitrary
  point-dependent incoming cache families, using genuine partition fibers.
  `_family_average_bound` directly consumes already g-normalized original-code
  counter bounds without dividing by m or requiring a nonempty residual graph.
  `initiated_model_goodCost_le` instantiates the checked closed log8 model
  budget without misidentifying completed priorities as original code seeds.
* `pointMean_eq_scoreMeanFor`, `large_score_contract`: arbitrary strict-rank
  laws on unchanged physical copies, using actual finite matching bounds.

Sampling/calibration failures are marginal statements, never claims of
uniformity conditional on a calibration or future cheap-execution event.
Resource composition keeps ACTUAL VO counter expectations explicit. It does
not assert inexpensive unconditional work on bad pool/rank branches; the
parent's genuine paired clocks can use separately proved good-prefix or
truncated accounts.
-/
