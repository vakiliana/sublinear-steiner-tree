module

public import SteinerUpperBound.Covers.OracleProgramSamplerSupport

@[expose] public section

/-!
# Causal metric-query retention factories and retained-point sampling

All interfaces below are in `SteinerUpperBound.Covers.OracleProgram`; sampler
interfaces are in its `Sampler` namespace. The terminal count is `k+1`.

## Runtime inputs and aborts

`Config V Q k` contains only public arrays `label : Fin(k+1) → V`,
`target : Q → Fin(k+1)`, `radius : Q → ℝ`, and private scan caps/trial counts.
There is no `Instance`, latent metric, or unknown neighborhood callback.
`factory cfg cache W D p` handles the genuine frontend `Code (Sym2 V) Q R`,
after its work cap `p.cap W`, with at most `D` private proposals.

On a cache miss the code generates one fresh uniform proposal at a time.
A target hit returns true without a metric call. Otherwise it issues the
actual pair-distance query, compares the returned answer with the public
radius, and counts near non-target hits. Per-coordinate exhaustion returns
false; global draw exhaustion aborts. Frontend metric, uniform, coin, and tick
nodes stay in their causal order. Only the resolved bit reaches a frontend
retention continuation.

The result is `Result Q (Option R)`: `value = none` is global factory abort;
`value = some none` is frontend-work abort. `value.join` flattens both aborts.
The returned state records the actual draw count, cache, newly disclosed true
bits, and logical frontend positive replies. Initial true cache entries are
not charged again. Public arrays/caches have constant-time indexed access in
the RAM model; explicit ticks charge comparisons, arithmetic, and bookkeeping.

## Exact factory semantics and resources

* `factory_resources cfg m b cache W D p seed` proves, for every compiled
  execution, `metricQueries ≤ W+D`, `work ≤ 32*(W+D+1)`, and
  `retentionQueries = 0`. The remaining oracle argument `b` is unused.
  `factory_draw_balance` proves `draws + remaining = D`;
  `factory_positive_le` proves `newPositive ≤ frontPositive`.
* `factory_compiled_evaluate cfg m b cache W D p F` identifies actual runtime
  expectations with `treeValue` averaged over `(p.cap W).compile m`.
  `compile_handler` handles adaptive coins; `treeValue_capped_law` identifies
  each seed's law with the existing actual cached/global factory interpreter.
* `factory_joint_pending_tail` proves
  `Pr[pending ∧ newPositive ≤ a] ≤ exp(a-D/(2*(k+1)))`.
  `factory_pending_bound` bounds pending probability by the uncapped
  frontend's positive-reply tail under `bits cfg m cache`, plus that
  exponential. `factory_pending_budget` replaces the exponential by `ε`
  when `D ≥ 2*(k+1)*(a+log(1/ε))`. Completion-prefix domination is proved,
  not assumed or conditioned on a future cheap event.
* `factory_option_boolean_close` compares arbitrary Boolean events on the
  entire optional result with the product-bit frontend; its error is the
  actual pending probability. `factory_output_boolean_close` flattens both
  abort kinds. They require no `Fintype R`, so real outputs are allowed.

`m`, `relation`, finite tapes, complete bit vectors, and compiled seed tables
are analysis-only. Runtime code never generates complete tapes upfront.
`bits` is the actual capped coordinate law with the initial cache forced;
the existing `Factory.cached_bits_ideal_close` separately handles its distance
from the ideal independent retention law.

## Actual capped retained-point sampler

`Sampler.program query root C s B cache` performs cached membership resolution
on fresh uniform proposals. It returns `s` labels, per-row stopping counts,
the total proposal count, and a success flag; proposal exhaustion yields
`labels = none`. A failed local rejection row is marked unsuccessful and uses
the public root fallback, as in the checked finite reference implementation.

* `Sampler.program_resources` proves, for every execution, zero metric calls,
  retention queries at most actual proposals, positive replies at most `s`,
  work at most `16*(actual proposals+s+1)`, and proposals at most `B`.
* `Sampler.program_output_evaluate` is exact equality with
  `Rejection.cappedPoolTree`; `pool_evaluate_replay` also preserves actual
  stopping/proposal counters.
* `Sampler.program_uniform_budget` proves marginal distance at most `β` from
  iid uniform-retained labels, for each fixed oracle and correct initial
  cache. `Sampler.program_calibration_budget` proves marginal cap/calibration
  failure at most `β`, using the actual total proposal count. Its
  `GoodRecord` predicate includes the checked lower/upper size estimates
  `Rejection.lowerEstimate` and `upperEstimate`.
* These use
  `s = Rejection.calibrationSamples (β/2) ξ`,
  `C = Rejection.proposalRowCap (k+1) s (β/2) ξ`,
  `B = Rejection.proposalBudget (k+1) s β`, and `W=16*(B+s+1)`;
  the Lean signatures write the count as `Fintype.card (Fin(k+1))`.
* `Sampler.factory_sampler_resources` includes the factory's actual query/work
  bounds, `newPositive ≤ s`, and `draws ≤ D` for every compiled execution.
  `factory_sampler_pending` gives `exp(s-D/(2*(k+1)))`, and
  `factory_sampler_pending_budget` supplies its explicit `ε`-budget form.
* `Sampler.factory_sampler_uniform_output` proves total output-law distance at
  most `β + exp(s-D/(2*(k+1)))` from the product-bit mixture of iid uniform
  retained labels. All aborts are mapped to `none`.

Calibration and uniformity are separate marginal statements; neither is
conditioned on the other. For an entire adaptive estimator, use
`factory_output_boolean_close` on that entire frontend rather than treating
the sampler's marginal label-mixture statement as conditional independence.
-/
