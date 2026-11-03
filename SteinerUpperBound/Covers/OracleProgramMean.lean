module

public import SteinerUpperBound.Covers.OracleProgramMeanWorst

@[expose] public section

/-!
# Actual cached sample-and-average frontends

Namespace: `SteinerUpperBound.Covers.OracleProgram.Mean`.
The terminal count is `k+1`; `M` may be instantiated with `Sym2 V`.

## Runtime interface

```
Callback M Q U := U → Cache Q → Code M Q (ℝ × Cache Q)
program (query : Fin(k+1) → Q) (root : Fin(k+1)) (C s B : ℕ)
  (cache : Cache Q) (ξ : ℝ)
  (callback : Callback M Q (Fin(k+1))) : Code M Q (Result Q k s)
```

The actual `Sampler.program` is run once. If every row accepts, `scores` calls
the actual callback sequentially on its `s` labels, threading the returned
cache and charging additions, division, and calibration arithmetic. Otherwise
the result's `value : Option ℝ` is `none`; root fallbacks are not observations.
`sample` preserves the sampler's labels, stopping times, proposal count, and
cache at sampling completion. `cache` is the final callback cache.
`lower` and `upper` are computed by `Rejection.lowerEstimate`/`upperEstimate`
using the actual total proposal count. No instance, retained set, metric
closure, seed law, or analysis score function is a runtime input.

## Genuine one-call refinements

For finite seed type `A`, `KernelSpec callback m b kernel score` asks only:

* Every callback run from a correct cache returns a correct cache.
* For every correct incoming cache and real test `F`,
  ```
  (callback u cache).evaluate m b (fun o => F o.value.1) =
    (kernel u).expect (fun a => F (score u a)).
  ```

`kernel : U → Law A` and `score : U → A → ℝ` are analysis-only. This is a
per-call value-law refinement, independent of the incoming correct cache,
not an empirical-accuracy or saving certificate. Updates may depend on the
sampled score. `KernelSpec.of_deterministic` specializes to seed `Unit` and a
Dirac score; `of_compiled` and `of_deterministic_compiled` accept the usual
every-compiled-seed cache refinements. `runs_of_compiled` converts other
every-seed resource/refinement interfaces to operational ones.

`program_cache_correct` proves actual final-cache correctness. `scores_value`
and `iid_sumValue` prove fresh conditional-kernel composition by induction.
The single iid point/kernel law is
`pointKernel μ kernel = μ.bind (fun u => (kernel u).map (fun a => (u,a)))`.

## Mean law, concentration, and calibration

For fixed closed `m,b`, correct initial cache, and nonempty selected bits:

* `program_value` is the exact joint score/sampling-observation replay law.
* `program_value_close` compares every `[0,1]`-valued test of the optional
  actual mean with the iid empirical point/kernel mean. Its error is
  `capError = Pr[proposal overrun] + Pr[failed rejection row]`.
  `cappedAccepted_uniform_close` proves the same error after marking failed
  rows as `none`; it does not incur an extra row-failure penalty.
* `program_confidence h query root C s B cache hc hb ξ accuracy δ ...`
  uses the checked empirical Chebyshev theorem. If scores lie in `[0,1]`,
  `s>0`, `accuracy>0`, and `1 ≤ δ*s*accuracy²`, then mean/abort failure is at
  most `capError+δ`.
* With `0<β≤1`, `0<ξ≤1`, and the standard sampler parameters
  ```
  s = Rejection.calibrationSamples (β/2) ξ
  C = Rejection.proposalRowCap (k+1) s (β/2) ξ
  B = Rejection.proposalBudget (k+1) s β,
  ```
  `capError_budget` is at most `β`; `program_confidence_budget` bounds
  mean/abort failure at accuracy `ξ` by `2β`.
* `program_calibration_budget` separately bounds failure of the actual
  `Sampler.GoodRecord` by `β`. `program_sample` preserves this entire sampler
  marginal, independently of callback behavior.
* `program_lowerCount_budget` combines those marginal failures by a union
  bound: with probability at least `1-3β`, `CorrectLower g mean ξ result`
  holds. This supplies an actual empirical value and
  ```
  0 ≤ Estimation.lowerCount result.lower empirical ξ ≤ g*mean
  g*mean - Estimation.lowerCount result.lower empirical ξ ≤ 3*ξ*g.
  ```
  `g` is the selected cardinality and `mean` the actual point/kernel mean.
  Calibration bounds are the usual `(1-ξ)g ≤ lower ≤ g ≤ upper ≤ (1+ξ)g`.

The signatures write the count as `Fintype.card (Fin(k+1))`.
No uniformity is asserted after conditioning on calibration.

## Actual resource accounts

`program_expected` accepts genuine per-label expected callback work and
positive-reply bounds `w(u),p(u)`, uniform over correct incoming caches. It
proves for actual counters, with `μ` uniform on the retained labels:

```
E[work] ≤ 64*(E[actual sampler proposals]+s+1) + s*μ.expect w
E[positiveReplies] ≤ s + s*μ.expect p.
```

`cappedAccepted_expect_le` proves the nonnegative-cost domination needed here;
there is no cap-error multiplied by a worst-case callback cost.

`program_worst` proves, from genuine per-call bounds `W,P`, on every execution:
```
work ≤ 64*(actual sampler proposals+s+1) + W*s
positiveReplies ≤ (P+1)*s,    actual sampler proposals ≤ B.
```
`program_compiled_worst` accepts per-call every-seed bounds and gives the
budget `64*(B+s+1)+W*s`. `program_compiled_work` needs only callback work
bounds. `program_cap_evaluate` proves that this cap does not change values.
Positive replies bound newly disclosed positives; the backend's checked
`factory_positive_le`/prefix domination excludes initially cached true bits.

An entire adaptive estimator must still be wrapped **once** with
`factory_output_boolean_close`. These fixed-oracle kernel refinements must
not be replaced by blanket independence assumptions about coins depending
on the unknown retained set.
-/
