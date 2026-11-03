module

public import SteinerUpperBound.BandEstimator.World
public import SteinerUpperBound.BandEstimator.Cache

/-!
# Actual multiscale band estimator

`Index g = Fin (g.intervals + 1)` includes every coarse level, including the
last endpoint. `program g label key root terminals data cache` sequentially
runs the actual cached rejection sampler/mean helper and the actual
`BandEvaluation` component/MST frontend at each level. It computes
`3*a*Estimation.lowerCount`, accumulates these clipped estimates, and returns
`Option ℝ × Cache Q`. A failed stage propagates `none`; it is not replaced
by an observation. Scale multiplications, index-list construction, clipping,
addition, and the underlying metric/retention operations are charged.

`fromParameters` takes the public integer `EstimatorParameters.PublicParameters`
record. For terminal count `k+1`, `ofParameters_eq` identifies its data with
`publicData n (k+1)`: cutoff `BQ n`, reciprocal denominator `xiBandInv n`,
`meanSamples n (xiBandInv n)`, and row cap
`samplerCap n (k+1) (xiBandInv n)`. The total proposal budget is the integer
`16*(k+1)*(samples+betaDenom n)`. Runtime inputs contain no metric instance,
retained set, score law, or score/correctness callback.

## Refinement and probability

`lowerCount_public` derives the actual mean/calibration contract from these
integer parameters and the shared genuine callback-kernel theorem.
`stage_failure_public` loses at most `3*beta n` and proves the actual clipped
estimate is in `[0,target]`, with loss at most `9*xi*a*|N|`.

`WorldGood` asks only that the actual retained rows are nonempty and their
actual all-level mass is at most `A n * L`. On this event, `program_success`
and `fromParameters_success` give probability at least
`1-3*beta n*(g.intervals+1)` for `GoodOutput`: a returned value in
`[0,totalSmallScore]` with loss at most `Structural.sigma0*L/1000`, and a
correct final cache. The bound is uniform over every correct incoming cache;
no calibration conditioning or inter-scale independence is assumed.
`*_averaged_success` subtracts the genuine `WorldGood` failure probability
under any finite cover-world law with cache consistency on its support.
The actual cover factory and the mass theorem are instantiated by the caller.

## Unconditional resource and cache accounts

Let `K = core n = (EstimatorParameters.coreSizes n).sum + 1`.
For a nodup public terminal list, injective enumeration, and the actual
height bound `g.intervals+1 ≤ heightBudget n`:

* `stage_public_expected` bounds ordinary work by
  `2*10^11*(n+1)*(K+2)^13` and positive replies by `(K+2)^2`.
* `program_public_expected` and `fromParameters_expected` bound the totals by
  `10^12*(n+1)*(K+2)^14` and `(K+2)^3`.
* `*_compiled_resources` prove these total bounds on every compiled execution.

These accounts require no cover/mass/calibration good event.
`*_averaged_resources` therefore remain unconditional under the actual
cache-consistent cover law. `program_cache_frame` and
`fromParameters_cache_frame` preserve every previously known bit and agree
with the incoming cache outside the actual coarse terminal-query family,
even on failed executions. No full-estimator or factory-clock theorem is
claimed here.
-/

@[expose] public section
