module

public import SteinerUpperBound.EstimatorMST.Program
public import SteinerUpperBound.EstimatorMST.Failure
public import SteinerUpperBound.EstimatorMST.Cache
public import SteinerUpperBound.EstimatorMST.Resources

/-!
# Fine MST preprocessing with public integer parameters

`EstimatorMST.withParameters` consumes an already-computed public configuration;
`program` specializes it to `EstimatorParameters.parameters n (k + 1)`. The terminal
enumeration has type `Fin (k + 1) → V`, so `k + 1` is the actual terminal count.
Neither runtime constructor takes a metric instance, MST value, or component oracle.

The fine quadrature executes exactly `List.range g.intervals`, excluding the last
endpoint. It is independent of the coarse saving/band loop, which uses all levels.
The caller supplies the genuinely generated fine grid and its first/last geometry.
On the actual retained-cover and factory-size events, `interval_failure` and
`interval_failure_factory_size` bound interval failure by `g.intervals * beta n`.
Their mean, calibration, cutoff, and proposal budgets are proved from the public
integer configuration, and the retained-cover mass allowance is derived internally.

`cache_on_support` preserves truthful cache entries without any cover/accuracy event.
`expected_resources` gives the explicit executed-loop accounting.
`expected_resources_polylog` bounds expected ordinary work by
`workFactor * (n + 1) * ell n ^ 36` and expected positive replies by
`positiveFactor * ell n ^ 27`, for fixed absolute natural factors.
-/

@[expose] public section
