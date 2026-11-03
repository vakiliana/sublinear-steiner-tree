module

public import SteinerUpperBound.EstimatorParameters.Fixed
public import SteinerUpperBound.EstimatorParameters.Logarithms
public import SteinerUpperBound.EstimatorParameters.Grids
public import SteinerUpperBound.EstimatorParameters.Confidence
public import SteinerUpperBound.EstimatorParameters.Allowances
public import SteinerUpperBound.EstimatorParameters.Balance
public import SteinerUpperBound.EstimatorParameters.Scores
public import SteinerUpperBound.EstimatorParameters.Reusable
public import SteinerUpperBound.EstimatorParameters.Sampling
public import SteinerUpperBound.EstimatorParameters.LargeBranch
public import SteinerUpperBound.EstimatorParameters.CoverFamily
public import SteinerUpperBound.EstimatorParameters.Configuration
public import SteinerUpperBound.EstimatorParameters.Normalization

/-!
# Executable public estimator parameters

`parameters n k` contains natural-number budgets computed from integer square roots,
integer binary logarithms, and fixed arithmetic. Scalar accuracies are reciprocals of
the public integer denominators. No parameter constructor receives a metric instance.
`coarseHeight` and `fineHeight` run bounded rational first-crossing loops; only grid
scale values, not the tuning budgets, depend on the observed radius.

`grids_count` gives the actual uniform height bound. `simultaneous_cover_failure`
uses the concrete finite private-tape cover factory and has error at most `1/4000000`.
`A`, `AM`, and `coarse_mass_bound`/`fine_mass_bound` supply known positive cover-mass
allowances. `reusable_sample_ready` instantiates the actual rational reusable sampler.
`all_core_polylog` bounds all core budgets by the fixed `publicFactor * ell(n)^9`;
proposal caps and the reusable pool have sharper bounds.

`incidenceBudget_large_real` proves the observed rational incidence ceiling is
unclamped on a good large branch and has square at most `50*(n+1)`.
`balanced_integer_cost` gives the exact square-root balance.
`rootRow`, `normalize`, and their semantics observe the root radius by actual metric
queries and implement flooring by response translation without extra distance queries.
-/

@[expose] public section
