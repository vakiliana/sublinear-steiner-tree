module

public import SteinerUpperBound.MSTApproximation.Grid
public import SteinerUpperBound.MSTApproximation.Components
public import SteinerUpperBound.MSTApproximation.Score
public import SteinerUpperBound.MSTApproximation.Quadrature
public import SteinerUpperBound.MSTApproximation.Mass
public import SteinerUpperBound.MSTApproximation.Interval
public import SteinerUpperBound.MSTApproximation.PointProgram
public import SteinerUpperBound.MSTApproximation.SamplingLaw
public import SteinerUpperBound.MSTApproximation.ScoresProgram
public import SteinerUpperBound.MSTApproximation.SamplerLaw
public import SteinerUpperBound.MSTApproximation.GridProgram
public import SteinerUpperBound.MSTApproximation.ScaleProgram
public import SteinerUpperBound.MSTApproximation.ScaleProbability
public import SteinerUpperBound.MSTApproximation.Frontend
public import SteinerUpperBound.MSTApproximation.ScaleResources
public import SteinerUpperBound.MSTApproximation.Correctness
public import SteinerUpperBound.MSTApproximation.FrontendResources
public import SteinerUpperBound.MSTApproximation.FrontendProbability
public import SteinerUpperBound.MSTApproximation.Parameters
public import SteinerUpperBound.MSTApproximation.Success
public import SteinerUpperBound.MSTApproximation.Configured

/-!
# Actual retained-cover MST interval preprocessing

`Grid.generate` and `gridProgram` use only public scalar data. The actual last index is the
first crossing of `4R`; `generated_endpoints` bounds its scale and logarithmic length.
`Grid.toStructural` specializes any such grid of ratio `Structural.omega`.

`coverSum_bounds` is proved from actual Kruskal edges and actual retained threshold components.
`pointScore_mean` and `retained_score_mean` establish the inverse-component-size sampling law.
`interval_correct_of_factory_sizes` derives the interval from concrete covers and factory-size,
calibration, and empirical events, rather than assuming an accurate MST estimate.

`frontend` executes the retained sampler, the metric component explorer, and the scalar
estimator. Its exact law is `frontend_law`; `frontend_interval_failure` bounds failure by
`grid.intervals * beta` on the explicit cover/size event. `frontend_expected_resources`
accounts for work and positive replies. `configuredPreprocessor` also constructs the
first-crossing fine grid and selects the public integer/accuracy budgets. No runtime
constructor takes an `Instance`, an MST-value callback, or a component callback.
-/

@[expose] public section
