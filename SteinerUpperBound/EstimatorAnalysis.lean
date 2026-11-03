module

public import SteinerUpperBound.EstimatorAnalysis.Statistics
public import SteinerUpperBound.EstimatorAnalysis.GoodRun
public import SteinerUpperBound.EstimatorAnalysis.Parameters
public import SteinerUpperBound.EstimatorParameters.Setup.Correctness

/-!
# Intermediate deterministic estimator analysis

`deterministic_good_run` assumes only the concrete retained-cover, mass, phase-bad,
primitive saving-score, primitive band-score, and MST-interval good events. It invokes
the actual saving/band soundness and completeness theorems, derives both structural
statistic bounds, and invokes the proved structural negative-evidence theorem.
`parameter_good_run` specializes the actual public integer cutoff and accuracy.

`observed_flooring_transfer` transfers this estimate from the observed-radius floored
metric to the original optimum through the actual cleaned-tree flooring theorem.
Neither declaration is the unconditional probabilistic upper-bound theorem.

The imported `EstimatorParameters.setupProgram` executes literal arithmetic
instructions, a divide-by-two logarithm loop, and a two-bit integer-square-root loop.
Its exact configuration output, zero oracle queries, and linear-in-`ell` setup work
are proved without treating `parameters n k` as a free runtime computation.
-/

@[expose] public section
