module

public import SteinerLowerBound.Simulation.Accounting
public import SteinerLowerBound.Simulation.Requests

@[expose] public section

/-!
# The actual visible-star simulator

`Simulation.Public.tree` compiles the shared unordered public-query model into
fresh candidate-membership queries. Its only private input is the sequence of
oracle replies; the permutation and fillers are its common-data parameters.
Each closure scan checks its cap before reading, caches all candidate answers,
and uses `2 * R + 1` fuel, proved sufficient by `Simulation.close_spec`.

`tree_valid`, `tree_actual_or_overflow`, and `tree_overflow_retained` give
pathwise validity, actual gated-transcript agreement, and deterministic overflow
accounting. `experimentTree` projects any finite observation of the full public
output/transcript. `experiment_projection_close_bound` bounds its distance from
the actual experiment, including all screening stops and closure overflow.
-/
