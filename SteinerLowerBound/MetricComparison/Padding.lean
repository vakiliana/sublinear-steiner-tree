module

public import SteinerLowerBound.MetricComparison.Padding.Protocol

@[expose] public section

/-!
# Public far-point padding

`Padding.optimum_padding` proves equality of the actual selected-center Steiner
optima, by contracting every padding vertex to a fixed ordinary terminal and
extracting a spanning tree of no larger cost. Padding centers have empty
neighbor sets.

`Padding.queryReduction.simulateOutput` removes publicly identifiable padding
queries. `simulate_public_output`, `simulate_public_queries`,
`simulate_public_bounded`, and `simulate_public_noRepeats` prove exact output
agreement without increased query cost. `simulate_public` additionally returns
the complete original padded transcript, including the deterministically
answered padding queries.
-/
