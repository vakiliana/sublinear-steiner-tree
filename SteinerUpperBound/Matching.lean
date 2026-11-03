module

public import SteinerUpperBound.Matching.Checks

/-!
# Local random-greedy matching on labeled loopless multigraphs

Main interfaces in `SteinerUpperBound.Matching.Graph`:

* `vertexOracle_eq_some_iff` identifies the exact sequential greedy matched copy.
* `expected_Q_le` bounds invocations of each fixed directed state, summed over
  separate fresh-cache roots. Cache hits are counted, not discarded.
* `expected_totalRequests_le` and `expected_vertexRequests_le` give independent
  uniform-root total and vertexwise cost accounts.
* `expected_weighted_requests_le` supports arbitrary fixed nonnegative
  directed-state costs.

Writing `N = card V + card E + 2`, all use the explicit budget
`8388610 * (1 + floor(log₂ N))³`. This is a soft-O bound, not a claim of the
paper's sharper logarithmic estimate. `DegreeShrink` through `DepthTail` prove
the required cubic-logarithmic stack tail by finite rank-swap averaging and
dyadic residual-line-graph paths, without importing an unproved parallel-MIS
theorem. `Rotation` constructs the rank rotations and proves their
image-plus-length injectivity. `Trace`, `Caching`, and `DoubleCounting`
account for invocation multiplicity and caches.
-/
