module

public import SteinerUpperBound.Matching.Padded.RuntimeTruncatedCost

/-!
# Actual padded local matching access

`Runtime.answer` is the causal implementation: only sampled padded slots are
tested, reverse-endpoint priorities are shared, discovered buckets are really
sorted, and directed matching answers are memoized.  Both vertex and copy
identifiers are ambient names; `Presentation` supplies proof-only embeddings.

The primitive premises are `Contract`, `Deterministic`, and `Resources`.
They concern only genuine preparation/slot values, persistent primitive memory,
and per-primitive counters.  No matching, rank-depth, call, or whole-VO resource
bound is an input.

For `h = floor(log₂ Nstar) + 1`, the exported interfaces are:

* `Presentation.answer_mean_error` / `answer_event_error`: the actual Boolean
  law is within `Nstar⁻³⁰` of global greedy matching with a uniform strict order
  of the same labeled parallel copies.  Integer-priority collisions are charged
  explicitly, not silently conditioned away.
* `Presentation.family_answer_counter_tail`: actual counter tail at threshold
  `t > 0` is at most `Nstar⁻³⁰ + 2⁶⁴ h⁸ publicPrice / t`.
* `Presentation.family_answer_original_good_failure` /
  `family_answer_original_good_cost`: on the original compiled program seeds,
  failure is at most `Nstar⁻³`, and good counter expectation is at most
  `2¹²⁸ h⁹ publicPrice`.  The event is the actual counter being at most
  `Cstar * 2^(100 + 20h)`, not an auxiliary posterior-rank event.

Here `publicPrice = Cstar * (1 + p/m) + (sum_v W_v)/m`, with every padded slot
included in `W_v`.  The resource interfaces average nonempty true-vertex roots
and allow a separate correct incoming primitive cache/frame for every root.
The empty-root case makes no oracle call.  Work and disclosure counters may be
instantiated separately and their original-seed good events intersected.
These are good-seed/clock-compatible accounts, not an unconditional inexpensive
execution claim on exceptional seeds.
-/
