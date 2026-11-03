module

public import SteinerUpperBound.BandEvaluation.Compiled
public import SteinerUpperBound.BandEvaluation.Sampling

/-!
# Exact small-component band evaluator

`BandEvaluation.program C a rho tau` takes only a public nodup component-ID
list and the observed scalar parameters. It queries the observed `C × V`
metric table, enumerates exactly `C.length^4` tuples, deduplicates each
four-point tuple in charged list scans, and ignores sets of size below two.
It never enumerates a powerset.

Each valid candidate is evaluated by two actual `FiniteMST.program` calls on
clipped/zeroed-clipped component matrices. Its one-center cost is computed by
actual MSTs on the selected set and on that set augmented by every public
center, with at most five vertices per call. Matrix lookups use only the
observed component rows; the extra-center diagonal is zero. The final result
is a charged maximum scan with baseline zero.

`program_correct` proves exact equality with `Band.score I C.toFinset a rho tau`
on the stated band-order condition. `program_bounds` gives `[0,3*a]` for
nonnegative `a,rho,tau`. `program_evaluates` identifies the concrete `run`;
`compiled_spec` proves the same facts for every compiled seed.

For `m = C.length`, the implementation makes at most `n*m` metric queries,
no retention queries or positive replies, and at most
`10^10*(n+1)*(m+1)^12` ordinary RAM work. This conservative fixed polynomial
already absorbs the logarithmic closure factor. All matrix construction,
sorting, Kruskal closure calls, tuple deduplication, center scans, arithmetic,
and extrema scans are instrumented; there is no runtime `Instance`, MST,
local-cost, band-score, or optimizer callback.

## Cached retained-point frontend

`frontend key a B terminals rho tau root cache` executes actual retained
component exploration. It returns zero for a component larger than `B`;
otherwise it runs the exact evaluator and returns `D/(3*a*|C|)` together
with the updated retention cache. `explore_complete_iff` proves the exact
size classification, and `frontend_compiled_spec` proves the normalized
score lies in `[0,1]`, preserves a correct cache, uses at most `B` new
positive replies, and has polynomial work. For a nodup public terminal
list its work is at most `8*10^10*n*(B+2)^12`.

The guarded `indexedCallback` also handles nonretained public labels,
allowing the checked `Covers.OracleProgram.Mean` sampler to be reused.
`uniform_component_mean` and `uniform_retained_mean_points` prove the
actual partition/fiber mean `smallBandSum/(3*a*g)`.
`sampling_clipped_budget` instantiates the shared cached iid/calibration
theorem: the clipped estimate `3*a*Estimation.lowerCount` is between zero
and `smallBandSum`, with loss at most `9*xi*a*g`, except with probability
at most `3*beta`. It includes sampler failures in that event.

`estimate_bounds` and `aggregate_bounds` give the deterministic genuine
calibration/sample-event versions. Summed scale mass at most `A*L` and
`xi ≤ Structural.sigma0/(100000*A)` yield aggregate loss at most
`Structural.sigma0*L/1000`. These are component-score and sampling
interfaces, not a claim that the full upper algorithm is assembled.
-/

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

end SteinerUpperBound.BandEvaluation
