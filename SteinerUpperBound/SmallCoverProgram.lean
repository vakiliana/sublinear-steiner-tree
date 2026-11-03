module

public import SteinerUpperBound.SmallCoverProgram.Compiled

/-!
# Actual small-cover metric-query program

`program (N : List (Fin n)) a` takes only the already revealed retained list
and the observed scale. It has no `Instance`, metric callback, optimum, or
saving statistic as a runtime argument. The only private observations are
the `n*N.length` calls to `Code.metric` on retained-point/center pairs.
There are no retention queries, coins, or random-permutation generators.

The implementation converts `N` to a vector once, stores observed distances
in a dense vector, computes strict-`a` connectivity by logarithmically many
Boolean squarings, and finds the minimum-index root of each component.
For every center it marks near-component root IDs in a Boolean vector,
scanning retained points once; there is no per-center quadratic deduplication.
Greedy eligibility is computed from the ORIGINAL RETAINED components, with
radius `5*a/8`, before claims/deletions. A second linear vector scan counts
fresh components, and accepted rows claim their entire marked vector.
The returned number is the actual claimed count minus accepted-row count.

All allocations, nested connectivity loops, reads, comparisons, writes, row
marking, counting, and claiming are explicitly ticked under the RAM model.
Finite sets, connected-component cells, and `SetSystem.smallCoverEstimate`
occur only in the semantic proofs, not as uncharged runtime computations.

`program_evaluates` identifies the concrete deterministic `run`.
`program_agrees` proves equality with the actual retained-row
`SetSystem.smallCoverEstimate`; `program_guarantee` proves
`0 ≤ Z ≤ savingOn` and `savingOn/2 ≤ Z`.
For a nodup retained list, `run_queries` gives at most `n*g` metric queries,
`run_work` gives at most `128*(n*g + g^3*(1+Nat.log2(g+1)))` ordinary work,
and `run_resources` gives zero retention queries and positive replies.
`compiled_outcome` and `compiled_spec` establish the same claims for EVERY
seed/output of the actual `QueryProgram.Code.compile`, not just in expectation.

The stable reusable closure facade is
`SteinerUpperBound.SmallCoverProgram.Closure`. It independently exports the
actual dense-array closure program, bounded-walk correctness, exact
reachability, canonical-root partition facts, and RAM resource bounds.
-/

@[expose] public section

namespace SteinerUpperBound.SmallCoverProgram

end SteinerUpperBound.SmallCoverProgram
