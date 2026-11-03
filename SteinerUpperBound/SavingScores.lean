module

public import SteinerUpperBound.SavingScores.Parameters
public import SteinerUpperBound.SavingScores.GeneralParameters

/-!
# Actual retained-point saving scores

For a surjective finite point partition `part : X → A`, `partSize part a` is
the cardinality of its actual fiber. `sampleLaw` samples a uniform point,
an independent uniform labeled-copy rank order, and a Bernoulli initiation
coin of bias `1/partSize`. Rank orders are analysis seeds only: this module
does not claim that generating a full permutation is an efficient query
program or introduce an input-dependent runtime callback.

`pointScore` is `1/partSize` on covered components, half of the actual
`Matching.Graph.vertexOracle` matched indicator on initiated remaining
components, and zero otherwise. `pointScore_bounds` proves it lies in `[0,1]`.
`scoreMean_eq` proves the exact mean
`(covered.card + expectedMatching G) / Nat.card X`, using actual oracle/global
agreement, fiber counting, and the matching endpoint count.
`iid_score_deviation` applies the checked bounded-score sampling theorem.

`Z gminus empirical xi s` is exactly
`max 0 (Estimation.lowerCount gminus empirical xi - 2*s)`.
`capped_Z_contract` derives its soundness and the manuscript deletion-score
loss from the actual row system and the proved mutual-cap matching theorem.
`ordered_Z_contract` instantiates the first-`b` incident lists and actual
finite labeled-copy graph; its additive matching loss is
`order.toFinset.card / b`, not a supplied approximation certificate.

`ordered_large_branch_contract` uses the actual integer ceilings
`smallThreshold eps = ceil(10/eps)` and
`incidenceBudget nrows eps gminus = ceil(100*nrows/(eps*gminus))`.
With the stated calibration/empirical events, actual large-part fiber-size
bounds, `S.card ≤ s ≤ t`, `50*t/eps < Nat.card X`, and `xi ≤ eps/100`,
it proves `0 ≤ Z ≤ fullSaving` and `fullSaving/2 - eps*Nat.card X ≤ Z`.
The ceiling wrapper assumes a nonempty public row list.

## Arbitrary global strict-order laws

`sampleLawFor μ`, `expectedMatchingFor μ`, and `scoreMeanFor μ` replace the
uniform rank law by any finite `Law (Matching.Rank D)`. They retain the actual
uniform point, independent reciprocal-fiber Bernoulli initiation, and actual
`pointScore`/vertex-oracle semantics. `scoreMeanFor_eq` proves the same exact
fiber/endpoint-count formula, and `scoreMeanFor_bounds` and
`iid_score_deviationFor` give bounded-score sampling for this actual law.
The three `*_uniform` equalities recover the existing uniform interfaces.

`capped_Z_contractFor` accepts any labeled-copy graph `G` realizing the actual
mutual incidence graph, with arbitrary `μ` on the same physical copy ranks.
It derives the matching bounds from greedy maximality and the genuine cap;
it assumes no mean/saving certificate and does not collapse parallel copies.
`large_branch_contractFor` adds the integer-ceiling loss calculation for any
genuine cap. `ordered_Z_contractFor` and `ordered_large_branch_contractFor`
specialize only the incidence lists to the ordered first-`b` construction,
not the graph's copy labels or the rank distribution.

Thus integer ranks with deterministic lexicographic tie breaking need no
total-variation correction for these score/saving contracts, once their
actual global strict-order law is identified. Uniform/no-ties assumptions
may still be needed by separate expected local-oracle complexity results.
-/

@[expose] public section

namespace SteinerUpperBound.SavingScores

end SteinerUpperBound.SavingScores
