module

public import SteinerUpperBound.ReusableSample.OracleProgram

@[expose] public section

/-!
# A reusable sample for fixed ordered rows

`SteinerUpperBound.ReusableSample.reusable_sample` proves the pool lemma for
the actual live-record logistic procedure. Its inputs are a fixed vector
`R : Fin n → Finset U`, a positive acceptance limit `t`, and `0 < β < 1/4`.
The output law `run` returns only `Fin n → Bool`; row order and row contents
cannot depend on the sampled records.

Put `L = 1 + log (512t/β)` and `M = 1 + log (128(n+1)t/β)`.
The explicit parameters are
`bandwidth t β = 1 / log (1 + 1/(64L))` and
`sampleSize n t β = ceil (512tLM)`.
`bandwidth_bounds` proves `64L ≤ b ≤ 128L`. The main theorem proves success
probability at least `1-β`, at most `t` accepted rows on every supported
transcript, at most `n * sampleSize n t β` membership tests on every path,
and the sample bound `sampleSize n t β ≤ 512tLM + 1`.

`Specification` states both true-cardinality guarantees. `mem_previousUnion`
identifies its fresh part as the row minus earlier selected rows;
`finalUnion_eq_biUnion` identifies its final cover with the selected rows.

The proof uses a finite survival induction (`Tree.Addition.reverse`),
replacement through an absent record (`mechanism_stable`), finite
hockey-stick posterior transfer (`Probability.posterior_transfer`), and
conditional empirical margins (`correctness`). The forward addition
comparison is exact, slightly improving the usual stability composition
constant. No stability or generalization hypothesis remains in the main
theorem.

## Integer calibration and compilation

For integer budgets `Lbar ≥ logBudget t β`, `Mbar ≥ rowBudget n t β`,
`integerSamples t Lbar Mbar = 512*t*Lbar*Mbar` is exactly divisible by `t`
(`integerSamples_div`). `integer_reusable_sample` proves the same guarantees
with bandwidth `calibratedBandwidth Lbar`; `calibratedBandwidth_le` gives
the sharper bound `b ≤ 64*Lbar + 1`. The more general
`reusable_sample_of_budgets` permits any integer sample size above `512*t*L*M`.

The compiler-facing output law is `rationalRun`, and its complete guarantee
is `integer_reusable_sample_rational` in
`SteinerUpperBound.ReusableSample.MembershipMatrix`. Its definition contains
no exponential or logarithm. In `SteinerUpperBound.ReusableSample.Rational`,
`logistic_integer_rule` identifies each decision probability with
`1/(1+z^e)`, where `z = 1+1/(64*Lbar)` and
`e = 2*(Ns/t)-c : ℤ`. `rationalProbability` computes this value in `ℚ`.

`SteinerUpperBound.ReusableSample.Arithmetic` supplies `fastProbability`,
using repeated squaring, and proves both its exact value and the bound
`fastProbabilityWork ≤ 6*(Nat.log2 (Ns+1)+2)+16` for `c ≤ Ns`.
This counts arithmetic/comparison operations, not bit operations.
The doubling variants of the main theorems need only the arithmetic tests
`512*t ≤ β*2^k`, `128*(n+1)*t ≤ β*2^ℓ`, and use budgets `k+1`, `ℓ+1`.

`mechanism_eq_matrix` factors the actual procedure through the Boolean
`membershipMatrix R X`; `mechanism_eq_rationalMatrix` also eliminates the
analytic transition rule. `mechanism_ext` permits entirely different
record/universe types with the same membership matrix and has no `Fintype`
or `Nonempty` requirement on either universe. The work counters factor
through the same matrix (`queryWork_eq_matrixWork`, `queryWork_ext`).
Thus all universe membership queries may be read before running the
bitmap-only `matrixTree`.
-/
