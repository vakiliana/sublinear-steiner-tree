# Steiner-tree distance-query bounds in Lean

This project formalizes both main results of
[`Submission/tight-main.tex`](../Submission/tight-main.tex): the distance-query
lower bound and the randomized sublinear approximation algorithm. The manuscript's
original text and its blue `\lean{...}` annotations about the lower-bound
formalization are preserved.

## Build

Lean and mathlib are pinned to **v4.35.0**. `lake-manifest.json` records the exact
dependency revisions. With elan installed:

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd Formalization
lake exe cache get
lake build
lake env lean Audit.lean
```

The cache command is only needed when obtaining dependencies on a fresh checkout.
Build artifacts and downloaded dependencies live in the ignored `.lake/` directory.

## Main results

### Lower bound

Import `SteinerLowerBound`.

- `SteinerLowerBound.lower_bound`: for every `0 < eta < 1` and natural `s`,
  positive constants exist such that, for every sufficiently large `n`, every
  successful randomized `(2-eta)`-approximation estimator needs more than
  `kappa * n^((3*s+7)/(2*s+5))` expected distance queries on some constructed
  `n`-point metric.
- `SteinerLowerBound.epsilon_lower_bound`: the corresponding
  `Omega(n^(3/2-epsilon))` result for every positive `epsilon`.

The first theorem includes, in particular, every integer `s >= 1` from the paper.
`Exponents.lowerExponent_eq` identifies its exponent with
`3/2 - 1/(4*s+10)`.

The theorem constructs `HardInstance` families. Their `Geometry` property proves:

- Exactly `n` points and between `n/D` and `n` terminals, for a fixed positive `D`.
- Actual metric-space axioms and exact agreement of the real distance oracle
  with that metric.
- Every off-diagonal distance belongs to `{ell, 1, 2}`, with
  `1/n^3 <= ell <= D^3/n^3`.

`HardInstance.optimum` is the actual minimum over selected Steiner vertices and
spanning trees, not a surrogate cost expression. Relabeling and far-center
padding preserve that optimum by proved tree transformations.

`HardInstance.Hard` quantifies over adaptive decision-tree algorithms with
real-valued distance answers and estimates. Repeated queries are allowed.
Random seeds range over arbitrary measurable probability spaces; only the
query-count and output functions must be measurable. Expected query counts use
the extended nonnegative integral, so infinite expectations are included.
Success means `OPT <= estimate <= (2-eta)*OPT` with probability at least `2/3`
on every member of the hard family. Consequently, an estimator correct on
every metric must satisfy the lower bound.

### Algorithmic upper bound

Import `SteinerUpperBound`.

- `SteinerUpperBound.algorithm`: the actual randomized metric-query estimator,
  taking only the public terminal-label vector on `Fin n`.
- `SteinerUpperBound.upper_bound`: for every genuine metric and valid injective
  terminal enumeration, its output satisfies
  `OPT <= estimate <= (2-eta0)*OPT` with probability at least `2/3`, where
  `eta0 = 1/(2*10^12) > 0`.
- `SteinerUpperBound.upper_bound_original_probability`: the same statement on
  that exact program's original compiled-seed law.
- `SteinerUpperBound.algorithm_query_time_bound`: on **every** execution,
  both distance queries and charged ordinary work are at most
  `C*(n+1)*sqrt(n+1)*(1+floor(log2(n+2)))^206`, for a proved positive absolute
  constant `C`. Thus both are `O~(n^(3/2))`.

The empty and singleton terminal cases return zero. `Instance.optimum` is the
actual minimum cost of a graph connecting the terminals, allowing any input
point as a Steiner vertex. The final theorem assumes neither accurate MST/band
estimates nor saving, VO, performance, or resource certificates. All intermediate
contracts are instantiated with their proved implementations.

The program has logical query type `Empty`: the retained-set membership requests
of its frontend are implemented by the actual private cached metric-query
factory, not supplied by an additional oracle. Component exploration, reusable
sampling, lazy random-order matching, finite MST/band evaluation, numerical
setup, and failure clocks are all part of the causal query program.

The time model is the manuscript's unit-cost arithmetic RAM, including indexed
memory operations and random sampling. The theorem is not a bit-complexity or
native Lean evaluator runtime claim. Its explicit constants and logarithmic
powers are conservative, not intended as a practical implementation.

## Proof organization

### Lower bound

[`LowerBound.lean`](SteinerLowerBound/LowerBound.lean) assembles the actual
floored parameters, all-size padding, cost separation, and expected-query
reduction. Its transcript estimate comes from
[`TranscriptBound.lean`](SteinerLowerBound/TranscriptBound.lean), which combines
the public metric comparison, four-way adaptive screening, implemented
visible-star simulator, categorical replacement, and adaptive moment matching.
The simulator's freshness, accessible-region bound, correctness before stopping,
and overflow accounting are proved from its implementation.

Several auxiliary arguments are deliberately different from the writeup:

- Finite moment-matched weight laws are constructed inductively using affine
  copies, rather than formalizing the writeup's interpolation construction
  and its asymptotic coefficient estimates.
- First-moment bounds give fixed small cost-gap failure probabilities; the
  writeup's stronger exponential auxiliary estimates are not claimed here.
- Direct tree-cost inequalities replace the exact profit identity.
- A direct Hellinger comparison replaces the relative-entropy hybrid and
  separate activation coupling.
- The generic adaptive coupling uses matching order `s+2`; the parameter choice
  still yields the stated exponent exactly.
- The uniform filler-sparsity failure bound is `3/m^3`, sufficient for the
  vanishing master error, rather than the writeup's stronger failure exponent.
- Explicit floor inequalities and a fixed adjacent-size ratio replace some
  asymptotic limit arguments.

These are proved alternative ingredients for the complete main theorem, not
unproved assumptions or identified counterexamples to the original arguments.
The blue `\lean{...}` annotations in
[`Submission/tight-main.tex`](../Submission/tight-main.tex) explain the reasons
and give human-readable proofs, including the changed constants and matching
order. In particular, the stronger original auxiliary statements are not
claimed to have been verified verbatim.

### Upper bound

[`Algorithm.lean`](SteinerUpperBound/Algorithm.lean) fixes the public algorithm
and resource constants; [`Main.lean`](SteinerUpperBound/Main.lean) publishes the
unconditional approximation theorem. The actual program is assembled in
[`ConcreteEstimator.lean`](SteinerUpperBound/ConcreteEstimator.lean), with
correctness in
[`ConcreteEstimator/Correctness.lean`](SteinerUpperBound/ConcreteEstimator/Correctness.lean)
and every-execution bounds in
[`ConcreteEstimator/Complexity.lean`](SteinerUpperBound/ConcreteEstimator/Complexity.lean).

`Model`, `TreeGeometry`, `Structural`, and `NetworkLifting` establish the genuine
optimization and structural inequalities. `QueryProgram`, `ComponentExplore`,
`LocalAccess`, and `PortGraph` implement the causal query/memory interfaces.
`Matching.Padded` proves the lazy matching runtime's value and weighted-access
bounds internally. `SavingEstimator.Resources.performance` closes its
original-seed good-event accounts with an explicit fixed constant and degree
64; the final theorem does not take this property as a premise.

Some upper-bound ingredients differ from the manuscript:

- A million discrete phases replace the continuous log-uniform shift.
  Their disjoint windows give the sufficient persistence failure bound `1/1000`.
- An implemented cover/component-count quadrature proves the accurate MST
  interval, rather than assuming an external MST-estimation algorithm.
- Second-moment bounds replace exponential score concentration. The additional
  inverse-confidence factors remain polynomial in logarithms.
- Exact clipped-weight MST differences evaluate band benefits, and actual
  small MST minima evaluate one-center costs. Projection uses the conservative
  loss `65*rho+3*tau*a`.
- Reusable sampling uses rational logistic odds and charged binary powering.
  Lazy matching uses finite integer priorities, explicit collision errors,
  and an internally proved polylogarithmic call/access bound.
- Component/list operations have conservative additional polynomial cutoff
  factors. Real paired work/disclosure clocks and restricted original-seed
  expectations handle bad calibration, pool, and rank executions without
  conditioning mistakes.

These proved changes preserve the main approximation and `n^(3/2)` exponent,
but do not assert the manuscript's sharper auxiliary constants or logarithmic
bounds verbatim.

## Trust audit

`Audit.lean` prints the axioms of the main accuracy and resource theorems and
checks the transitive axiom dependencies of every imported public and private
project declaration in both libraries. It rejects anything except the standard
Lean axioms `propext`, `Classical.choice`, and `Quot.sound`, including any
dependency on `sorryAx` or a custom assumed lemma. The project contains no
`sorry`, `admit`, custom axioms, or native proof-evaluation shortcuts.
