# Tight bounds for sublinear metric Steiner tree, in Lean

[![Lean build](https://github.com/vakiliana/sublinear-steiner-tree/actions/workflows/main.yml/badge.svg)](https://github.com/vakiliana/sublinear-steiner-tree/actions/workflows/main.yml)

In the metric Steiner tree problem, we are given an $n$-point metric space $(V, w)$ and a set $T \subseteq V$ of terminals, and we seek the smallest weight $\mathrm{OPT}$ of a tree that spans $T$ and may also use points of $V \setminus T$. In the distance-oracle model, the algorithm knows $V$ and $T$ upfront and may query any pair $\{u, v\}$ to learn $w(u, v)$; its cost is the number of queries. The minimum spanning tree on $T$ approximates $\mathrm{OPT}$ within a factor of $2$, and its weight can be estimated with $\widetilde{O}(n)$ queries, so the question is the query complexity of estimating $\mathrm{OPT}$ within a factor strictly below $2$.

This repository is a Lean 4 verification of the two theorems of **Tight Bounds for Sublinear Metric Steiner Tree** (*arXiv link to be added soon*), which together settle the question: the answer is $n^{3/2}$.

**Theorem (Upper bound).** There is an absolute constant $\eta_0 > 0$ and a randomized algorithm that, given an $n$-point instance, outputs with probability at least $2/3$ an estimate $C$ with $\mathrm{OPT} \le C \le (2 - \eta_0)\,\mathrm{OPT}$, using $\widetilde{O}(n^{3/2})$ distance queries and time.

**Theorem (Lower bound).** For every $\eta \in (0,1)$ and every integer $s \ge 1$ there are constants $\kappa > 0$ and $n_0$ such that, for all $n \ge n_0$, every randomized algorithm that outputs on every $n$-point instance, with probability at least $2/3$, an estimate in $[\mathrm{OPT}, (2-\eta)\,\mathrm{OPT}]$ must make more than $\kappa \cdot n^{(3s+7)/(2s+5)}$ distance queries in expectation on some instance. Since $(3s+7)/(2s+5) = 3/2 - 1/(4s+10)$, estimation within any factor $2-\eta$ requires $\Omega(n^{3/2-\varepsilon})$ queries for every $\varepsilon > 0$, so the exponent $3/2$ is tight.

## The lower bound

The main statement is `SteinerLowerBound.lower_bound` in [`SteinerLowerBound/LowerBound.lean`](SteinerLowerBound/LowerBound.lean):

```lean
namespace SteinerLowerBound

universe u

/-- Every sufficiently large size admits a three-distance metric family with
linear many terminals on which every successful randomized estimator needs
`Ω(n^((3s+7)/(2s+5)))` expected distance queries. -/
theorem lower_bound {η : ℝ} (hη : 0 < η) (hη₁ : η < 1) (s : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ D : ℕ, 0 < D ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ M : HardInstance η s n, M.Geometry D ∧ HardInstance.Hard.{u} M κ

end SteinerLowerBound
```

The statement uses these definitions:

* **Hard instances**: `HardInstance η s n` packages a constructed `n`-point instance; `HardInstance.optimum` is the actual minimum over selected Steiner vertices and spanning trees, not a surrogate cost expression.
* **Geometry**: `M.Geometry D` proves that the instance is a genuine metric on exactly `n` points, that at least `n / D` of them are terminals, that the real distance oracle agrees with that metric exactly, and that every off-diagonal distance lies in `{ℓ, 1, 2}` with `1/n³ ≤ ℓ ≤ D³/n³`.
* **Hardness**: `HardInstance.Hard M κ` quantifies over adaptive decision-tree algorithms with real-valued distance answers and estimates. Repeated queries are allowed; random seeds range over arbitrary measurable probability spaces (hence the universe parameter `u`), with only the query-count and output functions required measurable; expected query counts use the extended nonnegative integral, so infinite expectations are included. Success means `OPT ≤ estimate ≤ (2-η)·OPT` with probability at least `2/3` on every member of the family; the conclusion is that any such estimator makes more than `κ · n^((3s+7)/(2s+5))` expected queries on some member. The theorem is stated for every `s : ℕ`, so it covers in particular every integer `s ≥ 1` from the paper, and `Exponents.lowerExponent_eq` identifies the exponent with `3/2 - 1/(4s+10)`.

For a fixed target exponent, `SteinerLowerBound.epsilon_lower_bound` (same file) gives the `Ω(n^(3/2-ε))` form:

```lean
theorem epsilon_lower_bound {η ε : ℝ}
    (hη : 0 < η) (hη₁ : η < 1) (hε : 0 < ε) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ κ : ℝ, 0 < κ ∧
      ∃ D : ℕ, 0 < D ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ M : HardInstance η s n, M.Geometry D ∧ HardInstance.HardExponent.{u} M κ (3 / 2 - ε)
```

[`LowerBound.lean`](SteinerLowerBound/LowerBound.lean) assembles the floored parameters, all-size padding, cost separation, and expected-query reduction; the transcript-indistinguishability core — the public metric comparison, adaptive screening, visible-star simulator, and adaptive moment matching — is in [`TranscriptBound.lean`](SteinerLowerBound/TranscriptBound.lean).

## The upper bound

The main statement is `SteinerUpperBound.upper_bound` in [`SteinerUpperBound/Main.lean`](SteinerUpperBound/Main.lean):

```lean
namespace SteinerUpperBound

/-- The actual public-input metric-query algorithm beats factor two on every
finite metric. Its optimization objective is the genuine Steiner minimum. -/
theorem upper_bound {n length : ℕ} (I : Instance (Fin n))
    (terminals : Vector (Fin n) length) (hinj : Function.Injective terminals.get)
    (hT : Finset.univ.image terminals.get = I.terminals) :
    (2 : ℝ) / 3 ≤ Code.valueProbability I.weight Code.emptyBits (algorithm terminals)
      (GoodEstimate (2 - eta0) I.optimum)

end SteinerUpperBound
```

The statement uses these definitions:

* `algorithm` ([`SteinerUpperBound/Algorithm.lean`](SteinerUpperBound/Algorithm.lean)) — the actual randomized metric-query program. Its only input is the public terminal-label vector on `Fin n`; its logical query type is `Empty`, so every piece of metric-dependent information is obtained at run time through distance queries, including component exploration, reusable sampling, lazy random-order matching, and the finite MST/band evaluations.
* `Instance` and `Instance.optimum` — an arbitrary finite metric instance and the genuine Steiner minimum: the least cost of a graph connecting the terminals, with any input point allowed as a Steiner vertex.
* `eta0 = 1 / (2 · 10¹²)` — the proved approximation constant, and `GoodEstimate (2 - eta0) I.optimum` — the window `OPT ≤ estimate ≤ (2 - eta0) · OPT`.
* `Code.valueProbability` — the probability, over the program's random seeds, that the output satisfies the predicate. The proof ([`ConcreteEstimator/Correctness.lean`](SteinerUpperBound/ConcreteEstimator/Correctness.lean)) establishes success probability at least `9/10`; the published statement weakens it to the paper's `2/3`. `upper_bound_original_probability` (same file as `upper_bound`) states the identical guarantee for the compiled program's own finite seed law.

Resources are bounded on **every** execution, not only in expectation: `SteinerUpperBound.algorithm_query_time_bound` shows that both distance queries and charged ordinary work are at most `C · (n+1) · √(n+1) · (1 + ⌊log₂(n+2)⌋)^206` for a proved positive absolute constant `C`, i.e. `Õ(n^(3/2))`. The time model is the paper's unit-cost arithmetic RAM, including indexed memory operations and random sampling; this is not a bit-complexity or native Lean-evaluator runtime claim, and the explicit constants are conservative bookkeeping rather than a practical implementation. The program is assembled in [`ConcreteEstimator.lean`](SteinerUpperBound/ConcreteEstimator.lean), with the every-execution resource accounting in [`ConcreteEstimator/Complexity.lean`](SteinerUpperBound/ConcreteEstimator/Complexity.lean).

## Axioms and audit

The proofs use only Lean's standard foundational axioms:

* `propext` — propositional extensionality
* `Classical.choice` — the axiom of choice
* `Quot.sound` — quotient soundness

[`Audit.lean`](Audit.lean) prints the axioms of the main accuracy and resource theorems and checks the transitive axiom dependencies of every imported project declaration in both libraries, rejecting anything else — in particular any dependency on `sorryAx` or a custom axiom. The project contains no `sorry`, `admit`, custom axioms, or native proof-evaluation shortcuts. The [build workflow](.github/workflows/lean.yml) runs `lake build` and the axiom audit on every push and pull request; click the badge above for build logs.

## Building

Lean and mathlib are pinned to **v4.35.0** (`lean-toolchain`; `lake-manifest.json` records the exact dependency revisions). With elan installed, from the repository root:

```
lake exe cache get
lake build
lake env lean Audit.lean
```

The cache step is only needed on a fresh checkout. Build artifacts and downloaded dependencies live in the ignored `.lake/` directory.
