module

public import SteinerUpperBound.EstimatorClocks.Selection
public import SteinerUpperBound.EstimatorClocks.Correctness
public import SteinerUpperBound.EstimatorClocks.Program
public import SteinerUpperBound.EstimatorClocks.Resources

/-!
# Executable public clock budgets

This prefix selects integer budgets and specializes the actual disclosure/work clock.
It does not assert a final estimator or supply unproved runtime accounts.

With `H = heightBudget n`, a stage uses work budget `100000*(H+1)*(AW+1)`
and disclosure budget `100000*(H+1)*(AP+1)`. `stage_success_of_good` uses genuine
events and restricted expectations of the original compiled program. Summing its
loss over at most `H` stages costs at most `51/1000000`.

The factory uses `W=100000*(AW+1)`, `a=100000*(AP+1)`, and `D=2*k*(a+14)`.
`factory_total_loss` bounds the two Markov ratios and the exponential expression
by `3/20000` when `k>0`; `total_loss` combines both selections within `201/1000000`.
The exponential statement is arithmetic, not an assumed factory probability law.

`factory_budget_of_pos` proves `W+D+1 ≤ 400000*(AW+k*AP+k)`.
`factory_budget_polylog`, `stage_budget_polylog`, and `summed_stage_budgets_polylog`
derive explicit polynomial-log closure from natural account bounds.
Both natural and real versions of `(n+1)*(1+n/t) ≤ 2*(n+1)*t` are provided.

Budget setup executes literal integer addition/multiplication and field writes:
`byHeightProgram_evaluates` charges eight operations, the known-logarithm/parameter
variants charge nine, and `factoryProgram_evaluates` charges ten. All make zero
metric/retention queries and disclose no positives. Integer logarithms and the
input accounts are not recomputed for free by these constructors.
-/

@[expose] public section
