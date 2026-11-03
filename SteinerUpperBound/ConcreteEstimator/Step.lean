module

public import SteinerUpperBound.ConcreteEstimator.Step.Contract
public import SteinerUpperBound.ConcreteEstimator.Step.Resources
public import SteinerUpperBound.ConcreteEstimator.Step.Performance
public import SteinerUpperBound.ConcreteEstimator.Step.Closed

/-!
# Exact concrete saving-step adapters

The program is the parent's existing `ConcreteEstimator.step`, unchanged.
`Step.value`, `Step.work`, and `Step.positive` prove its exact relationship
to the executed `BandEstimator.scaleProgram` and the actual
`SavingEstimator.Clocked.fromParameters`.

`Step.Performance I bits label root p inverse AW AP δ` asks, for each coarse
index and each correct incoming cache, only for a genuine event on the
ORIGINAL uncapped saving program's compiled seeds: failure at most `δ`,
restricted ordinary expectation at most `AW`, and restricted positive
expectation at most `AP`. There is no scalar, sampling, or VO certificate.
`Step.raw` names that exact original program at the actual coarse scale.
`Step.performance_of_global` instantiates this predicate from the resource
owner's genuine `SavingEstimator.Resources.Performance K d`, using its
original-seed accounts at each scale/cache and `δ=10*beta n`.
`Step.closed_performance` and `Step.closed_saving_contract_of_geometry`
now instantiate the PROVED `SavingEstimator.Resources.performance`
witness at `resourceConstant,64`, with no performance premise.
`closed_saving_contract_of_geometry_of_le` also allows larger public
natural budgets, assuming only their numerical domination of those fixed
budgets. The resulting error is `14*beta n` plus the chosen clock loss.

`Step.saving_contract` proves the EXACT
`EstimatorFrontend.Analysis.SavingContract` for the concrete step, with
```
Step.error n δ = 4*beta n + δ +
  5/(EstimatorClocks.amplification*(heightBudget n+1)).
```
It uses injective public enumeration, terminal equality, the actual public
parameter equality, true coarse-root bits, and `Performance`.
`Step.saving_contract_of_geometry` takes the existing `Analysis.Geometry`
record instead of repackaging those facts. The retained label count is
proved equal to the actual retained point cardinality, and the saving
statistic is identified with `Analysis.coarseRetained`.

`Step.saving_resources` supplies the exact event-free
`EstimatorFrontend.Resources.SavingResources` bundle. Its natural budgets
are `stageW+25+2*heightBudget n+3` and `stageD+1`.
The additional repeated-multiply scale program is genuinely executed and
charged, not evaluated in a free leaf. Cache preservation on `some` holds
on all actual scalar outcomes and requires no performance, accuracy,
cover, or retained-root event. Enumeration and the actual coarse-height
bound suffice for these resource/cache adapters.

These adapters use the actual key functions directly; inverse-left and
cover-world facts are needed by the parent's geometry construction, not
additionally by these point-count or saving-statistic identities.
-/

@[expose] public section
