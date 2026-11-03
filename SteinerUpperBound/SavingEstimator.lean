module

public import SteinerUpperBound.SavingEstimator.Cache
public import SteinerUpperBound.SavingEstimator.Work

/-!
# Closed public-parameter saving frontend

```
SavingEstimator.fromParameters terminals root key a publicParameters cache :
  Code (Sym2 (Fin n)) Q (LargeCoverProgram.Answer Q n)
```

The terminal vector has length `k+1`. The code executes a `Setup.Plan` that
recomputes the two reusable-sample noise logarithms and the pool rejection
logarithm, charging every arithmetic/logarithm instruction. It constructs
the actual `LargeCoverProgram.Parameters` and invokes the actual
`PortGraph.RuntimeAdapter.builder` internally. There is no supplied VO,
metric instance, retained set, score law, or correctness/cost certificate.

`configuration_public` identifies the result for `parameters n (k+1)` with
`closed n (k+1)`. It uses the public `t n`, `B n`, `epsQ n`, `xiSavingQ n`,
`meanSamples n (xiSavingInv n)`, and `samplerCap` row cap. Calibration and
mean total proposal caps are samples times row cap. The pool uses
`NsPool n` samples, row cap `(k+1)*poolClock n`, and their product as its
total cap. `no_abort_capError` proves global proposal overflow impossible.
All sampler failures and calibration/mean deviations remain marginal
statements, not conditioning assumptions.

## Concrete confidence

`fromParameters_saving_confidence` gives success probability at least
`1-4*beta n` for the actual `LargeCoverProgram.GoodSaving` contract:
`0 ≤ Z ≤ Phi` and `Phi/2-eps n*g ≤ Z`, with the actual retained-system
saving and count. Its only premises are the actual terminal equality/nodup,
correct incoming cache, and retained public root. All public numerical tests
and the concrete VO refinement are discharged.

The explicit actual rank/tie error is paid, not discarded.
`inverse_eq_ten_cutoff`, `betaDenom_le_cube`, `samples_power_bound`, and
`rank_polynomial_budget` prove
`xiSavingInv=10*B`, `betaDenom≤B^3`,
`samples≤25600*B^5`, and `betaDenom*samples≤B^30`.
`publicSize_ge_cutoff` and `concrete_rank_error` therefore prove
`samples*concreteVOError≤beta n` for every nonempty public universe, without
a small-size exception or an asymptotic premise.

## Cache and setup accounts

`fromParameters_cache_ensures` closes the concrete builder's actual
`Causal.Ensures` cache law. `fromParameters_cache_failure_zero` and
`fromParameters_cache_on_support` give zero cache-failure probability and
cache correctness on every positive-mass compiled seed. No forged-frame
or zero-mass counterfactual correctness is asserted.
`fromParameters_good_confidence` gives the same `1-4*beta n` bound jointly
with correct returned cache, for direct sequential composition.

`configurationWork_exact` counts all setup instructions;
`configuration_work_polylog` bounds them by a fixed constant times `ell n`.
`fromParameters_work` adds exactly this work plus twelve units to the actual
concrete saving program; `fromParameters_positive` adds no positive replies.
Whole-VO averaged costs and the final disclosure/work clocks are separate
interfaces and are not assumed or claimed here.
-/

@[expose] public section
