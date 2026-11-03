module

public import SteinerUpperBound.SavingEstimator.Clocked.Confidence
public import SteinerUpperBound.SavingEstimator.Clocked.Cache

/-!
# Actual clocked saving step

```
SavingEstimator.Clocked.fromParameters terminals root key a p AW AP cache :
  Code (Sym2 (Fin n)) Q (Option (ℝ × Cache Q))
```

The code executes `EstimatorClocks.fromParametersProgram p AW AP`, which
charges all natural clock arithmetic using `p.heights`. It then runs the
actual closed `SavingEstimator.fromParameters` through the actual
`(raw.disclosureCap D).cap W`. A charged option scan flattens both clock
aborts and an absent raw scalar into `none`; only an actual scalar/cache
pair is returned as `some`.

`fromParameters_expected` is event-free:
ordinary expected work is at most `W+25` and expected fresh positive replies
at most `D+1`, where `(W,D)=EstimatorClocks.byHeight p.heights AW AP`.
Nine work units are actual clock setup, sixteen are flattening/control.
Neither performance accounts nor accurate calibration are premises.

`fromParameters_cache_ensures` and `fromParameters_cache_failure_zero`
preserve correct cache on successful positive-support outputs, including inaccurate scalar executions. Aborts
carry no cache. The proof uses the actual raw cache law and the exact paired
clock value formula, not a forged-frame/all-counterfactual branch assertion.

`fromParameters_success` accepts only a genuine performance event `Good`
on the ORIGINAL raw `SavingEstimator.fromParameters` compiled seed type:
`Pr[not Good]≤δ`, `E[1_Good*work]≤AW`, and
`E[1_Good*positiveReplies]≤AP`. No saving, calibration, or VO correctness
certificate is supplied. It intersects that event with the actual raw
`GoodAnswer` event, whose failure is already proved at most `4*beta n`.
The resulting `GoodReply` gives a returned scalar with actual saving
soundness/half-approximation and correct cache, with probability at least
```
1 - 4*beta n - δ - 4*AW/(W+1) - AP/(D+1).
```
`fromParameters_success_byHeight` bounds the two actual ratios by
`5/(100000*(heightBudget n+1))`.

The resource owner supplies the original-seed performance event/accounts.
This module does not identify foreign seed spaces, assume unconditional
uncapped VO costs, edit the raw estimator, or assemble the full estimator.
-/

@[expose] public section
