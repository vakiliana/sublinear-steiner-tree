module

public import SteinerUpperBound.ConcreteEstimator.Correctness.Program

/-!
# Original-metric correctness of the actual concrete estimator

`Correctness.closed_program_success` proves success probability at least `9/10`
for the actual program with the proved fixed saving resource constant, exponent
`64`, and `ConcreteEstimator.frontendFactor resourceConstant`. It has no
performance, resource, VO, MST-answer, band-accuracy, or final-correctness premise:
only a legal metric instance and its injective terminal-vector enumeration.
`closed_program_original_probability` states this on the original compiled
program's own seed law. The root upper-bound entrypoint can combine this checked
corollary with the same program's universal resource bounds.

`Correctness.program_success` proves success probability at least `9/10` for the
literal `ConcreteEstimator.program K (frontendFactor K) d label`, with ratio
`2 - eta0`, where `eta0 = 1/(2*10^12)`. Its only algorithmic premise is the named
`SavingEstimator.Resources.Performance K d`: genuine original raw saving-seed
Good accounts, uniformly over correct incoming caches. The closed corollary
instantiates exactly `SavingEstimator.Resources.performance`; the intermediate
conditional theorem is not presented as the final upper-bound theorem.

No VO callback, supplied fine-MST answer, band accuracy, final numerical
correctness, or cheap good-cover assumption occurs in the interface.

The proof uses the executed row observation and metric flooring, actual finite
phase mixture, private cached cover factory and both factory cutoffs, charged
fine/saving/band frontend, literal public-budget computation, and full outer
scalar cap. Frontend resources are averaged under the unconditional cached
factory law. The empty and singleton terminal cases execute pure zero and use
the actual optimum-zero theorem.

`program_original_probability` is the conditional original-seed formulation.
`prepared_success` exposes the intermediate
`49/50` guarantee after original-metric transfer, before the outer scalar cap.
-/
