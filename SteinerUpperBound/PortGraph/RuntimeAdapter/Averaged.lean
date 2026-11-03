module

public import SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged.Joint

/-!
# Actual averaged metric vertex-oracle accounts

`Averaged` instantiates the cost-sensitive matching transport with the actual
cached metric callbacks. Every root may have its own correct incoming cache;
the canonical frame and primitive initial memory also vary with that root.

* `work_W_eq` and `positive_W_eq` count all padded slots and actual Heavy slots.
* `calibrated_residual_product` obtains the residual product bound from the true
  calibration/residual inequalities, using an integer floor rather than a
  ceiling. No graph-density or resource certificate is assumed.
* `root_normalization`, `vertex_ratio`, and `counter_tail_empty` implement the
  retained-point initiation mass `1/g`, including the empty true-vertex case.
* `oracle_counter_test` transports arbitrary tests of the actual counter. The
  wrapper adds exactly twelve ordinary work and no positive disclosures.
* `callback_counter_tail` is uniform in the correct incoming cache at each root.
  Its analysis cost is independent of that cache.
* `closed_counter_tail` and `calibrated_counter_tail` prove original-code
  initiation-weighted tail bounds:

  `tail(θ + 12 * counter.work) ≤ (m/g) * δ + F * budget / θ`.

  Here `δ = publicSize⁻³⁰`, `F = 2⁶⁴ (log₂ publicSize + 1)⁸`, and the ordinary /
  positive budgets are respectively
  `1200000 (n+1)(1+n/t)(B+2)⁴` and `200 (1+n/t)(B+2)³`.
* `closed_original_good_accounts` and `calibrated_original_good_accounts`
  bound the actual original compiled-seed Good counter expectation by
  `2¹²⁸ (log₂ publicSize + 1)⁹ * budget + 12 * counter.work * (m/g)`,
  with original-seed failure at most `(m/g) publicSize⁻³`.
* `jointGood` intersects the ordinary and positive counter cutoffs on the
  **same** original oracle seed. `closed_joint_good_accounts` and its calibrated
  version preserve both cost bounds and pay failure at most
  `2 (m/g) publicSize⁻³`. `joint_accounts_empty` makes both accounts zero
  when the true graph has no vertex.
  `jointGoodCost_eq` / `jointGoodFailure_eq` identify these original-seed
  integrals with direct Code tests of `jointOutcomeGood`, the two natural
  outcome-counter cutoffs.

The public natural cutoff is
`unit * 2^(100 + 20 (log₂ publicSize + 1)) + overhead`,
where `unit` is the concrete work Cstar or `B+2`, and overhead is twelve
ordinary work or zero positives. `counterCeiling_polynomial` bounds it by
`2¹²⁰ unit publicSize²⁰ + overhead`.

The actual cold table allocation, hot preparation, accepted partner-frame
insertion, and arithmetic rate are included through the concrete primitive
Resources. The completed-rank injectivity event occurs only inside the proved
model analysis integral; it is not asserted to be an original runtime seed event.
-/
