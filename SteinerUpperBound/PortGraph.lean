module

public import SteinerUpperBound.PortGraph.Degree
public import SteinerUpperBound.PortGraph.Lift

@[expose] public section

/-!
# Actual retained-component port graph and static slot correspondence

Namespace: `SteinerUpperBound.PortGraph`. Runtime data is the parent's
`LocalAccess.SlotConfig Q n k`; `I`, `bits`, and all graph carriers below are
analysis-only. No runtime operation enumerates the retained set or true graph.

## True finite graph

`retained I bits cfg = I.terminals.filter (fun x => bits(cfg.key x))`.
`removed I cfg` is the actual terminal bitmap selected by `cfg.covered`;
the caller may identify it with its selected-ball union.
`parts` is the actual strict-threshold-`cfg.scale` component family on retained
terminals. `rows` uses radius `5*cfg.scale/8`, and `eligible` always uses those
ORIGINAL rows, not rows recomputed after deletions.

`smallParts I bits cfg B` filters parts of size at most `B` disjoint from the
bitmap. The execution vertex type is exactly
`Vertex I bits cfg B := ↥(smallParts ...)`, with
`vertices_card_le : Fintype.card Vertex ≤ retained.card`.

`Copy I bits cfg b B` is the subtype of `Fin n × (Fin k × Fin k)` consisting
of an originally eligible center and an ordered pair of distinct public
terminal indices. The ports are retained, near the center, in DIFFERENT
small residual components, and the center occurs in both first-`b` incidence
lists. Different physical port pairs remain parallel copies.

`graph I bits cfg b B` is the actual labeled loopless multigraph on `Vertex`.
`graph_realizes ... hT` proves its underlying graph is
`(SetSystem.mutualGraph smallParts eligible lists).comap Subtype.val`.
Here `hT : cfg.terminals.toList.toFinset = I.terminals`.
`copies_card_le` and `publicNames_card_le` give the public upper bound `n*k²`.
`name` maps true copies to ambient `Name n = Fin n × Sym2(Fin n)`;
`nameEmbedding` is injective when the public terminal vector is nodup.

## Canonical frames and ambient addresses

`canonicalFrame I cfg b B C` is the VALUE of the actual `frameResult` on
public vertex order, public terminal order, and wanted set `C`.
`pointList`, `canonicalFrame_points`, `canonicalFrame_pointSlot`,
`canonicalFrame_centers`, and `canonicalFrame_rowSlot` expose exact canonical
points/first-`b` centers and their padded vectors.

`explore_complete_iff` proves true completion iff the actual component has
size at most `B`; false completion gives a genuine reachable `B+1` witness.
`locate_frame I bits cfg b B hT hTermNodup hx cache hc` proves the actual
location result is
```
if (portComponent I bits cfg x).card ≤ B
then some(canonicalFrame I cfg b B (portComponent I bits cfg x))
else none.
```
Thus frames and positions are independent of the first root and correct cache.

`rootEmbedding I bits cfg B hT : Vertex ... ↪ Fin n` is the canonical point
list head. `frame_head` identifies the returned root, and `locate_root` gives
actual preparation directly at an embedded true vertex.
`slotEquiv b B k : LocalAccess.PortSlot b B k ≃ Fin(b*B*k)` flattens the
public three-index domain. `slots_card` proves its exact padded length.
`ambientAddress` embeds a true endpoint slot into
`Fin n × Fin(b*B*k)`. Runtime roots and copy names remain ambient data, so
counterfactual replies never have to manufacture subtype proofs.

## Actual slot program, not a correctness certificate

`eligible_iff_third` proves the ordinary partition-counting equivalence:
given two distinct complete incident components, an originally eligible
center has a third retained near point outside both, and conversely.
The third point may lie in a covered or large component.

`slot_value ... cache hc` proves that the actual
`LocalAccess.slotResult I.weight bits cfg canonicalFrame slot cache`
has first projection exactly `slotSpec`, independently of the correct cache.
The proof verifies actual finish/index, third-point, mutual, partner,
padding, bitmap, membership, distance, and retained-bit stages.

`slots I bits cfg hT hTermNodup : Matching.Padded.Slots (graph ...)` exports
the stable slot contract: proof-only directed-copy placement, unique
placement, reverse involution, and exact copy identity. Its `staticTest`
is analysis-only inverse placement.

`slot_result_encoded` proves the actual optional reply, mapped by
`encodeReply` to `(physical name, (ambient root, flattened reverse index))`,
equals `slots.test` mapped by `encodeTest`. `slot_program_value` gives this
same exact equality through the ACTUAL causal metric-query `slotProgram`,
for arbitrary real observable tests. No supplied slot-refinement premise
is used.

`slot_result_frame_exact` proves a successful reply contains precisely the
canonical frame of the static test's reverse vertex.
`slot_result_unique` proves one physical-copy slot per endpoint, even across
different correct caches. Generic `Slots.test_reverse` and `test_unique`
then apply directly. Combine these with the parent's checked
`LocalAccess.slot_cache_correct` and resource theorems.

## Genuine heavy/degree counts

`residualNeighbors` is the actual retained near ball minus the bitmap;
`residualNeighbors_eq` exposes `(N ∩ ball(v,5a/8)) \ D`.
Given the geometric residual bound
`hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P`,
the checked interfaces
```
heavySlots_card_le I bits cfg b hT hTermNodup C P hres
trueSlots_card_le  I bits cfg b hT hTermNodup C P hres
degree_le         I bits cfg   hT hTermNodup C P hres
```
give bounds `b*B*P`. `heavySlots` uses the parent's ACTUAL `LocalAccess.Heavy`
predicate, counting candidates even if later rejected as large, covered,
nonmutual, or ineligible. Only the residual-ball bound is supplied; neither
degree nor total cost is assumed. Per-slot resource proofs remain parent-owned.

## Saving-statistic lift without collapsing copies

`AllPart := ↥parts` retains every original component. `originalRows` is the
actual original row preimage, `residualParts` the residual small subfamily,
and `inclusion : Vertex ↪ AllPart`. `originalRows_card` preserves original
row cardinalities and `originalLists_ordered` identifies exact first-`b`
lists. `incidenceCap` is constructed from those genuine ordered lists.

`liftedGraph` is a PROOF-ONLY endpoint lift of the SAME `Copy` carrier to
`AllPart`. `lifted_realizes` proves Realizes for the original eligibility and
the constructed incidence cap. `lifted_greedy` preserves the entire greedy
copy set for EVERY rank assignment; `lifted_matched` preserves matched-value
events at included vertices. There is no copy collapse or rank-law change.

`greedy_saving_bounds` and `expected_greedy_saving_bounds` instantiate the
checked generic capping theorem, for every rank or arbitrary finite rank law:
```
saving(original eligible, original rows, residualParts)/2 - n/b
  ≤ actual greedy matching size
  ≤ saving(original eligible, original rows, residualParts).
```
Only the natural `1≤b` premise is needed in addition to the public enumeration.
No random-rank law for `Runtime.answer` is asserted here; its remaining causal
refinement/accounting proof is matching-owner work.
-/
