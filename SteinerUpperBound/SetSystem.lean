module

public import SteinerUpperBound.SetSystem.Greedy
public import SteinerUpperBound.SetSystem.Scores
public import SteinerUpperBound.SetSystem.OrderedMatching
public import SteinerUpperBound.SetSystem.MappedForest
public import SteinerUpperBound.SetSystem.PortSaving

/-!
# Finite set-system combinatorics

All interfaces use the unchanged `Structural.saving E rows A`. Eligibility `E`
is fixed, including in the deletion and score theorems.

* `smallCover E rows A order` actually inspects the eligible rows in `order`,
  accepting a row precisely when it has at least two fresh elements.
  `smallCover_guarantee` proves `0 ≤ Z ≤ saving` and `saving / 2 ≤ Z` for
  `Z = smallCoverEstimate E rows A order`.
* `saving_scores` proves both deletion/covered-component score inequalities.
* `orderedCap` constructs the first-`b` incident lists. `mutualGraph` is their
  actual mutual-incidence graph. `mutualCap_independent_bound` proves the
  independent-set bound by incidence double counting.
* `mutualCap_matching_half` applies to every maximal labeled-copy matching
  with exactly that underlying graph, including parallel copies.
  `orderedMutual_greedy_half` and `orderedMutual_expected_half` instantiate
  actual first-`b` lists and an actual finite copy graph, without assuming
  a matching-approximation contract.
* `saving_forest_edges` constructs true incidence ports on the whole current
  universe. Its graph is acyclic, every retained row has degree at least three,
  its edge count `f` and retained-row count `z` satisfy
  `saving / 2 ≤ f - 2*z` and `3*z ≤ f`, and the actual row-clique graph has
  rank `f - z`. The construction takes an attaining family, runs the finite
  spanning-forest algorithm, and filters rows of degree at most two.
* `incidence_forest_port_rank` proves the generic incidence-forest
  identification-rank formula. `forest_rank`, `rank_map_injective`, and
  `quotient_gain` give the corresponding graph-rank and quotient interfaces.
  `port_rank_saving` and `incidence_forest_events_le_saving` also apply to
  event labels with repeated center IDs.
-/

@[expose] public section

namespace SteinerUpperBound.SetSystem

end SteinerUpperBound.SetSystem
