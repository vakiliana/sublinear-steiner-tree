module

public import SteinerUpperBound.TreeGeometry.Basic
public import SteinerUpperBound.TreeGeometry.Surgery
public import SteinerUpperBound.TreeGeometry.Counts
public import SteinerUpperBound.TreeGeometry.Tour
public import SteinerUpperBound.TreeGeometry.Shortcut
public import SteinerUpperBound.TreeGeometry.Packing
public import SteinerUpperBound.TreeGeometry.Flooring

@[expose] public section

/-!
# Finite-tree geometry for the Steiner estimator

`TreeSolution` is an actual tree on an explicit selected vertex set. Its ambient
network is feasible for `Instance.optimum`, with exactly the same metric cost.
`clean_optimum_tree_attained` and `TreeSolution.cleanup` use proved leaf deletion
and degree-two suppression, not a cleanup hypothesis.

`exists_tree_tour` constructs doubled routes by leaf recursion. Metric
shortcutting gives `mst_le_twice_optimum`, `terminal_tour_mst`, and
`separated_terminal_packing`. `Flooring.floored` is an actual metric instance;
its decision-tree simulation, optimum comparison, and normalized estimate
transfer are proved in `Flooring`.
-/
