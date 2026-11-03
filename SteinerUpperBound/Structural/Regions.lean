module

public import SteinerUpperBound.Structural.Shapes

@[expose] public section

namespace SteinerUpperBound.Structural.Rooted

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] (G : SimpleGraph V) (r : V) (T : Finset V)

theorem first_step_child (ht : G.IsTree) {v w z q : V}
    (hvw : G.Adj v w) (p : G.Walk w z)
    (hq : G.Adj v q) (hdq : G.dist r q + 1 = G.dist r v)
    (hnot : s(v, q) ∉ (p.cons hvw).edges) : w ∈ children G r v := by
  rcases ht.dist_eq_dist_add_one_of_adj r hvw with hd | hd
  · have hwq := lower_neighbor_unique G r ht hvw hq hd.symm hdq
    exact False.elim (hnot (by simp only [SimpleGraph.Walk.edges_cons, List.mem_cons, hwq]; tauto))
  · exact (mem_children G r v w).mpr ⟨hvw, hd⟩

theorem path_region_height_le (ht : G.IsTree) {v z : V}
    (p : G.Walk v z) (hp : p.IsPath) {q : V}
    (hq : G.Adj v q) (hdq : G.dist r q + 1 = G.dist r v)
    (hnot : s(v, q) ∉ p.edges) : height G r T z ≤ height G r T v := by
  induction p generalizing q with
  | nil => exact le_rfl
  | @cons v w z hvw p ih =>
    have hchild := first_step_child G r ht hvw p hq hdq hnot
    have hdc := ((mem_children G r v w).mp hchild).2
    have hp' : p.IsPath := hp.of_cons
    have hnot' : s(w, v) ∉ p.edges := by
      rw [Sym2.eq_swap]
      exact (SimpleGraph.Walk.isTrail_cons hvw p).mp hp.isTrail |>.2
    exact (ih hp' hvw.symm hdc.symm hnot').trans (child_height_le G r T hchild)

theorem region_height_le (ht : G.IsTree) {v q z : V}
    (hq : G.Adj v q) (hdq : G.dist r q + 1 = G.dist r v)
    (hz : (G.deleteEdges {s(v, q)}).Reachable v z) :
    height G r T z ≤ height G r T v := by
  obtain ⟨p, hp⟩ := SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hz
  exact path_region_height_le G r T ht p.toPath p.toPath.isPath hq hdq
    (fun h => hp (p.edges_toPath_subset_edges h))

theorem path_height_one_unique (ht : G.IsTree) {v z : V}
    (hv : v ∉ T) (hh : height G r T v = 1)
    (p : G.Walk v z) (hp : p.IsPath) {q : V}
    (hq : G.Adj v q) (hdq : G.dist r q + 1 = G.dist r v)
    (hnot : s(v, q) ∉ p.edges) (hz : z ∉ T) : z = v := by
  cases p with
  | nil => rfl
  | @cons v w z hvw p =>
    have hchild := first_step_child G r ht hvw p hq hdq hnot
    have hdc := ((mem_children G r v w).mp hchild).2
    have hlt := child_height_lt G r T hv hchild
    have hnot' : s(w, v) ∉ p.edges := by
      rw [Sym2.eq_swap]
      exact (SimpleGraph.Walk.isTrail_cons hvw p).mp hp.isTrail |>.2
    have hle := path_region_height_le G r T ht p hp.of_cons hvw.symm hdc.symm hnot'
    have hpos := nonterminal_height_pos G r T hz
    omega

theorem path_height_two_nonterminal (ht : G.IsTree) (hr : r ∈ T) (hc : Clean G T)
    (hstar : NoZeroCoreStar G T) {v z : V}
    (hv : v ∉ T) (hh : height G r T v = 2)
    (p : G.Walk v z) (hp : p.IsPath) {q : V}
    (hq : G.Adj v q) (hdq : G.dist r q + 1 = G.dist r v)
    (hnot : s(v, q) ∉ p.edges) (hz : z ∉ T) :
    z = v ∨ (z ∈ children G r v ∧ height G r T z = 1) := by
  cases p with
  | nil => exact Or.inl rfl
  | @cons v w z hvw p =>
    have hchild := first_step_child G r ht hvw p hq hdq hnot
    have hdc := ((mem_children G r v w).mp hchild).2
    have hlt := child_height_lt G r T hv hchild
    have hnot' : s(w, v) ∉ p.edges := by
      rw [Sym2.eq_swap]
      exact (SimpleGraph.Walk.isTrail_cons hvw p).mp hp.isTrail |>.2
    by_cases hwT : w ∈ T
    · have hne := no_terminal_height_one G r T ht hr hc hstar w hwT
      have hzero : height G r T w = 0 := by omega
      have hle := path_region_height_le G r T ht p hp.of_cons hvw.symm hdc.symm hnot'
      have hpos := nonterminal_height_pos G r T hz
      omega
    · have hpos := nonterminal_height_pos G r T hwT
      have hw1 : height G r T w = 1 := by omega
      have hzw := path_height_one_unique G r T ht hwT hw1 p hp.of_cons hvw.symm hdc.symm hnot' hz
      exact Or.inr ⟨hzw ▸ hchild, by simpa only [hzw] using hw1⟩

theorem fringe_region_nonterminals (ht : G.IsTree) (hr : r ∈ T) (hc : Clean G T)
    (hstar : NoZeroCoreStar G T) {v q : V}
    (hv : v ∉ T) (hh : height G r T v = 2)
    (hq : G.Adj v q) (hdq : G.dist r q + 1 = G.dist r v) :
    ∀ z, (G.deleteEdges {s(v, q)}).Reachable v z → z ∉ T →
      z = v ∨ (z ∈ children G r v ∧ height G r T z = 1) := by
  intro z hz hzT
  obtain ⟨p, hp⟩ := SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hz
  exact path_height_two_nonterminal G r T ht hr hc hstar hv hh p.toPath p.toPath.isPath
    hq hdq (fun h => hp (p.edges_toPath_subset_edges h)) hzT

end SteinerUpperBound.Structural.Rooted
