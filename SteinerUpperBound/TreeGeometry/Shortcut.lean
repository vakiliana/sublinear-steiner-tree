module

public import SteinerUpperBound.TreeGeometry.Tour

@[expose] public section

namespace SteinerUpperBound.TreeGeometry

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*}

theorem routeCost_change_start (I : Instance V) (x y : V) (l : List V) :
    routeCost I x l ≤ I.distance x y + routeCost I y l := by
  cases l with
  | nil => simpa only [routeCost_nil, add_zero] using I.distance_nonneg x y
  | cons z l =>
    simp only [routeCost_cons]
    linarith [I.distance_triangle x y z]

theorem routeCost_sublist (I : Instance V) (x : V) {l m : List V} (h : l.Sublist m) :
    routeCost I x l ≤ routeCost I x m := by
  induction h generalizing x with
  | slnil => exact le_rfl
  | @cons l m a h ih =>
    exact (routeCost_change_start I x a l).trans (add_le_add (le_refl _) (ih a))
  | @cons_cons l m a h ih =>
    exact add_le_add (le_refl _) (ih a)

theorem routeEnd_filter (p : V → Prop) [DecidablePred p] (x : V) (l : List V)
    (hl : p (routeEnd x l)) :
    routeEnd x (l.filter p) = routeEnd x l := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih =>
    by_cases hy : p y
    · rw [List.filter_cons_of_pos (p := fun z => decide (p z)) (decide_eq_true hy)]
      exact ih y hl
    · rw [List.filter_cons_of_neg (by simpa only [decide_eq_true_eq] using hy)]
      have hh := ih y hl
      cases he : l.filter p with
      | nil =>
        have he' : routeEnd y l = y := by simpa only [he, routeEnd_nil] using hh.symm
        exact False.elim (hy (by simpa only [routeEnd_cons, he'] using hl))
      | cons z m =>
        simpa only [he, routeEnd_cons] using hh

theorem terminal_tour_of_tree (I : Instance V) (S : TreeSolution I)
    (r : V) (hr : r ∈ I.terminals) :
    ∃ l : List V, routeEnd r l = r ∧
      (∀ z ∈ r :: l, z ∈ I.terminals) ∧
      (∀ z ∈ I.terminals, z ∈ r :: l) ∧
      routeCost I r l ≤ 2 * S.cost := by
  classical
  obtain ⟨l, hl, hvisit, hc⟩ :=
    exists_tree_tour I S.graph S.isTree Subtype.val ⟨r, S.contains hr⟩
  refine ⟨l.filter (fun z => z ∈ I.terminals), ?_, ?_, ?_, ?_⟩
  · exact (routeEnd_filter _ r l (by simpa only [hl] using hr)).trans hl
  · intro z hz
    rcases List.mem_cons.mp hz with h | h
    · simpa only [h] using hr
    · exact of_decide_eq_true (List.mem_filter.mp h).2
  · intro z hz
    rcases List.mem_cons.mp (hvisit ⟨z, S.contains hz⟩) with h | h
    · exact List.mem_cons.mpr (Or.inl h)
    · exact List.mem_cons.mpr (Or.inr (List.mem_filter.mpr ⟨h, decide_eq_true hz⟩))
  · exact (routeCost_sublist I r List.filter_sublist).trans hc

theorem cost_sup_le [Fintype V] (w : Sym2 V → ℝ)
    (G H : SimpleGraph V) (hw : ∀ e, 0 ≤ w e) :
    GraphCost.cost w (G ⊔ H) ≤ GraphCost.cost w G + GraphCost.cost w H := by
  classical
  let : DecidableRel (G ⊔ H).Adj := fun _ _ => Classical.propDecidable _
  unfold GraphCost.cost
  have hh := Finset.sum_union_inter (s₁ := G.edgeFinset) (s₂ := H.edgeFinset) (f := w)
  have hn : 0 ≤ ∑ e ∈ G.edgeFinset ∩ H.edgeFinset, w e :=
    Finset.sum_nonneg fun e _ => hw e
  calc
    _ = ∑ e ∈ G.edgeFinset ∪ H.edgeFinset, w e := by
      apply Finset.sum_congr
      · ext e
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_sup, Set.mem_union,
          Finset.mem_union]
      · intro e _
        rfl
    _ ≤ _ := by linarith

theorem cost_single_edge_le [Fintype V] (I : Instance V) (x y : V) :
    GraphCost.cost I.weight (SimpleGraph.fromEdgeSet {s(x, y)}) ≤ I.distance x y := by
  classical
  let : DecidableRel (SimpleGraph.fromEdgeSet {s(x, y)} : SimpleGraph V).Adj :=
    fun _ _ => Classical.propDecidable _
  let : Fintype (SimpleGraph.fromEdgeSet {s(x, y)} : SimpleGraph V).edgeSet :=
    SimpleGraph.fintypeEdgeSet _
  unfold GraphCost.cost
  calc
    _ ≤ ∑ e ∈ ({s(x, y)} : Finset (Sym2 V)), I.weight e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet,
          Set.mem_sdiff, Set.mem_singleton_iff] at he
        exact Finset.mem_singleton.mpr he.1
      · intro e _ _
        exact I.weight_nonneg e
    _ = _ := by simp

noncomputable def routeGraph (x : V) : List V → SimpleGraph V
  | [] => ⊥
  | y :: l => SimpleGraph.fromEdgeSet {s(x, y)} ⊔ routeGraph y l

theorem routeGraph_reachable (x : V) (l : List V) (z : V) (hz : z ∈ x :: l) :
    (routeGraph x l).Reachable x z := by
  induction l generalizing x with
  | nil =>
    have hzx : z = x := List.mem_singleton.mp hz
    subst z
    exact SimpleGraph.Reachable.refl _
  | cons y l ih =>
    rcases List.mem_cons.mp hz with h | h
    · subst z
      exact SimpleGraph.Reachable.refl _
    · have hxy : (routeGraph x (y :: l)).Reachable x y := by
        by_cases he : x = y
        · subst y
          exact SimpleGraph.Reachable.refl _
        · apply SimpleGraph.Adj.reachable
          exact Or.inl ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨Set.mem_singleton _, he⟩)
      exact hxy.trans ((ih y h).mono le_sup_right)

theorem routeGraph_terminalOnly (T : Finset V) (x : V) (l : List V)
    (hT : ∀ z ∈ x :: l, z ∈ T) : Network.TerminalOnly T (routeGraph x l) := by
  induction l generalizing x with
  | nil => exact Network.bot_terminalOnly T
  | cons y l ih =>
    intro a b hab
    rcases hab with hab | hab
    · have he : s(a, b) = s(x, y) :=
        Set.mem_singleton_iff.mp ((SimpleGraph.fromEdgeSet_adj _).mp hab).1
      have hx := hT x (by simp)
      have hy := hT y (by simp)
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hx, hy⟩
      · exact ⟨hy, hx⟩
    · exact ih y (fun z hz => hT z (List.mem_cons_of_mem _ hz)) a b hab

theorem routeGraph_cost_le [Fintype V] (I : Instance V) (x : V) (l : List V) :
    GraphCost.cost I.weight (routeGraph x l) ≤ routeCost I x l := by
  induction l generalizing x with
  | nil => simp only [routeGraph, routeCost_nil, Network.cost_bot, le_refl]
  | cons y l ih =>
    exact (cost_sup_le _ _ _ I.weight_nonneg).trans
      (add_le_add (cost_single_edge_le I x y) (ih y))

theorem mst_le_routeCost [Fintype V] (I : Instance V) (r : V) (l : List V)
    (hT : ∀ z ∈ r :: l, z ∈ I.terminals)
    (hcover : ∀ z ∈ I.terminals, z ∈ r :: l) :
    I.mst ≤ routeCost I r l := by
  apply (I.mst_le (routeGraph r l) ?_ (routeGraph_terminalOnly _ _ _ hT)).trans
    (routeGraph_cost_le I r l)
  intro x hx y hy
  exact (routeGraph_reachable r l x (hcover x hx)).symm.trans
    (routeGraph_reachable r l y (hcover y hy))

theorem mst_le_twice_optimum [Fintype V] (I : Instance V) :
    I.mst ≤ 2 * I.optimum := by
  classical
  by_cases hT : I.terminals.Nonempty
  · obtain ⟨r, hr⟩ := hT
    obtain ⟨S, hS⟩ := optimum_tree_attained I ⟨r, hr⟩
    obtain ⟨l, _, hterminal, hcover, hcost⟩ := terminal_tour_of_tree I S r hr
    exact (mst_le_routeCost I r l hterminal hcover).trans (by simpa only [hS] using hcost)
  · have hk : I.terminals.card ≤ 1 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hT]
      simp
    rw [I.mst_eq_zero hk, I.optimum_eq_zero hk]
    norm_num

theorem terminal_tour_mst [Fintype V] (I : Instance V) (r : V) (hr : r ∈ I.terminals) :
    ∃ l : List V, routeEnd r l = r ∧
      (∀ z ∈ r :: l, z ∈ I.terminals) ∧
      (∀ z ∈ I.terminals, z ∈ r :: l) ∧
      routeCost I r l ≤ 2 * I.mst := by
  obtain ⟨G, hG, _, hc⟩ := I.mst_attained
  obtain ⟨S, hS⟩ := exists_tree_cost_le I ⟨r, hr⟩ G hG
  obtain ⟨l, hl, hterm, hcover, hcost⟩ := terminal_tour_of_tree I S r hr
  exact ⟨l, hl, hterm, hcover, hcost.trans (by linarith)⟩

theorem distance_le_walk_sum (I : Instance V) {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) : I.distance x y ≤ (p.edges.map I.weight).sum := by
  induction p with
  | nil => simp [I.distance_self]
  | @cons a b c hab p ih =>
    simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, Instance.weight_mk]
    exact (I.distance_triangle a b c).trans (add_le_add (le_refl _) ih)

theorem distance_le_cost_of_reachable [Fintype V] (I : Instance V)
    (G : SimpleGraph V) {x y : V} (hxy : G.Reachable x y) :
    I.distance x y ≤ GraphCost.cost I.weight G := by
  classical
  obtain ⟨p, hp⟩ := hxy.exists_isPath
  apply (distance_le_walk_sum I p).trans
  rw [← List.sum_toFinset I.weight hp.isTrail.edges_nodup]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [SimpleGraph.mem_edgeFinset]
    exact p.edges_subset_edgeSet (List.mem_toFinset.mp he)
  · intro e _ _
    exact I.weight_nonneg e

theorem terminal_distance_le_optimum [Fintype V] (I : Instance V)
    {x y : V} (hx : x ∈ I.terminals) (hy : y ∈ I.terminals) :
    I.distance x y ≤ I.optimum := by
  obtain ⟨G, hG, he⟩ := I.optimum_attained
  exact (distance_le_cost_of_reachable I G (hG x hx y hy)).trans_eq he

theorem terminal_distance_le_mst [Fintype V] (I : Instance V)
    {x y : V} (hx : x ∈ I.terminals) (hy : y ∈ I.terminals) :
    I.distance x y ≤ I.mst :=
  (terminal_distance_le_optimum I hx hy).trans I.optimum_le_mst

end SteinerUpperBound.TreeGeometry
