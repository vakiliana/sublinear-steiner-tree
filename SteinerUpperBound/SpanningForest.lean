module

public import SteinerUpperBound.GraphRank
public import SteinerUpperBound.WeightedSelection

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerUpperBound.SpanningForest

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*}

noncomputable def linked (G : SimpleGraph V) : Sym2 V → Prop :=
  Sym2.lift ⟨G.Reachable, fun _ _ => propext ⟨fun h => h.symm, fun h => h.symm⟩⟩

@[simp]
theorem linked_mk (G : SimpleGraph V) (x y : V) :
    linked G (Sym2.mk x y) ↔ G.Reachable x y := Iff.rfl

noncomputable def step (G : SimpleGraph V) (e : Sym2 V) : SimpleGraph V :=
  if linked G e then G else G ⊔ SimpleGraph.fromEdgeSet {e}

noncomputable def run : List (Sym2 V) → SimpleGraph V → SimpleGraph V
  | [], G => G
  | e :: l, G => run l (step G e)

noncomputable def picked : List (Sym2 V) → SimpleGraph V → List (Sym2 V)
  | [], _ => []
  | e :: l, G =>
      if linked G e then picked l G
      else e :: picked l (G ⊔ SimpleGraph.fromEdgeSet {e})

noncomputable def trace : List (Sym2 V) → SimpleGraph V → List (Sym2 V × Bool)
  | [], _ => []
  | e :: l, G => (e, decide (¬linked G e)) :: trace l (step G e)

theorem le_step (G : SimpleGraph V) (e : Sym2 V) : G ≤ step G e := by
  unfold step
  split_ifs
  · rfl
  · exact le_sup_left

theorem step_le (G : SimpleGraph V) (e : Sym2 V) :
    step G e ≤ G ⊔ SimpleGraph.fromEdgeSet {e} := by
  unfold step
  split_ifs
  · exact le_sup_left
  · rfl

theorem le_run (l : List (Sym2 V)) (G : SimpleGraph V) : G ≤ run l G := by
  induction l generalizing G with
  | nil => rfl
  | cons e l ih => exact (le_step G e).trans (ih _)

theorem run_le (l : List (Sym2 V)) (G : SimpleGraph V) :
    run l G ≤ G ⊔ GraphRank.ofEdges l.toFinset := by
  induction l generalizing G with
  | nil => simp only [run, List.toFinset_nil, GraphRank.ofEdges_empty, sup_bot_eq, le_refl]
  | cons e l ih =>
      calc
        _ ≤ step G e ⊔ GraphRank.ofEdges l.toFinset := ih _
        _ ≤ (G ⊔ SimpleGraph.fromEdgeSet {e}) ⊔ GraphRank.ofEdges l.toFinset :=
          sup_le_sup (step_le G e) le_rfl
        _ = _ := by
          rw [List.toFinset_cons, GraphRank.ofEdges_insert]
          ac_rfl

theorem run_append (l₁ l₂ : List (Sym2 V)) (G : SimpleGraph V) :
    run (l₁ ++ l₂) G = run l₂ (run l₁ G) := by
  induction l₁ generalizing G with
  | nil => rfl
  | cons e l ih => exact ih _

theorem picked_append (l₁ l₂ : List (Sym2 V)) (G : SimpleGraph V) :
    picked (l₁ ++ l₂) G = picked l₁ G ++ picked l₂ (run l₁ G) := by
  induction l₁ generalizing G with
  | nil => rfl
  | cons e l ih =>
      by_cases he : linked G e
      · simp only [List.cons_append, picked, he, ite_true, run, step, ih]
      · simp only [picked, he, ite_false, run, step, ih, List.cons_append]

theorem picked_sublist (l : List (Sym2 V)) (G : SimpleGraph V) : (picked l G).Sublist l := by
  induction l generalizing G with
  | nil => exact List.Sublist.refl _
  | cons e l ih =>
      by_cases he : linked G e
      · simp only [picked, he, ite_true]
        exact List.Sublist.cons e (ih _)
      · simp only [picked, he, ite_false]
        exact List.Sublist.cons₂ e (ih _)

theorem step_space (G : SimpleGraph V) (e : Sym2 V) :
    GraphRank.space (step G e) = GraphRank.space G ⊔ GraphRank.space (SimpleGraph.fromEdgeSet {e}) := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      by_cases hxy : G.Reachable x y
      · have he : linked G (Sym2.mk x y) := hxy
        simp only [step, he, ite_true]
        change GraphRank.space G =
          GraphRank.space G ⊔ GraphRank.space (SimpleGraph.edge x y)
        rw [GraphRank.space_edge]
        have hs : Submodule.span ℝ {GraphRank.delta x y} ≤ GraphRank.space G :=
          Submodule.span_le.mpr (fun z hz =>
            (Set.mem_singleton_iff.mp hz) ▸ GraphRank.reachable_mem G hxy)
        exact (sup_eq_left.mpr hs).symm
      · have he : ¬linked G (Sym2.mk x y) := hxy
        simp only [step, he, ite_false, GraphRank.space_sup]

theorem run_space (l : List (Sym2 V)) (G : SimpleGraph V) :
    GraphRank.space (run l G) = GraphRank.space G ⊔ GraphRank.space (GraphRank.ofEdges l.toFinset) := by
  induction l generalizing G with
  | nil => simp only [run, List.toFinset_nil, GraphRank.ofEdges_empty, GraphRank.space_bot, sup_bot_eq]
  | cons e l ih =>
      simp only [run, ih, step_space, List.toFinset_cons, GraphRank.ofEdges_insert, GraphRank.space_sup]
      ac_rfl

theorem run_graph (l : List (Sym2 V)) (G : SimpleGraph V) :
    run l G = G ⊔ GraphRank.ofEdges (picked l G).toFinset := by
  induction l generalizing G with
  | nil => simp only [run, picked, List.toFinset_nil, GraphRank.ofEdges_empty, sup_bot_eq]
  | cons e l ih =>
      by_cases he : linked G e
      · simp only [run, step, he, ite_true, picked, ih]
      · simp only [run, step, he, ite_false, picked, ih, List.toFinset_cons, GraphRank.ofEdges_insert]
        ac_rfl

theorem trace_map (l : List (Sym2 V)) (G : SimpleGraph V) :
    (trace l G).map Prod.fst = l := by
  induction l generalizing G with
  | nil => rfl
  | cons e l ih => simp only [trace, List.map_cons, ih]

theorem trace_drop (l : List (Sym2 V)) (G : SimpleGraph V) (i : ℕ) :
    (trace l G).drop i = trace (l.drop i) (run (l.take i) G) := by
  induction i generalizing l G with
  | zero => simp only [List.drop_zero, List.take_zero, run]
  | succ i ih =>
      cases l with
      | nil => simp [trace, run]
      | cons e l =>
          simp only [trace, List.drop_succ_cons, List.take_succ_cons, run]
          exact ih l (step G e)

theorem trace_count (l : List (Sym2 V)) (G : SimpleGraph V) :
    WeightedSelection.count Prod.snd (trace l G) = (picked l G).length := by
  induction l generalizing G with
  | nil => rfl
  | cons e l ih =>
      by_cases he : linked G e <;>
        simp [trace, step, picked, he, WeightedSelection.count] at ih ⊢
      · exact ih _
      · exact ih _

theorem trace_count_other (l : List (Sym2 V)) (G : SimpleGraph V) (q : Sym2 V → Bool) :
    WeightedSelection.count (fun z => q z.1) (trace l G) = WeightedSelection.count q l := by
  induction l generalizing G with
  | nil => rfl
  | cons e l ih =>
      cases hq : q e <;> simp [trace, WeightedSelection.count, hq] at ih ⊢ <;> exact ih _

theorem trace_weight (w : Sym2 V → ℝ) (l : List (Sym2 V)) (G : SimpleGraph V) :
    ((trace l G).map (fun z => if z.2 then w z.1 else 0)).sum = ((picked l G).map w).sum := by
  induction l generalizing G with
  | nil => rfl
  | cons e l ih =>
      by_cases he : linked G e <;> simp [trace, step, picked, he, ih]

theorem trace_weight_other (w : Sym2 V → ℝ) (l : List (Sym2 V)) (G : SimpleGraph V)
    (q : Sym2 V → Bool) :
    ((trace l G).map (fun z => if q z.1 then w z.1 else 0)).sum =
      (l.map (fun e => if q e then w e else 0)).sum := by
  induction l generalizing G with
  | nil => rfl
  | cons e l ih => simp only [trace, List.map_cons, List.sum_cons, ih]

variable [Fintype V]

theorem rank_step (G : SimpleGraph V) (e : Sym2 V) :
    GraphRank.rank (step G e) = GraphRank.rank G + if linked G e then 0 else 1 := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      by_cases hxy : G.Reachable x y
      · have he : linked G (Sym2.mk x y) := hxy
        simp only [step, he, ite_true, Nat.add_zero]
      · have he : ¬linked G (Sym2.mk x y) := hxy
        simp only [step, he, ite_false]
        exact GraphRank.rank_add_edge G x y hxy

theorem rank_run (l : List (Sym2 V)) (G : SimpleGraph V) :
    GraphRank.rank (run l G) = GraphRank.rank G + (picked l G).length := by
  induction l generalizing G with
  | nil => simp only [run, picked, List.length_nil, Nat.add_zero]
  | cons e l ih =>
      by_cases he : linked G e
      · simp only [run, step, picked, he, ite_true, ih]
      · simp only [run, step, picked, he, ite_false, List.length_cons, ih]
        have hr := rank_step G e
        simp only [step, he, ite_false] at hr
        omega

noncomputable def contribution (w : Sym2 V → ℝ) (G : SimpleGraph V) (e : Sym2 V) : ℝ :=
  if e ∈ G.edgeSet then w e else 0

theorem cost_sum (w : Sym2 V → ℝ) (G : SimpleGraph V) :
    GraphCost.cost w G = ∑ e, contribution w G e := by
  have he : G.edgeFinset = Finset.univ.filter (fun e => e ∈ G.edgeSet) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [GraphCost.cost, he, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hm : e ∈ G.edgeSet <;> simp [contribution, hm]

theorem cost_sup_edge (w : Sym2 V → ℝ) (G : SimpleGraph V) (x y : V)
    (hxy : x ≠ y) (he : Sym2.mk x y ∉ G.edgeSet) :
    GraphCost.cost w (G ⊔ SimpleGraph.edge x y) = GraphCost.cost w G + w (Sym2.mk x y) := by
  have hp (e : Sym2 V) :
      contribution w (G ⊔ SimpleGraph.edge x y) e =
        contribution w G e + (if e = Sym2.mk x y then w e else 0) := by
    simp only [contribution, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge_of_ne hxy,
      Set.mem_union, Set.mem_singleton_iff]
    by_cases h : e = Sym2.mk x y
    · subst e
      simp [he]
    · simp [h]
  calc
    _ = ∑ e, contribution w (G ⊔ SimpleGraph.edge x y) e := cost_sum _ _
    _ = ∑ e, (contribution w G e +
        (if e = Sym2.mk x y then w e else 0)) := Finset.sum_congr rfl (fun e _ => hp e)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← cost_sum]
      simp

theorem cost_step (w : Sym2 V → ℝ) (G : SimpleGraph V) (e : Sym2 V) :
    GraphCost.cost w (step G e) = GraphCost.cost w G + if linked G e then 0 else w e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      by_cases hxy : G.Reachable x y
      · have he : linked G (Sym2.mk x y) := hxy
        simp only [step, he, ite_true, add_zero]
      · have he : ¬linked G (Sym2.mk x y) := hxy
        simp only [step, he, ite_false]
        apply cost_sup_edge w G x y
        · intro h
          subst y
          exact hxy (SimpleGraph.Reachable.refl x)
        · intro h
          exact hxy (((SimpleGraph.mem_edgeSet G).mp h).reachable)

theorem cost_run (w : Sym2 V → ℝ) (l : List (Sym2 V)) (G : SimpleGraph V) :
    GraphCost.cost w (run l G) = GraphCost.cost w G + ((picked l G).map w).sum := by
  induction l generalizing G with
  | nil => simp only [run, picked, List.map_nil, List.sum_nil, add_zero]
  | cons e l ih =>
      by_cases he : linked G e
      · simp only [run, step, picked, he, ite_true, ih]
      · simp only [run, step, picked, he, ite_false, ih, List.map_cons, List.sum_cons]
        have hc := cost_step w G e
        simp only [step, he, ite_false] at hc
        rw [hc]
        ring

end SteinerUpperBound.SpanningForest
