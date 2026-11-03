module

public import SteinerUpperBound.Structural.Cherries

@[expose] public section

namespace SteinerUpperBound.Structural.Tree.Cherry

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}
variable {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}

noncomputable abbrev crossed (C : Cherry S v) (a b : ↥S.vertices)
    (ha : (S.graph.deleteEdges {s(v, C.center)}).Reachable C.center a)
    (hb : (S.graph.deleteEdges {s(v, C.center)}).Reachable v b) :
    TreeGeometry.TreeSolution I :=
  exchange C.promoted v C.center b a
    ((C.promoted_center_adj v).mpr (Or.inl rfl)).symm
    (C.promoted_trunk_regions hb) (C.promoted_trunk_regions ha)

theorem crossed_center_adj (C : Cherry S v) (a b : ↥S.vertices)
    (ha : (S.graph.deleteEdges {s(v, C.center)}).Reachable C.center a)
    (hb : (S.graph.deleteEdges {s(v, C.center)}).Reachable v b)
    (haT : (a : V) ∈ I.terminals) (hbT : (b : V) ∈ I.terminals)
    (z : ↥S.vertices) : (C.crossed a b ha hb).graph.Adj C.center z ↔ z = C.primary := by
  have hca : C.center ≠ a := fun h => C.center_nonterminal (h ▸ haT)
  have hcb : C.center ≠ b := fun h => C.center_nonterminal (h ▸ hbT)
  constructor
  · intro h
    rcases h with h | h
    · obtain ⟨h, hnot⟩ := SimpleGraph.deleteEdges_adj.mp h
      rcases (C.promoted_center_adj z).mp h with h | h
      · exact False.elim (hnot (by rw [h, Sym2.eq_swap]; exact Set.mem_singleton _))
      · exact h
    · rcases (SimpleGraph.edge_adj b a C.center z).mp h with ⟨h | h, _⟩
      · exact False.elim (hcb h.1)
      · exact False.elim (hca h.1)
  · rintro rfl
    apply Or.inl
    exact SimpleGraph.deleteEdges_adj.mpr
      ⟨(C.promoted_center_adj C.primary).mpr (Or.inr rfl),
        by simpa only [Set.mem_singleton_iff] using C.primary_edge_ne_trunk⟩

theorem crossed_center_degree (C : Cherry S v) (a b : ↥S.vertices)
    (ha : (S.graph.deleteEdges {s(v, C.center)}).Reachable C.center a)
    (hb : (S.graph.deleteEdges {s(v, C.center)}).Reachable v b)
    (haT : (a : V) ∈ I.terminals) (hbT : (b : V) ∈ I.terminals) :
    (C.crossed a b ha hb).graph.degree C.center = 1 := by
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  exact ⟨C.primary, (C.crossed_center_adj a b ha hb haT hbT C.primary).mpr rfl,
    fun z hz => (C.crossed_center_adj a b ha hb haT hbT z).mp hz⟩

noncomputable abbrev eliminate (C : Cherry S v) (a b : ↥S.vertices)
    (ha : (S.graph.deleteEdges {s(v, C.center)}).Reachable C.center a)
    (hb : (S.graph.deleteEdges {s(v, C.center)}).Reachable v b)
    (haT : (a : V) ∈ I.terminals) (hbT : (b : V) ∈ I.terminals) :
    TreeGeometry.TreeSolution I :=
  deleteLeaf (C.crossed a b ha hb) C.center C.center_nonterminal
    (C.crossed_center_degree a b ha hb haT hbT)

theorem eliminate_cost_le (C : Cherry S v) (a b : ↥S.vertices)
    (ha : (S.graph.deleteEdges {s(v, C.center)}).Reachable C.center a)
    (hb : (S.graph.deleteEdges {s(v, C.center)}).Reachable v b)
    (haT : (a : V) ∈ I.terminals) (hbT : (b : V) ∈ I.terminals)
    (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) :
    GraphCost.cost (fun e => w (e.map Subtype.val)) (C.eliminate a b ha hb haT hbT).graph ≤
      GraphCost.cost (fun e => w (e.map Subtype.val)) S.graph -
        w s((C.center : V), (C.secondary : V)) - w s((v : V), (C.center : V)) -
        w s((C.center : V), (C.primary : V)) +
        w s((C.primary : V), (C.secondary : V)) + w s((b : V), (a : V)) := by
  have h1 := exchangeEdge_cost_le S.graph (fun e => w (e.map Subtype.val)) (fun e => hw _)
    (a := C.primary) (b := C.secondary) C.secondary_arm
  change GraphCost.cost (fun e => w (e.map Subtype.val)) C.promoted.graph ≤ _ at h1
  have h2 := exchangeEdge_cost_le C.promoted.graph (fun e => w (e.map Subtype.val))
    (fun e => hw _) (a := b) (b := a)
    ((C.promoted_center_adj v).mpr (Or.inl rfl)).symm
  change GraphCost.cost (fun e => w (e.map Subtype.val)) (C.crossed a b ha hb).graph ≤ _ at h2
  obtain ⟨z, hz, he⟩ := deleteLeaf_cost_add (C.crossed a b ha hb) C.center C.center_nonterminal
    (C.crossed_center_degree a b ha hb haT hbT) w
  have hz' : z = C.primary := (C.crossed_center_adj a b ha hb haT hbT z).mp hz
  subst z
  simp only [Sym2.map_mk] at h1 h2
  change GraphCost.cost (fun e => w (e.map Subtype.val)) (C.eliminate a b ha hb haT hbT).graph +
    w s((C.center : V), (C.primary : V)) = _ at he
  linarith

theorem eliminate_preserves_terminals (C : Cherry S v) (a b : ↥S.vertices)
    (ha : (S.graph.deleteEdges {s(v, C.center)}).Reachable C.center a)
    (hb : (S.graph.deleteEdges {s(v, C.center)}).Reachable v b)
    (haT : (a : V) ∈ I.terminals) (hbT : (b : V) ∈ I.terminals) :
    terminalGraph S ≤ terminalGraph (C.eliminate a b ha hb haT hbT) :=
  (exchange_preserves_terminals S C.center C.secondary C.primary C.secondary C.secondary_arm
    (sibling_cut_reachable S C.center C.secondary C.primary C.secondary_arm C.primary_arm C.ports_ne.symm)
    (SimpleGraph.Reachable.refl _) C.center_nonterminal).trans
      ((exchange_preserves_terminals C.promoted v C.center b a
        ((C.promoted_center_adj v).mpr (Or.inl rfl)).symm
        (C.promoted_trunk_regions hb) (C.promoted_trunk_regions ha) C.attachment_nonterminal).trans
          (deleteLeaf_preserves_terminals (C.crossed a b ha hb) C.center C.center_nonterminal
            (C.crossed_center_degree a b ha hb haT hbT)))

theorem eliminate_reduces (C : Cherry S v) (a b : ↥S.vertices)
    (ha : (S.graph.deleteEdges {s(v, C.center)}).Reachable C.center a)
    (hb : (S.graph.deleteEdges {s(v, C.center)}).Reachable v b)
    (haT : (a : V) ∈ I.terminals) (hbT : (b : V) ∈ I.terminals)
    (hcost : I.distance C.primary C.secondary + I.distance a b ≤
      chi * (I.distance v C.center + I.distance C.center C.primary + I.distance C.center C.secondary)) :
    Reduces S (C.eliminate a b ha hb haT hbT) := by
  classical
  let Q := C.eliminate a b ha hb haT hbT
  have hpot := C.eliminate_cost_le a b ha hb haT hbT (potentialWeight I) (potentialWeight_nonneg I)
  simp only [potentialWeight_mk, potentialDistance, C.center_nonterminal,
    C.attachment_nonterminal, C.primary_terminal, C.secondary_terminal, haT, hbT,
    false_and, and_self, ↓reduceIte] at hpot
  rw [I.distance_comm (b : V) a] at hpot
  have hnn := C.eliminate_cost_le a b ha hb haT hbT (nonterminalWeight I) (nonterminalWeight_nonneg I)
  have hn1 := nonterminalWeight_nonneg I s((C.center : V), (C.secondary : V))
  have hn2 := nonterminalWeight_nonneg I s((v : V), (C.center : V))
  have hn3 := nonterminalWeight_nonneg I s((C.center : V), (C.primary : V))
  have hn4 : nonterminalWeight I s((C.primary : V), (C.secondary : V)) = 0 := by
    simp [nonterminalWeight_mk, nonterminalDistance, C.primary_terminal]
  have hn5 : nonterminalWeight I s((b : V), (a : V)) = 0 := by
    simp [nonterminalWeight_mk, nonterminalDistance, hbT]
  rw [hn4, hn5] at hnn
  have hab : (b : V) ≠ (a : V) := by
    intro h
    exact exchange_added_ne S C.trunk hb ha (Subtype.ext h)
  have hpq : (C.primary : V) ≠ (C.secondary : V) := fun h => C.ports_ne (Subtype.ext h)
  have hnew1 : steinerCountWeight I s((C.primary : V), (C.secondary : V)) = 0 := by
    simp [steinerCountWeight, SimpleGraph.mem_edgeSet, Network.completeOn_adj,
      hpq, C.primary_terminal, C.secondary_terminal]
  have hnew2 : steinerCountWeight I s((b : V), (a : V)) = 0 := by
    simp [steinerCountWeight, SimpleGraph.mem_edgeSet, Network.completeOn_adj, hab, hbT, haT]
  have hcount := C.eliminate_cost_le a b ha hb haT hbT (steinerCountWeight I)
    (steinerCountWeight_nonneg I)
  simp only [steinerCountWeight_incident I C.center_nonterminal,
    steinerCountWeight_incident I C.attachment_nonterminal, hnew1, hnew2, add_zero] at hcount
  change GraphCost.cost (fun e => steinerCountWeight I (e.map Subtype.val)) Q.graph ≤
    GraphCost.cost (fun e => steinerCountWeight I (e.map Subtype.val)) S.graph - 1 - 1 - 1 at hcount
  rw [steinerCountWeight_cost Q, steinerCountWeight_cost S] at hcount
  have hcountN : (steinerEdges Q).card + 3 ≤ (steinerEdges S).card := by
    exact_mod_cast (show ((steinerEdges Q).card : ℝ) + 3 ≤ (steinerEdges S).card by linarith)
  refine ⟨by exact Finset.erase_subset _ _, C.eliminate_preserves_terminals a b ha hb haT hbT,
    ?_, ?_, by change (steinerEdges Q).card < (steinerEdges S).card; omega⟩
  · change GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) Q.graph ≤
      GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) S.graph
    change GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) Q.graph ≤ _ at hpot
    nlinarith
  · change GraphCost.cost (fun e => nonterminalWeight I (e.map Subtype.val)) Q.graph ≤
      GraphCost.cost (fun e => nonterminalWeight I (e.map Subtype.val)) S.graph
    change GraphCost.cost (fun e => nonterminalWeight I (e.map Subtype.val)) Q.graph ≤ _ at hnn
    linarith

theorem crossing_barrier (C : Cherry S v) (hred : Reduced S) (a b : ↥S.vertices)
    (ha : (S.graph.deleteEdges {s(v, C.center)}).Reachable C.center a)
    (hb : (S.graph.deleteEdges {s(v, C.center)}).Reachable v b)
    (haT : (a : V) ∈ I.terminals) (hbT : (b : V) ∈ I.terminals) :
    p * (I.distance v C.center + I.distance C.center C.primary) < I.distance a b := by
  have hstrict : chi *
      (I.distance v C.center + I.distance C.center C.primary + I.distance C.center C.secondary) <
      I.distance C.primary C.secondary + I.distance a b := by
    by_contra h
    exact hred _ (C.eliminate_reduces a b ha hb haT hbT (le_of_not_gt h))
  have ht := I.distance_triangle (C.primary : V) C.center C.secondary
  rw [I.distance_comm (C.primary : V) C.center] at ht
  have hz := I.distance_nonneg v C.center
  have hs := C.ordered
  norm_num [p, chi, e0] at hstrict ⊢
  nlinarith

theorem crossing_barrier_strong (C : Cherry S v) (hred : Reduced S) (a b : ↥S.vertices)
    (ha : (S.graph.deleteEdges {s(v, C.center)}).Reachable C.center a)
    (hb : (S.graph.deleteEdges {s(v, C.center)}).Reachable v b)
    (haT : (a : V) ∈ I.terminals) (hbT : (b : V) ∈ I.terminals) :
    chi * I.distance v C.center +
      (chi - 1) * (I.distance C.center C.primary + I.distance C.center C.secondary) <
        I.distance a b := by
  have hstrict : chi *
      (I.distance v C.center + I.distance C.center C.primary + I.distance C.center C.secondary) <
      I.distance C.primary C.secondary + I.distance a b := by
    by_contra h
    exact hred _ (C.eliminate_reduces a b ha hb haT hbT (le_of_not_gt h))
  have ht := I.distance_triangle (C.primary : V) C.center C.secondary
  rw [I.distance_comm (C.primary : V) C.center] at ht
  nlinarith

end SteinerUpperBound.Structural.Tree.Cherry
