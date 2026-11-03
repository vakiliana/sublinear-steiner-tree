module

public import SteinerUpperBound.Structural.Suppression
public import SteinerUpperBound.Structural.Weights

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

theorem cleanup_weights {ι : Type*} (S : TreeGeometry.TreeSolution I)
    (hT : I.terminals.Nonempty) (weights : ι → Sym2 V → ℝ)
    (hnonneg : ∀ i e, 0 ≤ weights i e)
    (htriangle : ∀ i v, v ∉ I.terminals → ∀ x y,
      weights i s(x, y) ≤ weights i s(v, x) + weights i s(v, y)) :
    ∃ Q : TreeGeometry.TreeSolution I,
      Q.vertices ⊆ S.vertices ∧ Q.IsClean ∧ terminalGraph S ≤ terminalGraph Q ∧
      ∀ i, GraphCost.cost (fun e => weights i (e.map Subtype.val)) Q.graph ≤
        GraphCost.cost (fun e => weights i (e.map Subtype.val)) S.graph := by
  classical
  have hex : ∃ n : ℕ, ∃ Q : TreeGeometry.TreeSolution I,
      Q.vertices ⊆ S.vertices ∧ terminalGraph S ≤ terminalGraph Q ∧
      (∀ i, GraphCost.cost (fun e => weights i (e.map Subtype.val)) Q.graph ≤
        GraphCost.cost (fun e => weights i (e.map Subtype.val)) S.graph) ∧ Q.vertices.card = n :=
    ⟨S.vertices.card, S, Finset.Subset.refl _, le_rfl, fun _ => le_rfl, rfl⟩
  obtain ⟨Q, hsub, hperm, hcost, hcard⟩ := Nat.find_spec hex
  refine ⟨Q, hsub, ?_, hperm, hcost⟩
  intro v hv
  by_contra hdeg
  obtain ⟨t, ht⟩ := hT
  have hvt : v ≠ (⟨t, Q.contains ht⟩ : ↥Q.vertices) := by
    intro h
    exact hv (by simpa only [h] using ht)
  have hpos : 0 < Q.graph.degree v :=
    (Q.isTree.connected v ⟨t, Q.contains ht⟩).degree_pos_left hvt
  have hstep : ∃ R : TreeGeometry.TreeSolution I,
      R.vertices = Q.vertices.erase (v : V) ∧ terminalGraph Q ≤ terminalGraph R ∧
      ∀ i, GraphCost.cost (fun e => weights i (e.map Subtype.val)) R.graph ≤
        GraphCost.cost (fun e => weights i (e.map Subtype.val)) Q.graph := by
    by_cases hd1 : Q.graph.degree v = 1
    · refine ⟨deleteLeaf Q v hv hd1, rfl, deleteLeaf_preserves_terminals Q v hv hd1, ?_⟩
      intro i
      obtain ⟨x, _, he⟩ := deleteLeaf_cost_add Q v hv hd1 (weights i)
      have hn := hnonneg i s((v : V), (x : V))
      linarith
    · have hd2 : (Q.graph.neighborFinset v).card = 2 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        omega
      obtain ⟨x, y, hxy, he⟩ := Finset.card_eq_two.mp hd2
      have hadj (z : ↥Q.vertices) : Q.graph.Adj v z ↔ z = x ∨ z = y := by
        have hh := Finset.ext_iff.mp he z
        simpa only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton] using hh
      have hvx := (hadj x).mpr (Or.inl rfl)
      have hvy := (hadj y).mpr (Or.inr rfl)
      have hn := fun z hz => (hadj z).mp hz
      refine ⟨suppress Q v x y hv hvx hvy hxy hn, rfl,
        suppress_preserves_terminals Q v x y hv hvx hvy hxy hn, ?_⟩
      intro i
      have hs := suppress_cost_le Q v x y hv hvx hvy hxy hn (weights i) (hnonneg i)
      have ht := htriangle i (v : V) hv (y : V) (x : V)
      linarith
  obtain ⟨R, hRvertices, hRperm, hRcost⟩ := hstep
  have hRsub : R.vertices ⊆ S.vertices := by
    rw [hRvertices]
    exact (Finset.erase_subset _ _).trans hsub
  have hmin := Nat.find_min' hex
    ⟨R, hRsub, hperm.trans hRperm, fun i => (hRcost i).trans (hcost i), rfl⟩
  have hlt : R.vertices.card < Q.vertices.card := by
    rw [hRvertices]
    exact Finset.card_erase_lt_of_mem v.property
  omega

theorem cleanup_preserving (S : TreeGeometry.TreeSolution I) (hT : I.terminals.Nonempty) :
    ∃ Q : TreeGeometry.TreeSolution I, Q.vertices ⊆ S.vertices ∧ Q.IsClean ∧
      potential Q ≤ potential S ∧ nonterminalCost Q ≤ nonterminalCost S ∧
      terminalGraph S ≤ terminalGraph Q ∧ (steinerEdges Q).card ≤ (steinerEdges S).card := by
  let w : Fin 3 → Sym2 V → ℝ :=
    fun i => if i = 0 then potentialWeight I else if i = 1 then nonterminalWeight I
      else steinerCountWeight I
  have hnonneg : ∀ i e, 0 ≤ w i e := by
    intro i e
    fin_cases i
    · exact potentialWeight_nonneg I e
    · exact nonterminalWeight_nonneg I e
    · exact steinerCountWeight_nonneg I e
  have htri : ∀ i v, v ∉ I.terminals → ∀ x y,
      w i s(x, y) ≤ w i s(v, x) + w i s(v, y) := by
    intro i v hv x y
    fin_cases i
    · exact potentialWeight_triangle_at_nonterminal I hv x y
    · exact nonterminalWeight_triangle_at_nonterminal I hv x y
    · exact steinerCountWeight_triangle_at_nonterminal I hv x y
  obtain ⟨Q, hsub, hclean, hperm, hc⟩ := cleanup_weights S hT w hnonneg htri
  refine ⟨Q, hsub, hclean, hc 0, hc 1, hperm, ?_⟩
  have hh := hc 2
  change GraphCost.cost (fun e => steinerCountWeight I (e.map Subtype.val)) Q.graph ≤
    GraphCost.cost (fun e => steinerCountWeight I (e.map Subtype.val)) S.graph at hh
  rw [steinerCountWeight_cost, steinerCountWeight_cost] at hh
  exact_mod_cast hh

end SteinerUpperBound.Structural.Tree
