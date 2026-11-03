module

public import SteinerUpperBound.Structural.CompleteCleanup

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

def Reduces (S Q : TreeGeometry.TreeSolution I) : Prop :=
  Q.vertices ⊆ S.vertices ∧ terminalGraph S ≤ terminalGraph Q ∧
    potential Q ≤ potential S ∧ nonterminalCost Q ≤ nonterminalCost S ∧
    (steinerEdges Q).card < (steinerEdges S).card

def Reduced (S : TreeGeometry.TreeSolution I) : Prop :=
  ∀ Q : TreeGeometry.TreeSolution I, ¬ Reduces S Q

theorem exists_reduced (S : TreeGeometry.TreeSolution I) (hT : I.terminals.Nonempty) :
    ∃ Q : TreeGeometry.TreeSolution I, Q.vertices ⊆ S.vertices ∧ Q.IsClean ∧
      terminalGraph S ≤ terminalGraph Q ∧ potential Q ≤ potential S ∧
      nonterminalCost Q ≤ nonterminalCost S ∧
      (steinerEdges Q).card ≤ (steinerEdges S).card ∧ Reduced Q := by
  classical
  have hex : ∃ n : ℕ, ∃ Q : TreeGeometry.TreeSolution I,
      Q.vertices ⊆ S.vertices ∧ terminalGraph S ≤ terminalGraph Q ∧
      potential Q ≤ potential S ∧ nonterminalCost Q ≤ nonterminalCost S ∧
      (steinerEdges Q).card = n :=
    ⟨(steinerEdges S).card, S, Finset.Subset.refl _, le_rfl, le_rfl, le_rfl, rfl⟩
  obtain ⟨Q, hsub, hperm, hpot, hnn, hcard⟩ := Nat.find_spec hex
  obtain ⟨R, hrsub, hclean, hrpot, hrnn, hrperm, hrcard⟩ := cleanup_preserving Q hT
  have hRsub := hrsub.trans hsub
  have hRperm := hperm.trans hrperm
  have hRpot := hrpot.trans hpot
  have hRnn := hrnn.trans hnn
  have hminR := Nat.find_min' hex ⟨R, hRsub, hRperm, hRpot, hRnn, rfl⟩
  have hminS := Nat.find_min' hex
    ⟨S, Finset.Subset.refl _, le_rfl, le_rfl, le_rfl, rfl⟩
  have hRcard : (steinerEdges R).card = Nat.find hex := by omega
  refine ⟨R, hRsub, hclean, hRperm, hRpot, hRnn, by omega, ?_⟩
  intro Z hZ
  obtain ⟨hzsub, hzperm, hzpot, hznn, hzcard⟩ := hZ
  have hminZ := Nat.find_min' hex
    ⟨Z, hzsub.trans hRsub, hRperm.trans hzperm, hzpot.trans hRpot, hznn.trans hRnn, rfl⟩
  omega

theorem exchange_added_ne (S : TreeGeometry.TreeSolution I)
    {u v a b : ↥S.vertices} (huv : S.graph.Adj u v)
    (ha : (S.graph.deleteEdges {s(u, v)}).Reachable u a)
    (hb : (S.graph.deleteEdges {s(u, v)}).Reachable v b) : a ≠ b := by
  intro hab
  have hreach : (S.graph.deleteEdges {s(u, v)}).Reachable u v := by
    subst b
    exact ha.trans hb.symm
  have hbridge := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp S.isTree.isAcyclic huv
  exact SimpleGraph.isBridge_iff.mp hbridge hreach

theorem exchange_reduces (S : TreeGeometry.TreeSolution I)
    (u v a b : ↥S.vertices) (huv : S.graph.Adj u v)
    (ha : (S.graph.deleteEdges {s(u, v)}).Reachable u a)
    (hb : (S.graph.deleteEdges {s(u, v)}).Reachable v b)
    (hu : (u : V) ∉ I.terminals) (haT : (a : V) ∈ I.terminals) (hbT : (b : V) ∈ I.terminals)
    (hcost : I.distance a b ≤ chi * I.distance u v) :
    Reduces S (exchange S u v a b huv ha hb) := by
  classical
  let Q := exchange S u v a b huv ha hb
  have hne : (a : V) ≠ (b : V) := by
    intro h
    exact exchange_added_ne S huv ha hb (Subtype.ext h)
  have hnewT : s((a : V), (b : V)) ∈ (Network.completeOn I.terminals).edgeSet :=
    (Network.completeOn_adj _ _ _).mpr ⟨hne, haT, hbT⟩
  have hpot := exchangeEdge_cost_le S.graph (fun e => potentialWeight I (e.map Subtype.val))
    (fun e => potentialWeight_nonneg I _) (a := a) (b := b) huv
  simp only [Sym2.map_mk, potentialWeight_mk, potentialDistance, hu, false_and,
    haT, hbT, and_self, ↓reduceIte] at hpot
  have hnn := exchangeEdge_cost_le S.graph (fun e => nonterminalWeight I (e.map Subtype.val))
    (fun e => nonterminalWeight_nonneg I _) (a := a) (b := b) huv
  have hnnNew : nonterminalWeight I s((a : V), (b : V)) = 0 := by
    simp [nonterminalWeight_mk, nonterminalDistance, haT]
  simp only [Sym2.map_mk, hnnNew, add_zero] at hnn
  have hnnOld := nonterminalWeight_nonneg I s((u : V), (v : V))
  have hcount := exchangeEdge_cost_le S.graph (fun e => steinerCountWeight I (e.map Subtype.val))
    (fun e => steinerCountWeight_nonneg I _) (a := a) (b := b) huv
  have hnewCount : steinerCountWeight I s((a : V), (b : V)) = 0 := by
    simp only [steinerCountWeight, hnewT, ↓reduceIte]
  simp only [Sym2.map_mk, steinerCountWeight_incident I hu, hnewCount, add_zero] at hcount
  change GraphCost.cost (fun e => steinerCountWeight I (e.map Subtype.val)) Q.graph ≤
    GraphCost.cost (fun e => steinerCountWeight I (e.map Subtype.val)) S.graph - 1 at hcount
  rw [steinerCountWeight_cost, steinerCountWeight_cost] at hcount
  have hcountN : (steinerEdges Q).card + 1 ≤ (steinerEdges S).card := by
    exact_mod_cast (show ((steinerEdges Q).card : ℝ) + 1 ≤ (steinerEdges S).card by linarith)
  refine ⟨Finset.Subset.refl _, exchange_preserves_terminals S u v a b huv ha hb hu,
    ?_, ?_, Nat.lt_of_succ_le hcountN⟩
  · change GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) Q.graph ≤
      GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) S.graph
    change GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) Q.graph ≤ _ at hpot
    linarith
  · change GraphCost.cost (fun e => nonterminalWeight I (e.map Subtype.val)) Q.graph ≤
      GraphCost.cost (fun e => nonterminalWeight I (e.map Subtype.val)) S.graph
    change GraphCost.cost (fun e => nonterminalWeight I (e.map Subtype.val)) Q.graph ≤ _ at hnn
    linarith

theorem reduced_cut_barrier (S : TreeGeometry.TreeSolution I) (hred : Reduced S)
    (u v a b : ↥S.vertices) (huv : S.graph.Adj u v)
    (ha : (S.graph.deleteEdges {s(u, v)}).Reachable u a)
    (hb : (S.graph.deleteEdges {s(u, v)}).Reachable v b)
    (hu : (u : V) ∉ I.terminals) (haT : (a : V) ∈ I.terminals) (hbT : (b : V) ∈ I.terminals) :
    chi * I.distance u v < I.distance a b := by
  by_contra h
  exact hred _ (exchange_reduces S u v a b huv ha hb hu haT hbT (le_of_not_gt h))

end SteinerUpperBound.Structural.Tree
