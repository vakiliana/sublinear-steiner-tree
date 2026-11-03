module

public import SteinerUpperBound.Structural.Statistics

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*}

noncomputable def potentialDistance (I : Instance V) (x y : V) : ℝ :=
  if x ∈ I.terminals ∧ y ∈ I.terminals then I.distance x y else chi * I.distance x y

theorem potentialDistance_comm (I : Instance V) (x y : V) :
    potentialDistance I x y = potentialDistance I y x := by
  classical
  simp only [potentialDistance, I.distance_comm x y, and_comm]

noncomputable def potentialWeight (I : Instance V) : Sym2 V → ℝ :=
  Sym2.lift ⟨potentialDistance I, potentialDistance_comm I⟩

@[simp] theorem potentialWeight_mk (I : Instance V) (x y : V) :
    potentialWeight I s(x, y) = potentialDistance I x y := by
  rw [potentialWeight, Sym2.lift_mk]

theorem potentialWeight_nonneg (I : Instance V) (e : Sym2 V) :
    0 ≤ potentialWeight I e := by
  classical
  rcases e with ⟨x, y⟩
  rw [potentialWeight_mk, potentialDistance]
  split_ifs
  · exact I.distance_nonneg x y
  · exact mul_nonneg (by norm_num [chi, e0]) (I.distance_nonneg x y)

theorem potentialWeight_le (I : Instance V) (e : Sym2 V) :
    potentialWeight I e ≤ chi * I.weight e := by
  classical
  rcases e with ⟨x, y⟩
  rw [potentialWeight_mk, potentialDistance, Instance.weight_mk]
  split_ifs
  · nlinarith [I.distance_nonneg x y, show (1 : ℝ) ≤ chi by norm_num [chi, e0]]
  · exact le_rfl

noncomputable def nonterminalDistance (I : Instance V) (x y : V) : ℝ :=
  if x ∉ I.terminals ∧ y ∉ I.terminals then I.distance x y else 0

theorem nonterminalDistance_comm (I : Instance V) (x y : V) :
    nonterminalDistance I x y = nonterminalDistance I y x := by
  classical
  simp only [nonterminalDistance, I.distance_comm x y, and_comm]

noncomputable def nonterminalWeight (I : Instance V) : Sym2 V → ℝ :=
  Sym2.lift ⟨nonterminalDistance I, nonterminalDistance_comm I⟩

@[simp] theorem nonterminalWeight_mk (I : Instance V) (x y : V) :
    nonterminalWeight I s(x, y) = nonterminalDistance I x y := by
  rw [nonterminalWeight, Sym2.lift_mk]

theorem nonterminalWeight_nonneg (I : Instance V) (e : Sym2 V) :
    0 ≤ nonterminalWeight I e := by
  classical
  rcases e with ⟨x, y⟩
  rw [nonterminalWeight_mk, nonterminalDistance]
  split_ifs
  · exact I.distance_nonneg x y
  · exact le_rfl

namespace Tree

noncomputable def potential {I : Instance V} (S : TreeGeometry.TreeSolution I) : ℝ :=
  GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) S.graph

noncomputable def nonterminalCost {I : Instance V} (S : TreeGeometry.TreeSolution I) : ℝ :=
  GraphCost.cost (fun e => nonterminalWeight I (e.map Subtype.val)) S.graph

noncomputable def terminalGraph [Fintype V] {I : Instance V}
    (S : TreeGeometry.TreeSolution I) : SimpleGraph V :=
  S.ambient ⊓ Network.completeOn I.terminals

noncomputable def steinerEdges {I : Instance V} (S : TreeGeometry.TreeSolution I) :
    Finset (Sym2 ↥S.vertices) :=
  S.graph.edgeFinset.filter (fun e => e.map Subtype.val ∉ (Network.completeOn I.terminals).edgeSet)

theorem potential_le_cost {I : Instance V} (S : TreeGeometry.TreeSolution I) :
    potential S ≤ chi * S.cost := by
  unfold potential TreeGeometry.TreeSolution.cost GraphCost.cost
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun e _ => potentialWeight_le I _

end Tree

end SteinerUpperBound.Structural
