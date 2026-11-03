module

public import SteinerUpperBound.Structural.Potential

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*}

noncomputable def steinerCountWeight (I : Instance V) (e : Sym2 V) : ℝ :=
  if e ∈ (Network.completeOn I.terminals).edgeSet then 0 else 1

theorem steinerCountWeight_nonneg (I : Instance V) (e : Sym2 V) :
    0 ≤ steinerCountWeight I e := by
  classical
  unfold steinerCountWeight
  split_ifs <;> norm_num

theorem steinerCountWeight_le_one (I : Instance V) (e : Sym2 V) :
    steinerCountWeight I e ≤ 1 := by
  classical
  unfold steinerCountWeight
  split_ifs <;> norm_num

theorem steinerCountWeight_incident (I : Instance V) {v : V}
    (hv : v ∉ I.terminals) (x : V) : steinerCountWeight I s(v, x) = 1 := by
  classical
  simp [steinerCountWeight, SimpleGraph.mem_edgeSet, Network.completeOn_adj, hv]

theorem potentialWeight_triangle_at_nonterminal (I : Instance V) {v : V}
    (hv : v ∉ I.terminals) (x y : V) :
    potentialWeight I s(x, y) ≤ potentialWeight I s(v, x) + potentialWeight I s(v, y) := by
  classical
  have hchi : 0 ≤ chi := by norm_num [chi, e0]
  have hchi1 : 1 ≤ chi := by norm_num [chi, e0]
  have hd := I.distance_triangle x v y
  rw [I.distance_comm x v] at hd
  have hmul := mul_le_mul_of_nonneg_left hd hchi
  simp only [potentialWeight_mk, potentialDistance, hv, false_and, ↓reduceIte]
  split_ifs
  · have hh : I.distance x y ≤ chi * I.distance x y := by
      nlinarith [I.distance_nonneg x y]
    nlinarith
  · nlinarith

theorem nonterminalWeight_triangle_at_nonterminal (I : Instance V) {v : V}
    (hv : v ∉ I.terminals) (x y : V) :
    nonterminalWeight I s(x, y) ≤ nonterminalWeight I s(v, x) + nonterminalWeight I s(v, y) := by
  classical
  by_cases hx : x ∉ I.terminals
  · by_cases hy : y ∉ I.terminals
    · simpa [nonterminalWeight_mk, nonterminalDistance, hv, hx, hy,
        I.distance_comm x v] using I.distance_triangle x v y
    · have h1 := nonterminalWeight_nonneg I s(v, x)
      have h2 := nonterminalWeight_nonneg I s(v, y)
      have he : nonterminalWeight I s(x, y) = 0 := by
        simp [nonterminalWeight_mk, nonterminalDistance, hy]
      rw [he]
      exact add_nonneg h1 h2
  · have h1 := nonterminalWeight_nonneg I s(v, x)
    have h2 := nonterminalWeight_nonneg I s(v, y)
    have he : nonterminalWeight I s(x, y) = 0 := by
      simp [nonterminalWeight_mk, nonterminalDistance, hx]
    rw [he]
    exact add_nonneg h1 h2

theorem steinerCountWeight_triangle_at_nonterminal (I : Instance V) {v : V}
    (hv : v ∉ I.terminals) (x y : V) :
    steinerCountWeight I s(x, y) ≤ steinerCountWeight I s(v, x) + steinerCountWeight I s(v, y) := by
  rw [steinerCountWeight_incident I hv, steinerCountWeight_incident I hv]
  exact (steinerCountWeight_le_one I _).trans (by norm_num)

theorem steinerCountWeight_cost {I : Instance V} (S : TreeGeometry.TreeSolution I) :
    GraphCost.cost (fun e => steinerCountWeight I (e.map Subtype.val)) S.graph =
      (Tree.steinerEdges S).card := by
  classical
  unfold Tree.steinerEdges
  rw [Finset.card_filter, Nat.cast_sum]
  unfold GraphCost.cost
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : e.map Subtype.val ∈ (Network.completeOn I.terminals).edgeSet
  · simp [steinerCountWeight, h]
  · simp [steinerCountWeight, h]

end SteinerUpperBound.Structural
