module

public import SteinerUpperBound.TreeGeometry.Surgery

@[expose] public section

namespace SteinerUpperBound.TreeGeometry.TreeSolution

open scoped Classical BigOperators

variable {V : Type*} {I : Instance V}

theorem selected_card_le (S : TreeSolution I) (hc : S.IsClean)
    (hk : 2 ≤ I.terminals.card) :
    S.vertices.card + 2 ≤ 2 * I.terminals.card := by
  classical
  let A : Finset ↥S.vertices := Finset.univ.filter (fun v => (v : V) ∈ I.terminals)
  let B : Finset ↥S.vertices := Finset.univ \ A
  have hA : A.card = I.terminals.card := by
    apply Finset.card_bij (fun (v : ↥S.vertices) _ => (v : V))
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro x hx
      exact ⟨⟨x, S.contains hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
  have hU : 2 ≤ Fintype.card ↥S.vertices := by
    rw [Fintype.card_coe]
    exact hk.trans (Finset.card_le_card S.contains)
  have : Nontrivial ↥S.vertices := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hp (v : ↥S.vertices) : 1 ≤ S.graph.degree v :=
    S.isTree.connected.preconnected.degree_pos_of_nontrivial v
  have hdegA : A.card ≤ ∑ v ∈ A, S.graph.degree v := by
    calc
      _ = ∑ _v ∈ A, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hp v)
  have hdegB : 3 * B.card ≤ ∑ v ∈ B, S.graph.degree v := by
    calc
      _ = ∑ _v ∈ B, 3 := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v hv
        have hvA := (Finset.mem_sdiff.mp hv).2
        exact hc v (fun hvT => hvA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvT⟩))
  have hsplit : (∑ v ∈ A, S.graph.degree v) + (∑ v ∈ B, S.graph.degree v) =
      ∑ v, S.graph.degree v := by
    rw [add_comm]
    exact Finset.sum_sdiff (Finset.subset_univ A)
  have hcard : B.card + A.card = S.vertices.card := by
    simpa only [B, Finset.card_univ, Fintype.card_coe] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  have hsum := S.graph.sum_degrees_eq_twice_card_edges
  have he := S.edges_card
  omega

theorem nonterminals_card_le (S : TreeSolution I) (hc : S.IsClean)
    (hk : 2 ≤ I.terminals.card) :
    (S.vertices \ I.terminals).card ≤ I.terminals.card - 2 := by
  have h := S.selected_card_le hc hk
  have hd := Finset.card_sdiff_add_card_eq_card S.contains
  omega

theorem edges_card_le (S : TreeSolution I) (hc : S.IsClean)
    (hk : 2 ≤ I.terminals.card) :
    S.graph.edgeFinset.card ≤ 2 * I.terminals.card - 3 := by
  have h := S.selected_card_le hc hk
  have he := S.edges_card
  omega

end SteinerUpperBound.TreeGeometry.TreeSolution
