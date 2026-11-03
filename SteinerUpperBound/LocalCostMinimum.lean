module

public import SteinerUpperBound.Structural.Statistics
public import SteinerUpperBound.TerminalMST

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical

variable {V : Type*} [Fintype V]

theorem oneCenter_dichotomy (Y : Finset V) (G : SimpleGraph V)
    (hG : OneCenterNetwork Y G) :
    (Network.Feasible Y G ∧ Network.TerminalOnly Y G) ∨
      ∃ v, Network.Feasible (insert v Y) G ∧ Network.TerminalOnly (insert v Y) G := by
  by_cases hT : Network.TerminalOnly Y G
  · exact Or.inl ⟨hG.1, hT⟩
  · right
    have hout : ∃ v u, G.Adj v u ∧ v ∉ Y := by
      by_contra hn
      apply hT
      intro x y hxy
      constructor
      · by_contra hx
        exact hn ⟨x, y, hxy, hx⟩
      · by_contra hy
        exact hn ⟨y, x, hxy.symm, hy⟩
    obtain ⟨v, u, hvu, hv⟩ := hout
    obtain ⟨U, hU, hsupport⟩ := hG.2
    have hvU : v ∈ U := (Finset.mem_union.mp (hsupport v u hvu).1).resolve_left hv
    have hUv (z : V) (hz : z ∈ U) : z = v :=
      Finset.card_le_one.mp hU z hz v hvU
    have hu : u ∈ Y := by
      rcases Finset.mem_union.mp (hsupport v u hvu).2 with hu | hu
      · exact hu
      · exact (hvu.ne (hUv u hu).symm).elim
    have hsub {z : V} (hz : z ∈ Y ∪ U) : z ∈ insert v Y := by
      rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.mem_insert_of_mem hz
      · exact Finset.mem_insert.mpr (Or.inl (hUv z hz))
    have hreach (z : V) (hz : z ∈ insert v Y) : G.Reachable z u := by
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hvu.reachable
      · exact hG.1 z hz u hu
    refine ⟨v, ?_, ?_⟩
    · intro x hx y hy
      exact (hreach x hx).trans (hreach y hy).symm
    · intro x y hxy
      exact ⟨hsub (hsupport x y hxy).1, hsub (hsupport x y hxy).2⟩

theorem graph_oneCenter (w : Sym2 V → ℝ) (Y : Finset V) :
    OneCenterNetwork Y (TerminalMST.graph w Y) := by
  refine ⟨TerminalMST.graph_feasible w Y, ∅, by simp, ?_⟩
  simpa only [Finset.union_empty] using TerminalMST.graph_terminalOnly w Y

theorem augmented_graph_oneCenter (w : Sym2 V → ℝ) (Y : Finset V) (v : V) :
    OneCenterNetwork Y (TerminalMST.graph w (insert v Y)) := by
  refine ⟨?_, {v}, by simp, ?_⟩
  · intro x hx y hy
    exact TerminalMST.graph_feasible w (insert v Y) x (Finset.mem_insert_of_mem hx)
      y (Finset.mem_insert_of_mem hy)
  · simpa only [Finset.union_singleton] using TerminalMST.graph_terminalOnly w (insert v Y)

theorem localCost_le_mst (I : Instance V) (Y : Finset V) :
    localCost I Y ≤ TerminalMST.value I.weight Y := by
  rw [TerminalMST.value_eq_cost _ _ I.weight_nonneg]
  exact localCost_le I Y _ (graph_oneCenter _ _)

theorem localCost_le_augmented_mst (I : Instance V) (Y : Finset V) (v : V) :
    localCost I Y ≤ TerminalMST.value I.weight (insert v Y) := by
  rw [TerminalMST.value_eq_cost _ _ I.weight_nonneg]
  exact localCost_le I Y _ (augmented_graph_oneCenter _ _ _)

noncomputable def pointValues (w : Sym2 V → ℝ) (Y : Finset V) : Finset ℝ :=
  insert (TerminalMST.value w Y)
    (Finset.univ.image (fun v => TerminalMST.value w (insert v Y)))

noncomputable def pointMinimum (w : Sym2 V → ℝ) (Y : Finset V) : ℝ :=
  (pointValues w Y).min' (by simp [pointValues])

theorem localCost_eq_pointMinimum (I : Instance V) (Y : Finset V) :
    localCost I Y = pointMinimum I.weight Y := by
  apply le_antisymm
  · have hm : pointMinimum I.weight Y ∈ pointValues I.weight Y := Finset.min'_mem _ _
    rcases Finset.mem_insert.mp hm with hm | hm
    · rw [hm]
      exact localCost_le_mst I Y
    · obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hm
      rw [← hv]
      exact localCost_le_augmented_mst I Y v
  · obtain ⟨G, hG, hc⟩ := localCost_attained I Y
    rcases oneCenter_dichotomy Y G hG with h | ⟨v, h⟩
    · have hmin : pointMinimum I.weight Y ≤ TerminalMST.value I.weight Y :=
        Finset.min'_le _ _ (Finset.mem_insert_self _ _)
      have hv : TerminalMST.value I.weight Y ≤ GraphCost.cost I.weight G :=
        Network.minimum_le _ _ _ G h
      exact (hmin.trans hv).trans_eq hc
    · have hmin : pointMinimum I.weight Y ≤ TerminalMST.value I.weight (insert v Y) := by
        apply Finset.min'_le
        exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
      have hv : TerminalMST.value I.weight (insert v Y) ≤ GraphCost.cost I.weight G :=
        Network.minimum_le _ _ _ G h
      exact (hmin.trans hv).trans_eq hc

end SteinerUpperBound.Structural
