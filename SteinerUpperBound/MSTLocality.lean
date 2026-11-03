module

public import SteinerUpperBound.LocalCostMinimum

@[expose] public section

namespace SteinerUpperBound

open SteinerLowerBound
open scoped Classical

variable {V : Type*} [Fintype V]

theorem Network.cost_congr (w w' : Sym2 V → ℝ) (G : SimpleGraph V)
    (h : ∀ e ∈ G.edgeSet, w e = w' e) :
    GraphCost.cost w G = GraphCost.cost w' G := by
  unfold GraphCost.cost
  apply Finset.sum_congr rfl
  intro e he
  exact h e (SimpleGraph.mem_edgeFinset.mp he)

theorem TerminalMST.value_congr (w w' : Sym2 V → ℝ) (T : Finset V)
    (h : ∀ e ∈ (Network.completeOn T).edgeSet, w e = w' e) :
    TerminalMST.value w T = TerminalMST.value w' T := by
  have hg (G : SimpleGraph V) (hG : Network.TerminalOnly T G) :
      GraphCost.cost w G = GraphCost.cost w' G := by
    apply Network.cost_congr
    intro e he
    rcases e with ⟨x, y⟩
    have hxy := (SimpleGraph.mem_edgeSet G).mp he
    obtain ⟨hx, hy⟩ := hG x y hxy
    exact h _ ((SimpleGraph.mem_edgeSet _).mpr
      ((Network.completeOn_adj T x y).mpr ⟨hxy.ne, hx, hy⟩))
  apply le_antisymm
  · obtain ⟨G, hG, hc⟩ := Network.minimum_attained w'
      (fun G => Network.Feasible T G ∧ Network.TerminalOnly T G) _
    have hv : TerminalMST.value w T ≤ GraphCost.cost w G :=
      Network.minimum_le _ _ _ G hG
    exact hv.trans_eq ((hg G hG.2).trans hc)
  · obtain ⟨G, hG, hc⟩ := Network.minimum_attained w
      (fun G => Network.Feasible T G ∧ Network.TerminalOnly T G) _
    have hv : TerminalMST.value w' T ≤ GraphCost.cost w' G :=
      Network.minimum_le _ _ _ G hG
    exact hv.trans_eq ((hg G hG.2).symm.trans hc)

namespace Structural

theorem augmented_weights_congr (w w' : Sym2 V → ℝ) (Y : Finset V)
    (h : ∀ x ∈ Y, ∀ y, w (Sym2.mk x y) = w' (Sym2.mk x y)) (v : V) :
    ∀ e ∈ (Network.completeOn (insert v Y)).edgeSet, w e = w' e := by
  intro e he
  rcases e with ⟨x, y⟩
  obtain ⟨hne, hx, hy⟩ := (Network.completeOn_adj _ x y).mp
    ((SimpleGraph.mem_edgeSet _).mp he)
  by_cases hxY : x ∈ Y
  · exact h x hxY y
  · have hxv : x = v := (Finset.mem_insert.mp hx).resolve_right hxY
    have hyY : y ∈ Y := by
      rcases Finset.mem_insert.mp hy with hyv | hyY
      · exact (hne (hxv.trans hyv.symm)).elim
      · exact hyY
    simpa only [Sym2.eq_swap] using h y hyY x

theorem pointMinimum_congr (w w' : Sym2 V → ℝ) (Y : Finset V)
    (h : ∀ x ∈ Y, ∀ y, w (Sym2.mk x y) = w' (Sym2.mk x y)) :
    pointMinimum w Y = pointMinimum w' Y := by
  have hb : TerminalMST.value w Y = TerminalMST.value w' Y := by
    apply TerminalMST.value_congr
    intro e he
    rcases e with ⟨x, y⟩
    have hx := ((Network.completeOn_adj Y x y).mp ((SimpleGraph.mem_edgeSet _).mp he)).2.1
    exact h x hx y
  have ha (v : V) : TerminalMST.value w (insert v Y) = TerminalMST.value w' (insert v Y) :=
    TerminalMST.value_congr w w' (insert v Y) (augmented_weights_congr w w' Y h v)
  have hf : (fun v => TerminalMST.value w (insert v Y)) =
      (fun v => TerminalMST.value w' (insert v Y)) := funext ha
  have hv : pointValues w Y = pointValues w' Y := by
    unfold pointValues
    rw [hb, hf]
  unfold pointMinimum
  simp only [hv]

theorem localCost_from_rows (I : Instance V) (Y : Finset V) (table : Sym2 V → ℝ)
    (h : ∀ x ∈ Y, ∀ y, table (Sym2.mk x y) = I.weight (Sym2.mk x y)) :
    pointMinimum table Y = localCost I Y := by
  rw [pointMinimum_congr table I.weight Y h, localCost_eq_pointMinimum]

end Structural

end SteinerUpperBound
