module

public import SteinerUpperBound.Structural.Statistics
public import SteinerUpperBound.MSTRankIntegral

@[expose] public section

namespace SteinerUpperBound.Structural

open MeasureTheory
open scoped Classical Interval

variable {V : Type*} [Fintype V]

theorem threshold_eq_below (I : Instance V) (a : ℝ) :
    threshold I a = TerminalMST.below I.weight I.terminals a := by
  ext x y
  simp only [threshold_adj, TerminalMST.below_adj, Instance.weight_mk]

theorem weight_le_horizon (I : Instance V) :
    ∀ e ∈ (Network.completeOn I.terminals).edgeSet, I.weight e ≤ horizon I := by
  intro e he
  rcases e with ⟨x, y⟩
  obtain ⟨_, hx, hy⟩ := (Network.completeOn_adj I.terminals x y).mp
    ((SimpleGraph.mem_edgeSet _).mp he)
  simpa only [Instance.weight_mk] using (distance_lt_horizon I hx hy).le

theorem benefitWith_eq_value_decrease (I : Instance V) (earlier : SimpleGraph V)
    (hE : Network.TerminalOnly I.terminals earlier) (Y : Finset V) (hY : Y ⊆ I.terminals) :
    benefitWith I earlier Y =
      TerminalMST.value (TerminalMST.zeroed I.weight earlier) I.terminals -
        TerminalMST.value
          (TerminalMST.zeroed I.weight (earlier ⊔ Network.completeOn Y)) I.terminals := by
  have hF : Network.TerminalOnly I.terminals (Network.completeOn Y) := by
    intro x y hxy
    obtain ⟨_, hx, hy⟩ := (Network.completeOn_adj Y x y).mp hxy
    exact ⟨hY hx, hY hy⟩
  have hb : ∀ e ∈ (Network.completeOn I.terminals).edgeSet,
      TerminalMST.zeroed I.weight earlier e ≤ horizon I :=
    fun e he => (TerminalMST.zeroed_le I.weight earlier I.weight_nonneg e).trans
      (weight_le_horizon I e he)
  have hv := TerminalMST.value_difference_integral
    (TerminalMST.zeroed I.weight earlier) I.terminals (Network.completeOn Y)
    (TerminalMST.zeroed_nonneg I.weight earlier I.weight_nonneg) hF
    (horizon I) (horizon_pos I).le hb
  rw [TerminalMST.zeroed_sup] at hv
  apply Eq.trans _ hv.symm
  apply intervalIntegral.integral_congr_ae
  refine Filter.Eventually.of_forall (fun a ha => ?_)
  rw [Set.uIoc_of_le (horizon_pos I).le] at ha
  rw [TerminalMST.below_zeroed I.weight I.terminals earlier hE a ha.1,
    ← threshold_eq_below I a]

theorem benefit_eq_mst_decrease (I : Instance V) (Y : Finset V) (hY : Y ⊆ I.terminals) :
    benefit I Y = I.mst -
      TerminalMST.value (TerminalMST.zeroed I.weight (Network.completeOn Y)) I.terminals := by
  simpa only [benefit, TerminalMST.zeroed_bot, bot_sup_eq, TerminalMST.value_instance] using
    benefitWith_eq_value_decrease I ⊥ (Network.bot_terminalOnly _) Y hY

end SteinerUpperBound.Structural
