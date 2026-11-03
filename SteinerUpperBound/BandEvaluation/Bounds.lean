module

public import SteinerUpperBound.BandStatistic

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

open MeasureTheory
open scoped Classical Interval

variable {V : Type*} [Fintype V]

theorem benefit_le_three (I : Instance V) (C Y : Finset V) (hY : Y ⊆ C) (h4 : Y.card ≤ 4)
    (a rho tau : ℝ) (ha : 0 ≤ a) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (hband : tau * a ≤ a - 2 * rho) :
    Band.benefit I C Y (tau * a) (a - 2 * rho) ≤ 3 * a := by
  have hrank : GraphRank.rank (Network.completeOn Y) ≤ 3 := by
    rw [GraphRank.rank_completeOn]
    omega
  have hrank' : (GraphRank.rank (Network.completeOn Y) : ℝ) ≤ 3 := by exact_mod_cast hrank
  have hp (t : ℝ) :
      GraphRank.gain (TerminalMST.below I.weight C t) (Network.completeOn Y) ≤ 3 :=
    (GraphRank.gain_le_rank _ _).trans hrank'
  have hlo : 0 ≤ tau * a := mul_nonneg htau ha
  have hi := intervalIntegral.integral_mono_on hband
    (Band.benefit_integrable I C Y hY (tau * a) (a - 2 * rho) hlo hband)
    intervalIntegrable_const (fun t _ => hp t)
  have hint : Band.benefit I C Y (tau * a) (a - 2 * rho) ≤
      ((a - 2 * rho) - tau * a) * 3 := by
    simpa only [Band.benefit, intervalIntegral.integral_const, smul_eq_mul] using hi
  nlinarith

theorem score_bounds (I : Instance V) (C : Finset V) (a rho tau : ℝ)
    (ha : 0 ≤ a) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (hband : tau * a ≤ a - 2 * rho) :
    0 ≤ Band.score I C a rho tau ∧ Band.score I C a rho tau ≤ 3 * a := by
  refine ⟨Band.score_nonneg I C a rho tau, ?_⟩
  by_cases hp : 0 < Band.score I C a rho tau
  · obtain ⟨Y, hY, _, h4, he⟩ := Band.score_attained_positive I C a rho tau hp
    have hb := benefit_le_three I C Y hY h4 a rho tau ha hrho htau hband
    rw [he]
    linarith [Structural.localCost_nonneg I Y]
  · have hn := le_of_not_gt hp
    linarith

end SteinerUpperBound.BandEvaluation
