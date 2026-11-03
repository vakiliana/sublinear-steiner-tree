module

public import SteinerUpperBound.Covers.Geometry.BandSoundnessRank

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry.BandSoundness

open SteinerLowerBound MeasureTheory
open scoped Classical BigOperators Interval
open BandCompleteness

variable {V : Type*} [Fintype V]

/-- Shifting a rank-at-most-three contraction curve by `2ρ` loses at most `6ρ`.
The comparison uses actual bottleneck reachability in the retained component. -/
theorem local_band_le_global (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hρ : 0 ≤ ρ) (a : ℝ)
    {C Y : Finset V} (hC : C ∈ componentsOn I N a) (hY : Y ⊆ C) (h4 : Y.card ≤ 4)
    (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) :
    Band.benefit I C Y lo hi ≤
      (∫ t in lo..hi, globalGain I Y t) + 6 * ρ := by
  let f : ℝ → ℝ := fun t =>
    GraphRank.gain (TerminalMST.below I.weight C t) (Network.completeOn Y)
  have hI₁ : IntervalIntegrable f volume lo hi :=
    Band.benefit_integrable I C Y hY lo hi hlo hlohi
  have hI₂ : IntervalIntegrable f volume hi (hi + 2 * ρ) :=
    Band.benefit_integrable I C Y hY hi _ (hlo.trans hlohi) (by linarith)
  have hI₃ : IntervalIntegrable f volume lo (lo + 2 * ρ) :=
    Band.benefit_integrable I C Y hY lo _ hlo (by linarith)
  have hI₄ : IntervalIntegrable f volume (lo + 2 * ρ) (hi + 2 * ρ) :=
    Band.benefit_integrable I C Y hY _ _ (by linarith) (by linarith)
  have hshift : IntervalIntegrable (fun t => f (t + 2 * ρ)) volume lo hi := by
    simpa only [add_sub_cancel_right] using hI₄.comp_add_right (2 * ρ)
  have hshort : (∫ t in lo..(lo + 2 * ρ), f t) ≤ 6 * ρ := by
    calc
      _ ≤ ∫ _t in lo..(lo + 2 * ρ), (3 : ℝ) :=
        intervalIntegral.integral_mono_on (by linarith) hI₃ intervalIntegrable_const
          (fun _ _ => gain_le_three _ Y h4)
      _ = _ := by simp [intervalIntegral.integral_const, smul_eq_mul]; ring
  have htail : 0 ≤ ∫ t in hi..(hi + 2 * ρ), f t :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => GraphRank.gain_nonneg _ _)
  have h₁ := intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂
  have h₂ := intervalIntegral.integral_add_adjacent_intervals hI₃ hI₄
  have hcompare : (∫ t in lo..hi, f (t + 2 * ρ)) ≤
      ∫ t in lo..hi, globalGain I Y t :=
    intervalIntegral.integral_mono_on hlohi hshift (globalGain_integrable I Y lo hi)
      (fun t _ => global_gain_ge_shifted I N ρ hc hρ a hC hY t)
  rw [intervalIntegral.integral_comp_add_right] at hcompare
  change (∫ t in lo..hi, f t) ≤ _
  linarith

theorem completeOn_empty : Network.completeOn (∅ : Finset V) = ⊥ := by
  ext x y
  simp [Network.completeOn_adj]

/-- Every score has a genuine witness network. Positive scores use the actual
attaining small set and an actual attained one-center optimizer; zero scores
use empty links and the empty network. -/
theorem score_network_exists (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hρ : 0 ≤ ρ) (a τ : ℝ)
    (hlo : 0 ≤ τ * a) (hband : τ * a ≤ a - 2 * ρ)
    (C : Finset V) (hC : C ∈ componentsOn I N a) :
    ∃ Y : Finset V, ∃ K : SimpleGraph V,
      Y ⊆ C ∧ Y.card ≤ 4 ∧ Structural.OneCenterNetwork Y K ∧
      Band.score I C a ρ τ + GraphCost.cost I.weight K ≤
        ∫ t in (τ * a)..(a - 2 * ρ), globalGain I Y t := by
  classical
  by_cases hs : 0 < Band.score I C a ρ τ
  · obtain ⟨Y, hYC, _, h4, he⟩ := Band.score_attained_positive I C a ρ τ hs
    obtain ⟨K, hK, hcost⟩ := Structural.localCost_attained I Y
    refine ⟨Y, K, hYC, h4, hK, ?_⟩
    have hb := local_band_le_global I N ρ hc hρ a hC hYC h4 (τ * a) (a - 2 * ρ) hlo hband
    rw [he, hcost]
    linarith
  · have hs0 : Band.score I C a ρ τ = 0 :=
      le_antisymm (le_of_not_gt hs) (Band.score_nonneg I C a ρ τ)
    refine ⟨∅, ⊥, Finset.empty_subset _, by simp, ?_, ?_⟩
    · refine ⟨?_, ∅, by simp, ?_⟩
      · intro x hx
        simp at hx
      · exact Network.bot_terminalOnly _
    · rw [hs0, Network.cost_bot, add_zero]
      apply intervalIntegral.integral_nonneg hband
      intro t _
      exact GraphRank.gain_nonneg _ _

end SteinerUpperBound.Covers.Geometry.BandSoundness
