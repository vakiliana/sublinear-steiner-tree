module

public import SteinerUpperBound.Covers.Geometry.BandCost

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry.BandCompleteness

open SteinerLowerBound MeasureTheory
open scoped Classical BigOperators Interval

variable {V : Type*} [Fintype V]

theorem structural_benefit_eq_globalIntegral (I : Instance V) (Y : Finset V) :
    Structural.benefit I Y = ∫ t in (0 : ℝ)..Structural.horizon I, globalGain I Y t := by
  unfold Structural.benefit Structural.benefitWith
  simp only [sup_bot_eq]
  rfl

theorem integral_zero_of_vanish (f : ℝ → ℝ) (lo hi : ℝ) (hlohi : lo ≤ hi)
    (hf : ∀ t, lo < t → t ≤ hi → f t = 0) : (∫ t in lo..hi, f t) = 0 := by
  calc
    _ = ∫ _t in lo..hi, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [Set.uIoc_of_le hlohi] at ht
      exact hf t ht.1 ht.2
    _ = 0 := by simp

/-- No extra relation between the scale and the structural horizon is needed:
above `a` the witness is connected, and above the actual horizon every terminal
is connected. Both tails are proved zero. -/
theorem benefit_eq_integral_to_component (I : Instance V) (a : ℝ)
    {C Y : Finset V} (hC : C ∈ componentsOn I I.terminals a) (hY : Y ⊆ C) :
    Structural.benefit I Y = ∫ t in (0 : ℝ)..a, globalGain I Y t := by
  rw [structural_benefit_eq_globalIntegral]
  by_cases haH : a ≤ Structural.horizon I
  · have hz : (∫ t in a..Structural.horizon I, globalGain I Y t) = 0 :=
      integral_zero_of_vanish _ _ _ haH
        (fun _ ht _ => globalGain_zero_on_component I a hC hY ht.le)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (globalGain_integrable I Y 0 a) (globalGain_integrable I Y a (Structural.horizon I))
    rw [hz, add_zero] at hadd
    exact hadd.symm
  · have hHa : Structural.horizon I ≤ a := le_of_not_ge haH
    have hYT := hY.trans (componentsOn_subset I I.terminals a hC)
    have hz : (∫ t in Structural.horizon I..a, globalGain I Y t) = 0 :=
      integral_zero_of_vanish _ _ _ hHa
        (fun _ ht _ => globalGain_zero_above_horizon I hYT ht.le)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (globalGain_integrable I Y 0 (Structural.horizon I)) (globalGain_integrable I Y (Structural.horizon I) a)
    rw [hz, add_zero] at hadd
    exact hadd

theorem globalIntegral_nonneg (I : Instance V) (Y : Finset V) (lo hi : ℝ)
    (hlohi : lo ≤ hi) : 0 ≤ ∫ t in lo..hi, globalGain I Y t :=
  intervalIntegral.integral_nonneg hlohi (fun _ _ => GraphRank.gain_nonneg _ _)

theorem globalIntegral_le_three (I : Instance V) (Y : Finset V) (h4 : Y.card ≤ 4)
    (lo hi : ℝ) (hlohi : lo ≤ hi) :
    (∫ t in lo..hi, globalGain I Y t) ≤ 3 * (hi - lo) := by
  calc
    _ ≤ ∫ _t in lo..hi, (3 : ℝ) :=
      intervalIntegral.integral_mono_on hlohi (globalGain_integrable I Y lo hi)
        intervalIntegrable_const (fun _ _ => gain_le_three _ Y h4)
    _ = _ := by simp [intervalIntegral.integral_const, smul_eq_mul]; ring

theorem projected_globalIntegral_lower (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals) (hρ : 0 ≤ ρ)
    (Y : Finset V) (hY : Y ⊆ I.terminals) (h4 : Y.card ≤ 4)
    (a : ℝ) (hρa : ρ ≤ a) :
    (∫ t in (0 : ℝ)..a, globalGain I Y t) - 3 * ρ ≤
      ∫ t in (0 : ℝ)..a, globalGain I (projected I N ρ hc Y) t := by
  have he : (∫ t in ρ..a, globalGain I Y t) =
      ∫ t in ρ..a, globalGain I (projected I N ρ hc Y) t := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le hρa] at ht
    exact projected_gain_eq I N ρ hc hNT hρ hY t ht.1
  have haddY := intervalIntegral.integral_add_adjacent_intervals
    (globalGain_integrable I Y 0 ρ) (globalGain_integrable I Y ρ a)
  have haddP := intervalIntegral.integral_add_adjacent_intervals
    (globalGain_integrable I (projected I N ρ hc Y) 0 ρ)
    (globalGain_integrable I (projected I N ρ hc Y) ρ a)
  have hsmall := globalIntegral_le_three I Y h4 0 ρ hρ
  have hp := globalIntegral_nonneg I (projected I N ρ hc Y) 0 ρ hρ
  linarith

theorem globalIntegral_band_truncation (I : Instance V) (Y : Finset V) (h4 : Y.card ≤ 4)
    (a lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhia : hi ≤ a) :
    (∫ t in (0 : ℝ)..a, globalGain I Y t) ≤
      (∫ t in lo..hi, globalGain I Y t) + 3 * lo + 3 * (a - hi) := by
  have hadd₁ := intervalIntegral.integral_add_adjacent_intervals
    (globalGain_integrable I Y 0 lo) (globalGain_integrable I Y lo hi)
  have hadd₂ := intervalIntegral.integral_add_adjacent_intervals
    (globalGain_integrable I Y 0 hi) (globalGain_integrable I Y hi a)
  have hleft := globalIntegral_le_three I Y h4 0 lo hlo
  have hright := globalIntegral_le_three I Y h4 hi a hhia
  linarith

/-- Retaining fewer threshold edges can only increase the contraction gain. -/
theorem retained_band_ge_global (I : Instance V) (D P : Finset V)
    (hD : D ⊆ I.terminals) (hP : P ⊆ D) (lo hi : ℝ)
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) :
    (∫ t in lo..hi, globalGain I P t) ≤ Band.benefit I D P lo hi := by
  unfold Band.benefit
  apply intervalIntegral.integral_mono_on hlohi
    (globalGain_integrable I P lo hi) (Band.benefit_integrable I D P hP lo hi hlo hlohi)
  intro t _
  apply GraphRank.gain_antitone
  rw [below_eq_thresholdOn, ← thresholdOn_terminals_eq]
  exact thresholdOn_mono I hD le_rfl

/-- Full witness transfer with conservative, completely proved losses.
`50ρ` is the arbitrary attained one-center network cost loss; the remaining
`15ρ` covers projection, the upper band cut, and the score's own penalty. -/
theorem band_candidate_lower (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals) (hρ : 0 ≤ ρ)
    (a τ : ℝ) (hρa : ρ ≤ a) (hlo : 0 ≤ τ * a) (hband : τ * a ≤ a - 2 * ρ)
    {C Y D : Finset V} (hC : C ∈ componentsOn I I.terminals a) (hY : Y ⊆ C)
    (h4 : Y.card ≤ 4) (hD : D ⊆ I.terminals) (hP : projected I N ρ hc Y ⊆ D) :
    Structural.benefit I Y - Structural.localCost I Y - (65 * ρ + 3 * (τ * a)) ≤
      Band.benefit I D (projected I N ρ hc Y) (τ * a) (a - 2 * ρ) -
        Structural.localCost I (projected I N ρ hc Y) - 6 * ρ := by
  have hYT := hY.trans (componentsOn_subset I I.terminals a hC)
  have hfull := benefit_eq_integral_to_component I a hC hY
  have hproj := projected_globalIntegral_lower I N ρ hc hNT hρ Y hYT h4 a hρa
  rw [← hfull] at hproj
  have h4P := (projected_card_le I N ρ hc Y).trans h4
  have htrunc := globalIntegral_band_truncation I (projected I N ρ hc Y) h4P
    a (τ * a) (a - 2 * ρ) hlo hband (by linarith)
  have hret := retained_band_ge_global I D (projected I N ρ hc Y) hD hP
    (τ * a) (a - 2 * ρ) hlo hband
  have hcost := localCost_projected_le I N ρ hc hρ Y hYT h4
  linarith

end SteinerUpperBound.Covers.Geometry.BandCompleteness
