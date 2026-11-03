module

public import SteinerUpperBound.SavingSoundness.Partition
public import SteinerUpperBound.StructuralSemantics

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerUpperBound.SavingSoundness

open SteinerLowerBound Covers.Geometry MeasureTheory
open scoped Classical BigOperators Interval

variable {V : Type*} [Fintype V]

noncomputable def retainedSaving (I : Instance V) (N : Finset V) (a : ℝ) : ℝ :=
  savingOn I N a (5 * a / 8)

theorem retainedSaving_nonneg (I : Instance V) (N : Finset V) (a : ℝ) :
    0 ≤ retainedSaving I N a := Structural.saving_nonneg _ _ _

noncomputable def integratedGain (I : Instance V) (earlier F : SimpleGraph V) : ℝ :=
  ∫ t in (0 : ℝ)..Structural.horizon I,
    GraphRank.gain (Structural.threshold I t ⊔ earlier) F

theorem integratedGain_nonneg (I : Instance V) (earlier F : SimpleGraph V) :
    0 ≤ integratedGain I earlier F :=
  intervalIntegral.integral_nonneg (Structural.horizon_pos I).le
    (fun _ _ => GraphRank.gain_nonneg _ _)

theorem integratedGain_lower (I : Instance V) (earlier F : SimpleGraph V)
    (b r : ℝ) (hb : 0 ≤ b) (hbM : b ≤ Structural.horizon I)
    (hgain : ∀ t ∈ Set.Icc 0 b,
      r ≤ GraphRank.gain (Structural.threshold I t ⊔ earlier) F) :
    b * r ≤ integratedGain I earlier F := by
  let g := fun t => GraphRank.gain (Structural.threshold I t ⊔ earlier) F
  have hg (u v : ℝ) : IntervalIntegrable g volume u v :=
    Structural.gain_intervalIntegrable I earlier F u v
  have hfirst : b * r ≤ ∫ t in (0 : ℝ)..b, g t := by
    calc
      _ = ∫ _t in (0 : ℝ)..b, r := by simp
      _ ≤ _ := intervalIntegral.integral_mono_on hb intervalIntegrable_const (hg _ _) hgain
  have htail : 0 ≤ ∫ t in b..Structural.horizon I, g t :=
    intervalIntegral.integral_nonneg hbM (fun _ _ => GraphRank.gain_nonneg _ _)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hg 0 b) (hg b (Structural.horizon I))
  change b * r ≤ ∫ t in (0 : ℝ)..Structural.horizon I, g t
  linarith

theorem star_arithmetic (a ρ f z Φ : ℝ) (ha : 0 ≤ a) (hρ : 0 ≤ ρ)
    (hsmall : 64 * ρ ≤ a) (hz : 0 ≤ z) (hdegree : 3 * z ≤ f)
    (hsaving : Φ / 2 ≤ f - 2 * z) :
    a * Φ / 32 ≤ (a - 2 * ρ) * (f - z) - (5 * a / 8) * f := by
  let r := f - 2 * z
  have hzr : z ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hz.trans hzr
  have hc : 0 ≤ a / 4 + 2 * ρ := by positivity
  have hzc := mul_le_mul_of_nonneg_left hzr hc
  have hδ := mul_nonneg (sub_nonneg.mpr hsmall) hr
  have hp := mul_le_mul_of_nonneg_left hsaving ha
  dsimp only [r] at hzc hδ
  nlinarith

theorem exists_scale_networks (I : Instance V) (N : Finset V)
    (a ρ : ℝ) (ha : 0 < a) (hρ : 0 ≤ ρ) (hsmall : 64 * ρ ≤ a)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals) :
    ∃ F K : SimpleGraph V,
      Network.TerminalOnly I.terminals F ∧
      (∀ x y, F.Adj x y → K.Reachable x y) ∧
      (∀ x y, F.Adj x y → I.distance x y ≤ 5 * a / 4) ∧
      ∀ earlier : SimpleGraph V, earlier ≤ Structural.threshold I (a - 2 * ρ) →
        a * retainedSaving I N a / 32 + GraphCost.cost I.weight K ≤
          integratedGain I earlier F := by
  classical
  let : DecidableEq (Finset V) := Classical.decEq _
  by_cases hΦ : 0 < retainedSaving I N a
  · let E := eligibleOn I N a (5 * a / 8)
    let rows := rowOn I N a (5 * a / 8)
    let A := componentsOn I N a
    have hlarge : ∀ r ∈ E, 3 ≤ (A ∩ rows r).card := by
      intro r hr
      have h3 := (Finset.mem_filter.mp hr).2
      have he : A ∩ rows r = rows r := Finset.inter_eq_right.mpr
        (rowOn_subset_componentsOn I N a (5 * a / 8) r)
      rw [he]
      exact h3
    obtain ⟨S, ports, _, hsound, hdegree, _, hprofit, hcount, hrank⟩ :=
      SetSystem.saving_forest_on_universe E rows A hlarge
    have hpoints : ∀ (r : ↥S) (c : ↥(ports r)),
        ∃ x ∈ c.val.val, I.distance r.val x ≤ 5 * a / 8 := by
      intro r c
      exact ((mem_rowOn I N a (5 * a / 8) r.val c.val.val).mp
        (hsound r c.val c.property)).2
    choose pick hcell hnear using hpoints
    have hterminal (r : ↥S) (c : ↥(ports r)) : pick r c ∈ I.terminals :=
      hNT (componentsOn_subset I N a c.val.property (hcell r c))
    have hS : S.Nonempty := by
      by_contra hn
      have hs : (∑ r : ↥S, ((ports r).card : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro r _
        exact (hn ⟨r.val, r.property⟩).elim
      change retainedSaving I N a / 2 ≤ _ at hprofit
      rw [hs] at hprofit
      have hz : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
      linarith
    have haM : a < Structural.horizon I := by
      obtain ⟨r, hrS⟩ := hS
      let r' : ↥S := ⟨r, hrS⟩
      obtain ⟨C, hC, D, hD, hCD⟩ := Finset.one_lt_card.mp
        (show 1 < (ports r').card by have := hdegree r'; omega)
      let c : ↥(ports r') := ⟨C, hC⟩
      let d : ↥(ports r') := ⟨D, hD⟩
      have hsep := cells_separated I N a C D hCD (hcell r' c) (hcell r' d)
      exact hsep.trans_lt (Structural.distance_lt_horizon I (hterminal r' c) (hterminal r' d))
    let F := chosenLinks ports pick
    let K := chosenStars ports (fun r : ↥S => r.val) pick
    have hcost : GraphCost.cost I.weight K ≤ (5 * a / 8) *
        (∑ r : ↥S, ((ports r).card : ℝ)) :=
      chosenStars_cost I ports (fun r : ↥S => r.val) pick _ hnear
    have hdiam : ∀ x y, F.Adj x y → I.distance x y ≤ 5 * a / 4 := by
      intro x y hxy
      have hh := chosenLinks_diameter I ports (fun r : ↥S => r.val) pick _ hnear x y hxy
      linarith
    refine ⟨F, K, chosenLinks_terminalOnly _ ports pick hterminal,
      chosenLinks_connect ports _ pick, hdiam, ?_⟩
    intro earlier hEarlier
    have hpartition := threshold_le_partition I N ρ hc hρ a
    have hbase := partition_gain I N ρ hc hNT a ports pick hcell
    have hrank' : (GraphRank.rank (SetSystem.portGraph ports) : ℝ) + S.card =
        ∑ r : ↥S, ((ports r).card : ℝ) := by exact_mod_cast hrank
    have hgain : ∀ t ∈ Set.Icc 0 (a - 2 * ρ),
        (∑ r : ↥S, ((ports r).card : ℝ)) - S.card ≤
          GraphRank.gain (Structural.threshold I t ⊔ earlier) F := by
      intro t ht
      have hle : Structural.threshold I t ⊔ earlier ≤ fiberGraph (label I N ρ hc a) :=
        sup_le ((Structural.threshold_mono I ht.2).trans hpartition) (hEarlier.trans hpartition)
      have hh := GraphRank.gain_antitone hle F
      change GraphRank.gain _ (chosenLinks ports pick) ≤ _ at hh
      rw [hbase] at hh
      linarith
    have hcut : 0 ≤ a - 2 * ρ := by linarith
    have hcutM : a - 2 * ρ ≤ Structural.horizon I := by linarith
    have hint := integratedGain_lower I earlier F (a - 2 * ρ)
      ((∑ r : ↥S, ((ports r).card : ℝ)) - S.card) hcut hcutM hgain
    have hz : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hcount' : 3 * (S.card : ℝ) ≤ ∑ r : ↥S, ((ports r).card : ℝ) := by
      exact_mod_cast hcount
    change retainedSaving I N a / 2 ≤ _ at hprofit
    have harith := star_arithmetic a ρ (∑ r : ↥S, ((ports r).card : ℝ)) S.card
      (retainedSaving I N a) ha.le hρ hsmall hz hcount' hprofit
    linarith
  · have hzero : retainedSaving I N a = 0 := by
      linarith [retainedSaving_nonneg I N a]
    refine ⟨⊥, ⊥, Network.bot_terminalOnly _, ?_, ?_, ?_⟩
    · intro x y hxy; exact hxy.elim
    · intro x y hxy; exact hxy.elim
    · intro earlier _
      simpa only [hzero, mul_zero, zero_div, Network.cost_bot, zero_add] using
        integratedGain_nonneg I earlier ⊥

end SteinerUpperBound.SavingSoundness
