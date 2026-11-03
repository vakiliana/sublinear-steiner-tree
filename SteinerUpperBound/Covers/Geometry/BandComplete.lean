module

public import SteinerUpperBound.Covers.Geometry.BandBenefit

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry.BandCompleteness

open SteinerLowerBound
open scoped Classical BigOperators Interval

variable {V : Type*} [Fintype V]

noncomputable abbrev bandDelta : ℝ := 1 / 10000000000
noncomputable abbrev bandTau : ℝ := Structural.sigma0 / 100

theorem sigma0_pos : 0 < Structural.sigma0 := by norm_num [Structural.sigma0]

theorem band_parameters (a ρ : ℝ) (ha : 0 < a) (hρ : 0 ≤ ρ) (hsmall : ρ ≤ bandDelta * a) :
    ρ < a ∧ 0 ≤ bandTau * a ∧ bandTau * a ≤ a - 2 * ρ ∧
      65 * ρ + 3 * (bandTau * a) ≤ Structural.sigma0 * a / 2 := by
  dsimp [bandDelta, bandTau, Structural.sigma0] at *
  constructor
  · nlinarith
  constructor
  · positivity
  constructor <;> nlinarith

theorem localAdvantage_attained_positive (I : Instance V) (C : Finset V)
    (h : 0 < Structural.localAdvantage I C) :
    ∃ Y, Y ⊆ C ∧ 2 ≤ Y.card ∧ Y.card ≤ 4 ∧
      Structural.localAdvantage I C = Structural.benefit I Y - Structural.localCost I Y := by
  classical
  have hm : Structural.localAdvantage I C ∈
      insert 0 ((C.powerset.filter (fun Y => 2 ≤ Y.card ∧ Y.card ≤ 4)).image
        (fun Y => max (Structural.benefit I Y - Structural.localCost I Y) 0)) :=
    Finset.max'_mem _ _
  rcases Finset.mem_insert.mp hm with hm | hm
  · rw [hm] at h
    exact (lt_irrefl _ h).elim
  · obtain ⟨Y, hY, he⟩ := Finset.mem_image.mp hm
    obtain ⟨hYC, h2, h4⟩ : Y ⊆ C ∧ 2 ≤ Y.card ∧ Y.card ≤ 4 := by
      simpa only [Finset.mem_filter, Finset.mem_powerset] using hY
    have hpos : 0 < Structural.benefit I Y - Structural.localCost I Y := by
      by_contra hn
      have hz := max_eq_right (le_of_not_gt hn)
      rw [hz] at he
      linarith
    refine ⟨Y, hYC, h2, h4, ?_⟩
    rw [max_eq_left hpos.le] at he
    exact he.symm

theorem projected_subset_retainedPart (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) {C Y : Finset V}
    (hC : C ∈ componentsOn I I.terminals a) (hY : Y ⊆ C) :
    projected I N ρ hc Y ⊆ N ∩ C := by
  classical
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
  have hyC := hY hy
  have hyT := componentsOn_subset I I.terminals a hC hyC
  have hpN := project_mem I I.terminals N ρ hc hyT
  have hatt := terminal_attachment I I.terminals N ρ hc hNT hρ a hρa hyT
  have hpC := (mem_componentOn I I.terminals a y _).mpr ⟨hNT hpN, hatt⟩
  rw [componentOn_eq_of_mem I I.terminals a hC hyC] at hpC
  exact Finset.mem_inter.mpr ⟨hpN, hpC⟩

theorem persistent_retained_component (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) {C : Finset V}
    (hC : C ∈ componentsOn I I.terminals a)
    (hphase : C ∉ phaseBad I I.terminals (a - 2 * ρ) a) :
    N ∩ C ∈ componentsOn I N a ∧ componentMap I I.terminals a (N ∩ C) = C := by
  obtain ⟨x, hx⟩ := componentsOn_nonempty I I.terminals a hC
  have hxT := componentsOn_subset I I.terminals a hC hx
  have he := retained_component_eq_inter_of_not_phaseBad
    I I.terminals N ρ hc hNT hρ a hρa hC hphase hx
  have hD : N ∩ C ∈ componentsOn I N a := by
    rw [← he]
    exact componentOn_mem_componentsOn I N a (project_mem I I.terminals N ρ hc hxT)
  have hmap := projected_componentMap I I.terminals N ρ hc hNT hρ a hρa hxT
  rw [he, componentOn_eq_of_mem I I.terminals a hC hx] at hmap
  exact ⟨hD, hmap⟩

theorem persistent_retained_injective (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) {C D : Finset V}
    (hC : C ∈ componentsOn I I.terminals a) (hD : D ∈ componentsOn I I.terminals a)
    (hphaseC : C ∉ phaseBad I I.terminals (a - 2 * ρ) a)
    (hphaseD : D ∉ phaseBad I I.terminals (a - 2 * ρ) a)
    (he : N ∩ C = N ∩ D) : C = D := by
  have hmapC := (persistent_retained_component I N ρ hc hNT hρ a hρa hC hphaseC).2
  have hmapD := (persistent_retained_component I N ρ hc hNT hρ a hρa hD hphaseD).2
  have h := congrArg (componentMap I I.terminals a) he
  rwa [hmapC, hmapD] at h

/-- Every high-advantage exact component has an actual projected small-set
witness with half the original threshold advantage. Persistence is needed only
to identify `N ∩ C` as one retained component, not for this analytic bound. -/
theorem retained_band_witness (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals) (hρ : 0 ≤ ρ)
    (a : ℝ) (ha : 0 < a) (hsmall : ρ ≤ bandDelta * a) {C : Finset V}
    (hC : C ∈ Structural.components I a)
    (hhigh : Structural.sigma0 * a ≤ Structural.localAdvantage I C) :
    ∃ Y, Y ⊆ C ∧ 2 ≤ Y.card ∧ Y.card ≤ 4 ∧
      2 ≤ (projected I N ρ hc Y).card ∧ (projected I N ρ hc Y).card ≤ 4 ∧
      projected I N ρ hc Y ⊆ N ∩ C ∧
      Structural.sigma0 * a / 2 ≤
        Band.benefit I (N ∩ C) (projected I N ρ hc Y) (bandTau * a) (a - 2 * ρ) -
          Structural.localCost I (projected I N ρ hc Y) - 6 * ρ := by
  have hC' : C ∈ componentsOn I I.terminals a := by rwa [componentsOn_terminals_eq]
  obtain ⟨hρa, hlo, hband, hloss⟩ := band_parameters a ρ ha hρ hsmall
  have hσa : 0 < Structural.sigma0 * a := mul_pos sigma0_pos ha
  obtain ⟨Y, hYC, h2, h4, he⟩ := localAdvantage_attained_positive I C (hσa.trans_le hhigh)
  have hP := projected_subset_retainedPart I N ρ hc hNT hρ a hρa hC' hYC
  have hD : N ∩ C ⊆ I.terminals := Finset.inter_subset_left.trans hNT
  have htransfer := band_candidate_lower I N ρ hc hNT hρ a bandTau hρa.le hlo hband
    hC' hYC h4 hD hP
  have hbound :
      Structural.sigma0 * a / 2 ≤
        Band.benefit I (N ∩ C) (projected I N ρ hc Y) (bandTau * a) (a - 2 * ρ) -
          Structural.localCost I (projected I N ρ hc Y) - 6 * ρ := by
    rw [he] at hhigh
    calc
      _ ≤ Structural.benefit I Y - Structural.localCost I Y -
          (65 * ρ + 3 * (bandTau * a)) := by
        have hmid := sub_le_sub hhigh hloss
        convert hmid using 1 <;> ring
      _ ≤ _ := htransfer
  have hP2 : 2 ≤ (projected I N ρ hc Y).card := by
    by_contra hn
    have hP1 : (projected I N ρ hc Y).card ≤ 1 := by omega
    have hz := band_benefit_zero_card_le_one I (N ∩ C) (projected I N ρ hc Y) hP1
      (bandTau * a) (a - 2 * ρ)
    rw [hz] at hbound
    linarith [Structural.localCost_nonneg I (projected I N ρ hc Y)]
  exact ⟨Y, hYC, h2, h4, hP2, (projected_card_le I N ρ hc Y).trans h4, hP, hbound⟩

/-- Retained band completeness for an actual persistent exact component.
There are no horizon hypotheses or assumed projection-saving certificates. -/
theorem retained_band_completeness (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals) (hρ : 0 ≤ ρ)
    (a : ℝ) (ha : 0 < a) (hsmall : ρ ≤ bandDelta * a) {C : Finset V}
    (hC : C ∈ Structural.components I a)
    (hphase : C ∉ phaseBad I I.terminals (a - 2 * ρ) a)
    (hhigh : Structural.sigma0 * a ≤ Structural.localAdvantage I C) :
    N ∩ C ∈ componentsOn I N a ∧ componentMap I I.terminals a (N ∩ C) = C ∧
      Structural.sigma0 * a / 2 ≤ Band.score I (N ∩ C) a ρ bandTau := by
  have hC' : C ∈ componentsOn I I.terminals a := by rwa [componentsOn_terminals_eq]
  have hρa := (band_parameters a ρ ha hρ hsmall).1
  have hcomp := persistent_retained_component I N ρ hc hNT hρ a hρa hC' hphase
  obtain ⟨Y, _, _, _, hP2, hP4, hP, hbound⟩ :=
    retained_band_witness I N ρ hc hNT hρ a ha hsmall hC hhigh
  exact ⟨hcomp.1, hcomp.2,
    hbound.trans (Band.score_witness I (N ∩ C) (projected I N ρ hc Y) a ρ bandTau hP hP2 hP4)⟩

end SteinerUpperBound.Covers.Geometry.BandCompleteness
