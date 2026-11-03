module

public import SteinerUpperBound.Covers.Geometry.BandSoundnessBenefit

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry.BandSoundness

open SteinerLowerBound MeasureTheory
open scoped Classical BigOperators Interval
open BandCompleteness

variable {V : Type*} [Fintype V]

theorem retained_quotient_disjoint (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hρ : 0 ≤ ρ) (a t : ℝ)
    (ht : t ≤ a - 2 * ρ) {C D Y Z : Finset V}
    (hC : C ∈ componentsOn I N a) (hD : D ∈ componentsOn I N a) (hCD : C ≠ D)
    (hY : Y ⊆ C) (hZ : Z ⊆ D) :
    Disjoint (Y.image (Structural.threshold I t).connectedComponentMk)
      (Z.image (Structural.threshold I t).connectedComponentMk) := by
  classical
  apply Finset.disjoint_left.mpr
  intro c hcY hcZ
  obtain ⟨x, hx, hxc⟩ := Finset.mem_image.mp hcY
  obtain ⟨y, hy, hyc⟩ := Finset.mem_image.mp hcZ
  have hr : (Structural.threshold I t).Reachable x y :=
    SimpleGraph.ConnectedComponent.exact (hxc.trans hyc.symm)
  have hrf : (thresholdOn I I.terminals (a - 2 * ρ)).Reachable x y := by
    rw [← thresholdOn_terminals_eq] at hr
    exact reachable_mono I (Finset.Subset.refl I.terminals) ht hr
  have hp := project_reachable I I.terminals N ρ hc hρ a hrf
  rw [project_fix I I.terminals N ρ hc (componentsOn_subset I N a hC (hY hx)),
    project_fix I I.terminals N ρ hc (componentsOn_subset I N a hD (hZ hy))] at hp
  have he := componentOn_eq_of_reachable I N a hp
  rw [componentOn_eq_of_mem I N a hC (hY hx), componentOn_eq_of_mem I N a hD (hZ hy)] at he
  exact hCD he

theorem cell_gain_additive (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hρ : 0 ≤ ρ) (a t : ℝ)
    (ht : t ≤ a - 2 * ρ) (Y : ↥(componentsOn I N a) → Finset V)
    (hY : ∀ C, Y C ⊆ C.val) :
    GraphRank.gain (Structural.threshold I t)
      (SavingSoundness.graphUnion (fun C => Network.completeOn (Y C))) =
        ∑ C, globalGain I (Y C) t := by
  classical
  apply gain_disjoint_cliques
  intro C D hCD
  exact retained_quotient_disjoint I N ρ hc hρ a t ht C.property D.property
    (fun he => hCD (Subtype.ext he)) (hY C) (hY D)

/-- Pure geometric scale data, not a network or benefit certificate. -/
structure ScaleData (I : Instance V) where
  a : ℝ
  rho : ℝ
  retained : Finset V
  positive : 0 < a
  rho_nonneg : 0 ≤ rho
  rho_small : rho ≤ bandDelta * a
  subset : retained ⊆ I.terminals
  cover : CoverOn I I.terminals retained rho

abbrev Cells (I : Instance V) (s : ScaleData I) := ↥(componentsOn I s.retained s.a)

theorem cell_exists (I : Instance V) (s : ScaleData I) (C : Cells I s) :
    ∃ Y : Finset V, ∃ K : SimpleGraph V,
      Y ⊆ C.val ∧ Y.card ≤ 4 ∧ Structural.OneCenterNetwork Y K ∧
      Band.score I C.val s.a s.rho bandTau + GraphCost.cost I.weight K ≤
        ∫ t in (bandTau * s.a)..(s.a - 2 * s.rho), globalGain I Y t := by
  have hp := band_parameters s.a s.rho s.positive s.rho_nonneg s.rho_small
  exact score_network_exists I s.retained s.rho s.cover s.rho_nonneg s.a bandTau
    hp.2.1 hp.2.2.1 C.val C.property

noncomputable def cellWitness (I : Instance V) (s : ScaleData I) (C : Cells I s) : Finset V :=
  Classical.choose (cell_exists I s C)

noncomputable def cellNetwork (I : Instance V) (s : ScaleData I) (C : Cells I s) : SimpleGraph V :=
  Classical.choose (Classical.choose_spec (cell_exists I s C))

theorem cell_spec (I : Instance V) (s : ScaleData I) (C : Cells I s) :
    cellWitness I s C ⊆ C.val ∧ (cellWitness I s C).card ≤ 4 ∧
      Structural.OneCenterNetwork (cellWitness I s C) (cellNetwork I s C) ∧
      Band.score I C.val s.a s.rho bandTau + GraphCost.cost I.weight (cellNetwork I s C) ≤
        ∫ t in (bandTau * s.a)..(s.a - 2 * s.rho), globalGain I (cellWitness I s C) t :=
  Classical.choose_spec (Classical.choose_spec (cell_exists I s C))

noncomputable def scaleLinks (I : Instance V) (s : ScaleData I) : SimpleGraph V :=
  SavingSoundness.graphUnion (fun C : Cells I s => Network.completeOn (cellWitness I s C))

noncomputable def scaleNetworks (I : Instance V) (s : ScaleData I) : SimpleGraph V :=
  SavingSoundness.graphUnion (cellNetwork I s)

noncomputable def scaleScore (I : Instance V) (s : ScaleData I) : ℝ :=
  ∑ C ∈ componentsOn I s.retained s.a, Band.score I C s.a s.rho bandTau

theorem scaleLinks_terminalOnly (I : Instance V) (s : ScaleData I) :
    Network.TerminalOnly I.terminals (scaleLinks I s) := by
  intro x y hxy
  obtain ⟨C, hC⟩ := (SavingSoundness.graphUnion_adj _ x y).mp hxy
  obtain ⟨_, hx, hy⟩ := (Network.completeOn_adj _ x y).mp hC
  have hsub := (cell_spec I s C).1.trans (componentsOn_subset I s.retained s.a C.property)
  exact ⟨s.subset (hsub hx), s.subset (hsub hy)⟩

theorem scaleNetworks_connect (I : Instance V) (s : ScaleData I) :
    ∀ x y, (scaleLinks I s).Adj x y → (scaleNetworks I s).Reachable x y := by
  intro x y hxy
  obtain ⟨C, hC⟩ := (SavingSoundness.graphUnion_adj _ x y).mp hxy
  obtain ⟨_, hx, hy⟩ := (Network.completeOn_adj _ x y).mp hC
  exact (((cell_spec I s C).2.2.1.1) x hx y hy).mono
    (SavingSoundness.le_graphUnion _ C)

theorem scaleNetworks_cost (I : Instance V) (s : ScaleData I) :
    GraphCost.cost I.weight (scaleNetworks I s) ≤
      ∑ C : Cells I s, GraphCost.cost I.weight (cellNetwork I s C) :=
  SavingSoundness.graphUnion_cost I.weight I.weight_nonneg _

theorem scale_score_cost_le_band (I : Instance V) (s : ScaleData I) :
    scaleScore I s + GraphCost.cost I.weight (scaleNetworks I s) ≤
      ∫ t in (bandTau * s.a)..(s.a - 2 * s.rho),
        GraphRank.gain (Structural.threshold I t) (scaleLinks I s) := by
  classical
  have hp := band_parameters s.a s.rho s.positive s.rho_nonneg s.rho_small
  have hsum := Finset.sum_le_sum (fun C (_ : C ∈ (Finset.univ : Finset (Cells I s))) =>
    (cell_spec I s C).2.2.2)
  rw [Finset.sum_add_distrib] at hsum
  have hscore : scaleScore I s =
      ∑ C : Cells I s, Band.score I C.val s.a s.rho bandTau :=
    (Finset.sum_coe_sort (componentsOn I s.retained s.a)
      (fun C => Band.score I C s.a s.rho bandTau)).symm
  have hint :
      (∑ C : Cells I s, ∫ t in (bandTau * s.a)..(s.a - 2 * s.rho),
        globalGain I (cellWitness I s C) t) =
      ∫ t in (bandTau * s.a)..(s.a - 2 * s.rho),
        GraphRank.gain (Structural.threshold I t) (scaleLinks I s) := by
    rw [← intervalIntegral.integral_finsetSum
      (fun C _ => globalGain_integrable I (cellWitness I s C) _ _)]
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le hp.2.2.1] at ht
    exact (cell_gain_additive I s.retained s.rho s.cover s.rho_nonneg s.a t ht.2
      (cellWitness I s) (fun C => (cell_spec I s C).1)).symm
  calc
    _ ≤ (∑ C : Cells I s, Band.score I C.val s.a s.rho bandTau) +
        ∑ C : Cells I s, GraphCost.cost I.weight (cellNetwork I s C) :=
      add_le_add (le_of_eq hscore) (scaleNetworks_cost I s)
    _ ≤ _ := hsum
    _ = _ := hint

end SteinerUpperBound.Covers.Geometry.BandSoundness
