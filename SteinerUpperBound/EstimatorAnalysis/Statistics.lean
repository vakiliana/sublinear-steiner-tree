module

public import SteinerUpperBound.SavingSoundness.Grid
public import SteinerUpperBound.Covers.Geometry.BandAggregate
public import SteinerUpperBound.Covers.Geometry.BandSoundnessGrid
public import SteinerUpperBound.Structural.Theorem
public import SteinerUpperBound.EstimatorParameters.Fixed
public import SteinerUpperBound.MSTApproximation.Score

@[expose] public section

namespace SteinerUpperBound.EstimatorAnalysis

open SteinerLowerBound Covers.Geometry
open scoped Classical BigOperators
open BandCompleteness

variable {V : Type*} [Fintype V]

noncomputable abbrev delta : ℝ := EstimatorParameters.deltaCoarse

noncomputable def radii (g : Structural.Grid) (i : Fin (g.intervals + 1)) : ℝ := delta * g.scale i
noncomputable def mass (g : Structural.Grid) (N : Fin (g.intervals + 1) → Finset V) : ℝ :=
  ∑ i, g.scale i * ((N i).card : ℝ)

noncomputable def savingEstimate (g : Structural.Grid) (Z : Fin (g.intervals + 1) → ℝ) : ℝ :=
  ∑ i, g.scale i * Z i

noncomputable def accuracy (A : ℝ) : ℝ := Structural.e0 / (100000 * A)

theorem delta_eq_band : delta = BandCompleteness.bandDelta := by
  norm_num [delta, EstimatorParameters.deltaCoarse, EstimatorParameters.deltaCoarseQ, BandCompleteness.bandDelta]

theorem delta_eq_saving : delta = SavingSoundness.delta := by
  norm_num [delta, EstimatorParameters.deltaCoarse, EstimatorParameters.deltaCoarseQ, SavingSoundness.delta]

theorem band_separation :
    Structural.omega ^ (-(EstimatorParameters.QQ : ℤ)) < BandCompleteness.bandTau / 2 := by
  have h := EstimatorParameters.QQ_separation
  have ht : 0 < EstimatorParameters.tau := by norm_num [EstimatorParameters.tau, EstimatorParameters.tauQ]
  have hp : 0 < Structural.omega ^ EstimatorParameters.QQ :=
    pow_pos (by norm_num [Structural.omega]) _
  have hm := (div_lt_iff₀ ht).mp h
  have hi : 1 / Structural.omega ^ EstimatorParameters.QQ < EstimatorParameters.tau / 2 :=
    (div_lt_iff₀ hp).mpr (by nlinarith)
  have he : EstimatorParameters.tau = BandCompleteness.bandTau :=
    EstimatorParameters.ratio_casts.2.2.2
  simpa only [zpow_neg, zpow_natCast, one_div, he] using hi

theorem gamma_from_primitive (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (A : ℝ) (hA : 1 ≤ A)
    (hN : ∀ i, N i ⊆ I.terminals)
    (hc : ∀ i, CoverOn I I.terminals (N i) (radii g i))
    (hmass : mass g N ≤ A * I.mst)
    (Z : Fin (g.intervals + 1) → ℝ)
    (hlower : ∀ i, savingOn I (N i) (g.scale i) (5 * g.scale i / 8) / 2 -
      accuracy A * (N i).card ≤ Z i) :
    Structural.gamma I g ≤ 2 * savingEstimate g Z + Structural.e0 * I.mst / 1000 := by
  have hAp : 0 < A := by linarith
  have he : 0 ≤ accuracy A := by unfold accuracy; positivity [show 0 < Structural.e0 by norm_num [Structural.e0]]
  have hpoint (i : Fin (g.intervals + 1)) :
      g.scale i * Structural.rowSaving I (g.scale i) ≤
        2 * (g.scale i * Z i) + (2 * accuracy A) * (g.scale i * ((N i).card : ℝ)) := by
    have hpos := g.positive i
    have hd := structural_rowSaving_le_retained I (N i) (radii g i) (hc i) (hN i)
      (by unfold radii; norm_num [delta, EstimatorParameters.deltaCoarse, EstimatorParameters.deltaCoarseQ]; positivity)
      (g.scale i)
      (by unfold radii; norm_num [delta, EstimatorParameters.deltaCoarse, EstimatorParameters.deltaCoarseQ]; linarith)
      (by unfold radii; norm_num [delta, EstimatorParameters.deltaCoarse, EstimatorParameters.deltaCoarseQ]; linarith)
    have hrow : Structural.rowSaving I (g.scale i) ≤ 2 * Z i + 2 * accuracy A * (N i).card := by
      linarith [hlower i]
    have hm := mul_le_mul_of_nonneg_left hrow hpos.le
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) => hpoint i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have hm := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 2 * accuracy A by positivity)
  have hcoef : (2 * accuracy A) * A = Structural.e0 / 50000 := by
    unfold accuracy
    field_simp
    <;> ring
  have hsmall : (Structural.e0 / 50000) * I.mst ≤ Structural.e0 * I.mst / 1000 := by
    norm_num [Structural.e0]
    nlinarith [I.mst_nonneg]
  change Structural.gamma I g ≤ 2 * savingEstimate g Z + Structural.e0 * I.mst / 1000
  have htemp : Structural.gamma I g ≤ 2 * savingEstimate g Z + (2 * accuracy A) * mass g N := hs
  calc
    _ ≤ 2 * savingEstimate g Z + (2 * accuracy A) * mass g N := htemp
    _ ≤ 2 * savingEstimate g Z + (2 * accuracy A) * (A * I.mst) := add_le_add le_rfl hm
    _ = 2 * savingEstimate g Z + (Structural.e0 / 50000) * I.mst := by rw [← mul_assoc, hcoef]
    _ ≤ _ := add_le_add le_rfl hsmall

theorem saving_sound_from_primitive (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (hN : ∀ i, N i ⊆ I.terminals)
    (hc : ∀ i, CoverOn I I.terminals (N i) (radii g i))
    (Z : Fin (g.intervals + 1) → ℝ)
    (hupper : ∀ i, Z i ≤ savingOn I (N i) (g.scale i) (5 * g.scale i / 8)) :
    savingEstimate g Z / (32 * (EstimatorParameters.QS : ℝ)) ≤ I.mst - I.optimum := by
  have hcover : ∀ i, CoverOn I I.terminals (N i) (SavingSoundness.delta * g.scale i) := by
    simpa only [radii, delta_eq_saving] using hc
  have hgeom := SavingSoundness.retained_saving_sound_32 I g N hN hcover
  have hs : savingEstimate g Z ≤
      ∑ i, g.scale i * savingOn I (N i) (g.scale i) (5 * g.scale i / 8) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hupper i) (g.positive i).le)
  apply (div_le_iff₀ (by norm_num [EstimatorParameters.QS] : 0 < 32 * (EstimatorParameters.QS : ℝ))).mpr
  norm_num [EstimatorParameters.QS]
  nlinarith

theorem weightedLarge_le (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (A : ℝ) (hA : 1 ≤ A)
    (hmass : mass g N ≤ A * I.mst) (BQ : ℕ) (hBQ : 400 * A ≤ (BQ : ℝ)) :
    weightedLarge I g N BQ ≤ I.mst / 400 := by
  have hpoint (i : Fin (g.intervals + 1)) :
      g.scale i * ((largeRetained I (N i) (g.scale i) BQ).card : ℝ) ≤
        g.scale i * (N i).card / ((BQ : ℝ) + 1) := by
    have hc := MSTApproximation.large_components_div_bound I (N i) (g.scale i) BQ
    change ((largeRetained I (N i) (g.scale i) BQ).card : ℝ) ≤
      ((N i).card : ℝ) / ((BQ : ℝ) + 1) at hc
    have hm := mul_le_mul_of_nonneg_left hc (g.positive i).le
    convert hm using 1 <;> ring
  have hs := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) => hpoint i)
  rw [← Finset.sum_div] at hs
  have hd : 0 < (BQ : ℝ) + 1 := by positivity
  have hm := div_le_div_of_nonneg_right hmass hd.le
  have hb := mul_le_mul_of_nonneg_right hBQ I.mst_nonneg
  have hlast : A * I.mst / ((BQ : ℝ) + 1) ≤ I.mst / 400 := by
    apply (div_le_div_iff₀ hd (by norm_num : (0 : ℝ) < 400)).mpr
    calc
      _ = 400 * A * I.mst := by ring
      _ ≤ (BQ : ℝ) * I.mst := hb
      _ ≤ _ := by nlinarith [I.mst_nonneg]
  exact hs.trans (hm.trans hlast)

theorem band_sound_from_primitive (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (hN : ∀ i, N i ⊆ I.terminals)
    (hc : ∀ i, CoverOn I I.terminals (N i) (radii g i))
    (BQ : ℕ) (That : ℝ)
    (hThat : That ≤ totalSmallScore I g N (radii g) BQ) :
    That / (EstimatorParameters.QQ : ℝ) ≤ I.mst - I.optimum := by
  have hcover : ∀ i, CoverOn I I.terminals (N i) (bandDelta * g.scale i) := by
    simpa only [radii, delta_eq_band] using hc
  have hgeom := BandSoundness.small_retained_band_sound I g N hN hcover BQ EstimatorParameters.QQ
    (by norm_num [EstimatorParameters.QQ]) band_separation
  have he : (fun i => bandDelta * g.scale i) = radii g := by
    funext i
    simp only [radii, delta_eq_band]
  rw [he] at hgeom
  apply (div_le_iff₀ (by norm_num [EstimatorParameters.QQ] : (0 : ℝ) < EstimatorParameters.QQ)).mpr
  exact (hThat.trans hgeom).trans_eq (mul_comm _ _)

theorem lambda_from_primitive (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (A : ℝ) (hA : 1 ≤ A)
    (hN : ∀ i, N i ⊆ I.terminals)
    (hc : ∀ i, CoverOn I I.terminals (N i) (radii g i))
    (hmass : mass g N ≤ A * I.mst)
    (hphase : weightedPhaseBad I g (radii g) ≤ I.mst / 200)
    (BQ : ℕ) (hBQ : 400 * A ≤ (BQ : ℝ)) (That : ℝ)
    (hloss : totalSmallScore I g N (radii g) BQ - That ≤ Structural.sigma0 * I.mst / 1000) :
    Structural.lambda I g ≤
      2 * (That + Structural.sigma0 * I.mst / 1000) / Structural.sigma0 + I.mst / 100 := by
  have hrho : ∀ i, 0 ≤ radii g i := by
    intro i
    unfold radii
    exact mul_nonneg (by norm_num [delta, EstimatorParameters.deltaCoarse, EstimatorParameters.deltaCoarseQ])
      (g.positive i).le
  have hsmall : ∀ i, radii g i ≤ bandDelta * g.scale i := by
    intro i
    simp only [radii, delta_eq_band, le_refl]
  have hcomp := lambda_le_smallScore_and_bad I g N (radii g) hc hN hrho hsmall BQ
  have hlarge := weightedLarge_le I g N A hA hmass BQ hBQ
  have hm : totalSmallScore I g N (radii g) BQ ≤ That + Structural.sigma0 * I.mst / 1000 := by linarith
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 2)) sigma0_pos.le
  linarith [I.mst_nonneg]

end SteinerUpperBound.EstimatorAnalysis
