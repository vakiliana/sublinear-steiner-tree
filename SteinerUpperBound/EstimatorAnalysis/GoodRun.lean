module

public import SteinerUpperBound.EstimatorAnalysis.Statistics
public import SteinerUpperBound.EstimatorParameters.Normalization

@[expose] public section

namespace SteinerUpperBound.EstimatorAnalysis

open SteinerLowerBound Covers.Geometry
open scoped Classical BigOperators
open BandCompleteness

variable {V : Type*} [Fintype V]

/-- Intermediate deterministic correctness on the actual primitive good events.
No statistical probability or final accuracy hypothesis is supplied here. -/
theorem deterministic_good_run (I : Instance V) (g : Structural.Grid) (hg : g.Covers I)
    (N : Fin (g.intervals + 1) → Finset V) (A : ℝ) (hA : 1 ≤ A)
    (hN : ∀ i, N i ⊆ I.terminals)
    (hc : ∀ i, CoverOn I I.terminals (N i) (radii g i))
    (hmass : mass g N ≤ A * I.mst)
    (hphase : weightedPhaseBad I g (radii g) ≤ I.mst / 200)
    (BQ : ℕ) (hBQ : 400 * A ≤ (BQ : ℝ))
    (Z : Fin (g.intervals + 1) → ℝ)
    (hZ : ∀ i, 0 ≤ Z i ∧ Z i ≤ savingOn I (N i) (g.scale i) (5 * g.scale i / 8) ∧
      savingOn I (N i) (g.scale i) (5 * g.scale i / 8) / 2 -
        accuracy A * (N i).card ≤ Z i)
    (That upper : ℝ)
    (hThat : 0 ≤ That ∧ That ≤ totalSmallScore I g N (radii g) BQ ∧
      totalSmallScore I g N (radii g) BQ - That ≤ Structural.sigma0 * I.mst / 1000)
    (hupper : I.mst ≤ upper ∧ upper ≤ (1 + EstimatorParameters.nu) * I.mst) :
    GoodEstimate (2 - EstimatorParameters.c) I.optimum
      (Estimation.output upper (savingEstimate g Z) That EstimatorParameters.QS EstimatorParameters.QQ) := by
  have hS0 : 0 ≤ savingEstimate g Z :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (g.positive i).le (hZ i).1)
  have hsound := saving_sound_from_primitive I g N hN hc Z (fun i => (hZ i).2.1)
  have hbsound := band_sound_from_primitive I g N hN hc BQ That hThat.2.1
  have hGamma := gamma_from_primitive I g N A hA hN hc hmass Z (fun i => (hZ i).2.2)
  have hLambda := lambda_from_primitive I g N A hA hN hc hmass hphase BQ hBQ That hThat.2.2
  obtain ⟨hc0, hcS, hcQ, hcE, hc1, hnu0, hnueq, _⟩ := EstimatorParameters.scalar_bounds
  exact Estimation.estimate_correct I.mst I.optimum upper (savingEstimate g Z) That
    (Structural.gamma I g) (Structural.lambda I g) Structural.e0 Structural.sigma0
    EstimatorParameters.QS EstimatorParameters.QQ EstimatorParameters.c EstimatorParameters.nu
    I.mst_nonneg I.optimum_nonneg (TreeGeometry.mst_le_twice_optimum I)
    hupper.1 hupper.2 (by norm_num [Structural.e0]) (by norm_num [Structural.sigma0])
    (by norm_num [EstimatorParameters.QS]) (by norm_num [EstimatorParameters.QQ])
    hS0 hThat.1 hsound hbsound hGamma hLambda
    (fun hG hL => Structural.negative_evidence_of_covers I g hg hG hL)
    hc0 hcS hcQ hcE hc1 hnu0.le hnueq.le

theorem observed_flooring_transfer (I : Instance V) (root : V) (l : List V)
    (hn : l.Nodup) (hT : l.toFinset = I.terminals) (hr : root ∈ I.terminals)
    (hk : 2 ≤ I.terminals.card) (estimate : ℝ)
    (hgood : GoodEstimate (2 - EstimatorParameters.c)
      (TreeGeometry.Flooring.floored I
        (EstimatorParameters.floorScale l.length (EstimatorParameters.rowValue I.weight root l 0))).optimum estimate) :
    GoodEstimate (2 - EstimatorParameters.c / 2) I.optimum estimate := by
  rw [EstimatorParameters.observed_scale_eq I root l hn hT] at hgood
  exact TreeGeometry.Flooring.transfer_estimate I root hr hk EstimatorParameters.c
    (by norm_num [EstimatorParameters.c, EstimatorParameters.cQ])
    (by norm_num [EstimatorParameters.c, EstimatorParameters.cQ]) estimate hgood.1 hgood.2

end SteinerUpperBound.EstimatorAnalysis
