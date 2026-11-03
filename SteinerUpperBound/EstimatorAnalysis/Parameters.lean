module

public import SteinerUpperBound.EstimatorAnalysis.GoodRun
public import SteinerUpperBound.EstimatorParameters.Scores

@[expose] public section

namespace SteinerUpperBound.EstimatorAnalysis

open SteinerLowerBound Covers.Geometry
open scoped Classical BigOperators
open BandCompleteness

variable {V : Type*} [Fintype V]

theorem parameter_good_run (I : Instance V) (g : Structural.Grid) (hg : g.Covers I)
    (N : Fin (g.intervals + 1) → Finset V) (n : ℕ)
    (hN : ∀ i, N i ⊆ I.terminals)
    (hc : ∀ i, CoverOn I I.terminals (N i) (radii g i))
    (hmass : mass g N ≤ (EstimatorParameters.A n : ℝ) * I.mst)
    (hphase : weightedPhaseBad I g (radii g) ≤ I.mst / 200)
    (Z : Fin (g.intervals + 1) → ℝ)
    (hZ : ∀ i, 0 ≤ Z i ∧ Z i ≤ savingOn I (N i) (g.scale i) (5 * g.scale i / 8) ∧
      savingOn I (N i) (g.scale i) (5 * g.scale i / 8) / 2 -
        EstimatorParameters.eps n * (N i).card ≤ Z i)
    (That upper : ℝ)
    (hThat : 0 ≤ That ∧ That ≤ totalSmallScore I g N (radii g) (EstimatorParameters.BQ n) ∧
      totalSmallScore I g N (radii g) (EstimatorParameters.BQ n) - That ≤ Structural.sigma0 * I.mst / 1000)
    (hupper : I.mst ≤ upper ∧ upper ≤ (1 + EstimatorParameters.nu) * I.mst) :
    GoodEstimate (2 - EstimatorParameters.c) I.optimum
      (Estimation.output upper (savingEstimate g Z) That EstimatorParameters.QS EstimatorParameters.QQ) := by
  have hA : (1 : ℝ) ≤ EstimatorParameters.A n := by exact_mod_cast EstimatorParameters.A_pos n
  have hBQ : 400 * (EstimatorParameters.A n : ℝ) ≤ EstimatorParameters.BQ n :=
    (EstimatorParameters.integer_budget_equations n).2.1.symm.le
  have he : accuracy (EstimatorParameters.A n : ℝ) = EstimatorParameters.eps n :=
    (EstimatorParameters.score_scalar_equations n).1.symm
  exact deterministic_good_run I g hg N _ hA hN hc hmass hphase (EstimatorParameters.BQ n) hBQ
    Z (by simpa only [he] using hZ) That upper hThat hupper

end SteinerUpperBound.EstimatorAnalysis
