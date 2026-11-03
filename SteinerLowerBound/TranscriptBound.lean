module

public import SteinerLowerBound.MetricComparison.PublicGatedLaw
public import SteinerLowerBound.Simulation
public import SteinerLowerBound.MasterBound

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerLowerBound.TranscriptBound

open HardDistribution MetricComparison
open scoped Classical

variable {S G I C W Z : Type*}
  [Fintype S] [Fintype G] [Fintype I] [Fintype C] [Fintype W] [Fintype Z]

noncomputable def load (k : Setup S W) : ℝ :=
  VisibleMass.tripleConstant k.d k.H0 k.M * (5 * Real.exp 1 + 16)

noncomputable def metricError (k : Setup S W) (q : ℕ) : ℝ :=
  512 * scale k * Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2))

noncomputable def recordError (k : Setup S W) (r : ℕ) : ℝ :=
  2 * VisibleMass.openedBudget (S := S) k.R * (anchorConstant k.d k.H0 k.M / k.R) ^ 2 +
    2 * Fintype.card S * (load k * k.R / Fintype.card S) ^ (r + 1) +
    3 / (Fintype.card S : ℝ) ^ 3

noncomputable def error (k : Setup S W) (r q : ℕ) : ℝ :=
  2 * (metricError k q + Simulation.Public.screeningError (G := G) (I := I) k q +
    Simulation.Public.closureError k) + recordError k r

theorem metric_outputs_close (k : Setup S W) (μ ν : Law W)
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S) (hM : 0 < k.M)
    (hhalf : anchorConstant k.d k.H0 k.M / k.R ≤ 1 / 2)
    (hS : Fintype.card S = k.d * Fintype.card G) (hA : 64 ≤ Fintype.card G)
    (hRsize : k.R = Fintype.card I)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * k.R)
    (hRm : k.R ≤ Fintype.card S) (hlog : Real.log (Fintype.card S) ≤ k.R)
    (r : ℕ) (hmom : Law.MatchingMoments μ ν k.value k.value r)
    (t : DecisionTree (Public.Queries S G I C) Screening.Reply Z) (ht : t.NoRepeats)
    (q : ℕ) (hq : Screening.DecisionTree.Bounded t q) :
    Law.Close (Public.metricOutputLaw k μ t) (Public.metricOutputLaw k ν t)
      (error (G := G) (I := I) k r q) := by
  let hs := small_of_R k hR
  let simTree := Simulation.Public.experimentTree k t Prod.fst
  have hI : 0 < Fintype.card I := by
    have h := k.R_pos
    rw [hRsize] at h
    exact_mod_cast h
  have hsupport (a : Option (Subsets S k.d)) :
      potentialSupport a = a.elim ∅ Subtype.val := by cases a <;> rfl
  have hone (ρ : Law W) :
      Law.Close (Public.metricOutputLaw k ρ t)
        (Screening.Experiment.visibleOutputLaw k ρ hs simTree)
        (metricError k q + (Simulation.Public.screeningError (G := G) (I := I) k q +
          Simulation.Public.closureError k)) := by
    have hmetric := Public.public_outputs_close k ρ hR hm t ht q hq
    have hsim := Simulation.Public.experiment_projection_close_bound k ρ hM hs hhalf
      hS hA hI hRsize hC q t hq Prod.fst
    have hsource := PublicGatedLaw.gatedOutputLaw_eq_experiment k ρ hs t
    simp_rw [hsupport] at hsource
    rw [← hsource] at hsim
    exact hmetric.trans hsim
  have hvisible := Screening.Experiment.visible_protocol_close k μ ν hM hs hRm hlog hC
    r hmom simTree (Simulation.Public.experimentTree_valid k hRsize t Prod.fst)
  have hall := (hone μ).trans (hvisible.trans (hone ν).symm)
  convert hall using 1 <;> unfold error metricError recordError load <;> ring

noncomputable def comparisonConstant (d s : ℕ) (H0 M : ℝ) : ℝ :=
  MasterBound.constant s (1024 * parameterScale d H0 M)
    (2 * Screening.screeningConstant d (anchorConstant d H0 M)
      (Screening.Experiment.vertexConstant d H0 M))
    (4 * (anchorConstant d H0 M) ^ 2)
    (4 * d * VisibleMass.tripleConstant d H0 M) 2
    (VisibleMass.tripleConstant d H0 M * (5 * Real.exp 1 + 16)) 9

theorem comparisonConstant_pos (d s : ℕ) (H0 M : ℝ) :
    0 < comparisonConstant d s H0 M :=
  MasterBound.constant_pos _ _ _ _ _ _ _ _

omit [Fintype W] in
theorem error_eq (k : Setup S W) (s q : ℕ) (hRsize : k.R = Fintype.card I) :
    error (G := G) (I := I) k (s + 2) q =
      MasterBound.error s (1024 * scale k)
        (2 * Screening.screeningConstant k.d (anchorConstant k.d k.H0 k.M)
          (Screening.Experiment.vertexConstant k.d k.H0 k.M))
        (4 * (anchorConstant k.d k.H0 k.M) ^ 2)
        (4 * k.d * VisibleMass.tripleConstant k.d k.H0 k.M) 2 (load k) 9
        (Fintype.card G) k.R (Fintype.card S) q := by
  unfold error metricError recordError Simulation.Public.screeningError
    Simulation.Public.closureError Screening.Experiment.categoricalError
    Screening.Experiment.visibleLoad MasterBound.error MasterBound.opened VisibleMass.openedBudget
  rw [← hRsize]
  rw [show (s + 2) + 1 = s + 3 by omega]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

omit [Fintype W] in
theorem error_le_balance (k : Setup S W) (s q : ℕ)
    (hRsize : k.R = Fintype.card I) (hm : 1 ≤ Fintype.card S)
    (hA : 0 < Fintype.card G) (hRm : k.R ≤ Fintype.card S) (hM : 0 ≤ k.M) :
    error (G := G) (I := I) k (s + 2) q ≤
      comparisonConstant k.d s k.H0 k.M *
        (Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2)) +
          q / ((Fintype.card G : ℝ) * k.R ^ 2) +
          q / ((Fintype.card G : ℝ) ^ 2 * k.R) +
          k.R ^ (s + 3) / (Fintype.card S : ℝ) ^ (s + 2) +
          k.R / Fintype.card S + Real.log (Fintype.card S) / k.R +
          1 / (Fintype.card S : ℝ) ^ 3) := by
  rw [error_eq k s q hRsize]
  have hT : 0 ≤ VisibleMass.tripleConstant k.d k.H0 k.M := by
    have hH := k.H0_nonneg
    unfold VisibleMass.tripleConstant
    positivity
  have hbound := MasterBound.bound s (1024 * scale k)
    (2 * Screening.screeningConstant k.d (anchorConstant k.d k.H0 k.M)
      (Screening.Experiment.vertexConstant k.d k.H0 k.M))
    (4 * (anchorConstant k.d k.H0 k.M) ^ 2)
    (4 * k.d * VisibleMass.tripleConstant k.d k.H0 k.M) 2 (load k) 9
    (Fintype.card G) k.R (Fintype.card S) q (by exact_mod_cast hA) k.R_pos
    (by exact_mod_cast hm) (Nat.cast_nonneg q) hRm (by positivity)
  simpa only [comparisonConstant, load, scale_eq_parameters] using hbound

end SteinerLowerBound.TranscriptBound
