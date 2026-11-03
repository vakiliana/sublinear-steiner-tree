module

public import SteinerUpperBound.MSTApproximation.Success
public import SteinerUpperBound.MSTApproximation.FrontendResources
public import SteinerUpperBound.EstimatorParameters.Configuration

@[expose] public section

namespace SteinerUpperBound.EstimatorMST

open SteinerLowerBound Covers.Geometry QueryProgram
open scoped Classical BigOperators
open Covers.Rejection Covers.FiniteSampling

variable {V Q : Type*} {k : ℕ}

def samples (n : ℕ) : ℕ := EstimatorParameters.meanSamples n (EstimatorParameters.xiMInv n)
def proposals (n terminals : ℕ) : ℕ := EstimatorParameters.samplerCap n terminals (EstimatorParameters.xiMInv n)
noncomputable def accuracy (n : ℕ) : ℝ := 1 / (EstimatorParameters.xiMInv n : ℝ)

/-- Load the four already-computed public fields and form the reciprocal accuracy.
The retained sampler and component explorer are the existing actual frontend. -/
noncomputable def withParameters (p : EstimatorParameters.PublicParameters)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q) (g : MSTApproximation.Grid)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q) :
    Code (Sym2 V) Q (MSTApproximation.IntervalAnswer Q) :=
  .tick 4 (MSTApproximation.frontend e key g EstimatorParameters.nu
    (1 / (p.mstAccuracyDenominator : ℝ)) p.mstCutoff p.mstProposalCap p.mstSamples l root cache)

noncomputable abbrev program (n : ℕ) (e : Fin (k + 1) → V)
    (key : ℕ → V → Q) (g : MSTApproximation.Grid)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q) :
    Code (Sym2 V) Q (MSTApproximation.IntervalAnswer Q) :=
  withParameters (EstimatorParameters.parameters n (k + 1)) e key g l root cache

theorem withParameters_eq_program (n : ℕ) (p : EstimatorParameters.PublicParameters)
    (hp : p = EstimatorParameters.parameters n (k + 1))
    (e : Fin (k + 1) → V) (key : ℕ → V → Q) (g : MSTApproximation.Grid)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q) :
    withParameters p e key g l root cache = program n e key g l root cache := by
  subst p
  rfl

theorem program_value (w : Sym2 V → ℝ) (bits : Q → Bool) (n : ℕ)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q) (g : MSTApproximation.Grid)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q) (F : MSTApproximation.IntervalAnswer Q → ℝ) :
    (program n e key g l root cache).evaluate w bits (fun o => F o.value) =
      (MSTApproximation.frontend e key g EstimatorParameters.nu (accuracy n) (EstimatorParameters.BM n)
        (proposals n (k + 1)) (samples n) l root cache).evaluate w bits (fun o => F o.value) := by
  rfl

theorem accuracy_eq (n : ℕ) : accuracy n = EstimatorParameters.xiM n := by
  simp only [accuracy, EstimatorParameters.xiM, EstimatorParameters.xiMQ,
    Rat.cast_div, Rat.cast_one, Rat.cast_natCast]

theorem public_tuning (n terminals : ℕ) (hk : 0 < terminals) :
    0 < accuracy n ∧ accuracy n ≤ 1 ∧
      accuracy n = EstimatorParameters.nu / (100 * (EstimatorParameters.AM n : ℝ)) ∧
      (EstimatorParameters.BM n : ℝ) = 100 * (EstimatorParameters.AM n : ℝ) / EstimatorParameters.nu ∧
      0 < samples n ∧
      256 = EstimatorParameters.beta n * ((samples n : ℝ) * accuracy n ^ 2) ∧
      Real.exp (-(proposals n terminals : ℝ) / terminals) ≤
        EstimatorParameters.beta n * accuracy n / (16 * samples n) := by
  obtain ⟨_, _, _, _, _, _, hx, hx1⟩ := EstimatorParameters.score_ranges n
  have hd := (EstimatorParameters.integer_budget_pos n).2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, (EstimatorParameters.integer_budget_equations n).2.2,
    EstimatorParameters.meanSamples_positive _ _ hd, ?_, ?_⟩
  · simpa only [accuracy_eq] using hx
  · simpa only [accuracy_eq] using hx1
  · rw [accuracy_eq]
    exact (EstimatorParameters.score_scalar_equations n).2.2.2
  · exact (EstimatorParameters.meanSamples_exact n (EstimatorParameters.xiMInv n) hd).symm
  · exact EstimatorParameters.samplerCap_test n terminals (EstimatorParameters.xiMInv n) hk hd

variable [Fintype V]

theorem program_law (I : Instance V) (bits : Q → Bool) (n : ℕ)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q) (g : MSTApproximation.Grid)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct bits cache) (he : Finset.univ.image e = l.toFinset)
    (hr : ∀ i < g.intervals, bits (key i (e root)) = true)
    (F : MSTApproximation.IntervalAnswer Q → ℝ) :
    (program n e key g l root cache).evaluate I.weight bits (fun o => F o.value) =
      (tape (poolLaw (proposals n (k + 1)) (samples n)) (List.range g.intervals).length).expect
        (fun rows => F (MSTApproximation.answerTrace I.weight bits e key g EstimatorParameters.nu
          (accuracy n) (EstimatorParameters.BM n) (proposals n (k + 1)) (samples n) l root cache rows)) := by
  rw [program_value]
  exact MSTApproximation.frontend_law I bits e key g EstimatorParameters.nu (accuracy n) (EstimatorParameters.BM n)
    (proposals n (k + 1)) (samples n) l root cache hc he hr F

theorem program_probability (I : Instance V) (bits : Q → Bool) (n : ℕ)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q) (g : MSTApproximation.Grid)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct bits cache) (he : Finset.univ.image e = l.toFinset)
    (hr : ∀ i < g.intervals, bits (key i (e root)) = true)
    (E : Set (MSTApproximation.IntervalAnswer Q)) :
    Code.probability I.weight bits (program n e key g l root cache) {o | o.value ∈ E} =
      (tape (poolLaw (proposals n (k + 1)) (samples n)) (List.range g.intervals).length).prob
        {rows | MSTApproximation.answerTrace I.weight bits e key g EstimatorParameters.nu
          (accuracy n) (EstimatorParameters.BM n) (proposals n (k + 1)) (samples n) l root cache rows ∈ E} := by
  classical
  have heq : Code.probability I.weight bits (program n e key g l root cache) {o | o.value ∈ E} =
      Code.probability I.weight bits (MSTApproximation.frontend e key g EstimatorParameters.nu (accuracy n)
        (EstimatorParameters.BM n) (proposals n (k + 1)) (samples n) l root cache) {o | o.value ∈ E} := by rfl
  rw [heq]
  exact MSTApproximation.frontend_probability I bits e key g EstimatorParameters.nu (accuracy n)
    (EstimatorParameters.BM n) (proposals n (k + 1)) (samples n) l root cache hc he hr E

end SteinerUpperBound.EstimatorMST
