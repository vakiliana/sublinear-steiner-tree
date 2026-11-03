module

public import SteinerUpperBound.ConcreteEstimator.Complexity
public import SteinerUpperBound.ConcreteEstimator.Resources
public import SteinerUpperBound.SavingEstimator.Resources

@[expose] public section

noncomputable section

namespace SteinerUpperBound

open SteinerLowerBound QueryProgram

def eta0 : ℝ := EstimatorParameters.c / 2

def logExponent : ℕ := 206

def queryConstant : ℕ :=
  2 * ConcreteEstimator.workFactor
    (ConcreteEstimator.frontendFactor SavingEstimator.Resources.resourceConstant) 64

def algorithm {n length : ℕ} (terminals : Vector (Fin n) length) :
    Code (Sym2 (Fin n)) Empty ℝ :=
  ConcreteEstimator.program SavingEstimator.Resources.resourceConstant
    (ConcreteEstimator.frontendFactor SavingEstimator.Resources.resourceConstant) 64 terminals

theorem eta0_pos : 0 < eta0 := by
  norm_num [eta0, EstimatorParameters.c, EstimatorParameters.cQ]

theorem eta0_lt_one : eta0 < 1 := by
  norm_num [eta0, EstimatorParameters.c, EstimatorParameters.cQ]

theorem queryConstant_pos : 0 < queryConstant := by
  unfold queryConstant ConcreteEstimator.workFactor
  omega

theorem algorithm_resources {n length : ℕ} (terminals : Vector (Fin n) length)
    (m : Sym2 (Fin n) → ℝ) :
    ∀ seed : ((algorithm terminals).compile m).Seed,
      let out := (((algorithm terminals).compile m).tree seed).output Code.emptyBits
      out.work ≤ ConcreteEstimator.workBound n
          (ConcreteEstimator.frontendFactor SavingEstimator.Resources.resourceConstant) 64 ∧
        out.metricQueries ≤ ConcreteEstimator.workBound n
          (ConcreteEstimator.frontendFactor SavingEstimator.Resources.resourceConstant) 64 ∧
        out.retentionQueries = 0 := by
  exact ConcreteEstimator.program_resources terminals SavingEstimator.Resources.resourceConstant
    (ConcreteEstimator.frontendFactor SavingEstimator.Resources.resourceConstant) 64 m

theorem algorithm_query_time_bound {n length : ℕ} (terminals : Vector (Fin n) length)
    (m : Sym2 (Fin n) → ℝ) (seed : ((algorithm terminals).compile m).Seed) :
    let out := (((algorithm terminals).compile m).tree seed).output Code.emptyBits
    (out.work : ℝ) ≤
        queryConstant * ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) *
          (EstimatorParameters.ell n : ℝ) ^ logExponent ∧
      (out.metricQueries : ℝ) ≤
        queryConstant * ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) *
          (EstimatorParameters.ell n : ℝ) ^ logExponent ∧
      out.retentionQueries = 0 := by
  have hr := algorithm_resources terminals m seed
  have hb := ConcreteEstimator.workBound_sqrt n
    (ConcreteEstimator.frontendFactor SavingEstimator.Resources.resourceConstant) 64
  have hwork := (Nat.cast_le.mpr hr.1).trans hb
  have hqueries := (Nat.cast_le.mpr hr.2.1).trans hb
  refine ⟨?_, ?_, hr.2.2⟩
  · simpa only [queryConstant, logExponent, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hwork
  · simpa only [queryConstant, logExponent, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hqueries

end SteinerUpperBound
