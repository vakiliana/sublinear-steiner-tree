module

public import SteinerUpperBound.ConcreteEstimator

@[expose] public section

noncomputable section

namespace SteinerUpperBound.ConcreteEstimator

open SteinerLowerBound QueryProgram EstimatorParameters

def workFactor (frontendFactor exponent : ℕ) : ℕ :=
  100 * EstimatorRunner.outerFactor frontendFactor exponent + 101

def workBound (n frontendFactor exponent : ℕ) : ℕ :=
  workFactor frontendFactor exponent * (n + 1) * t n * ell n ^ (exponent + 142)

private def Resources {n : ℕ} (p : Code (Sym2 (Fin n)) Empty ℝ)
    (m : Sym2 (Fin n) → ℝ) (bound : ℕ) : Prop :=
  ∀ seed : (p.compile m).Seed,
    let o := ((p.compile m).tree seed).output Code.emptyBits
    o.work ≤ bound ∧ o.metricQueries ≤ bound ∧ o.retentionQueries = 0

/-- Transport the entire seed-indexed claim along code equality, rather than
unfolding the concrete frontend to convert its compiled seed type. -/
private theorem resources_congr {n : ℕ} (p q : Code (Sym2 (Fin n)) Empty ℝ)
    (m : Sym2 (Fin n) → ℝ) (bound : ℕ) (hpq : p = q) (hq : Resources q m bound) :
    Resources p m bound := by
  cases hpq
  exact hq

private theorem program_two_eq {n j : ℕ} (label : Vector (Fin n) (j + 2))
    (savingFactor frontendFactor exponent : ℕ) :
    program savingFactor frontendFactor exponent label =
      EstimatorRunner.program label (0 : Fin (j + 2)) savingFactor frontendFactor exponent
        (family label 0) := rfl

private theorem runner_resources {n k : ℕ} (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (savingFactor frontendFactor exponent : ℕ) (frontend : EstimatorRunner.FrontendFamily n k)
    (m : Sym2 (Fin n) → ℝ)
    (seed : ((EstimatorRunner.program label root savingFactor frontendFactor exponent frontend).compile m).Seed) :
    let o := (((EstimatorRunner.program label root savingFactor frontendFactor exponent frontend).compile m).tree
      seed).output Code.emptyBits
    o.work ≤ workBound n frontendFactor exponent ∧ o.metricQueries ≤ workBound n frontendFactor exponent ∧
      o.retentionQueries = 0 := by
  have h := EstimatorRunner.program_resources label root savingFactor frontendFactor exponent frontend m seed
  have hb := EstimatorRunner.resource_bound n (k + 1) savingFactor frontendFactor exponent
  exact ⟨h.1.trans hb, (h.2.1.trans (Nat.le_succ _)).trans hb, h.2.2⟩

theorem program_resources {n length : ℕ} (label : Vector (Fin n) length)
    (savingFactor frontendFactor exponent : ℕ) (m : Sym2 (Fin n) → ℝ) :
    ∀ seed : ((program savingFactor frontendFactor exponent label).compile m).Seed,
    let o := (((program savingFactor frontendFactor exponent label).compile m).tree seed).output Code.emptyBits
    o.work ≤ workBound n frontendFactor exponent ∧ o.metricQueries ≤ workBound n frontendFactor exponent ∧
      o.retentionQueries = 0 := by
  cases length with
  | zero =>
      intro seed
      simp only [program, Code.compile, Compiled.leaf, DecisionTree.output, Outcome.pure]
      exact ⟨Nat.zero_le _, Nat.zero_le _, True.intro⟩
  | succ length =>
      cases length with
      | zero =>
          intro seed
          simp only [program, Code.compile, Compiled.leaf, DecisionTree.output, Outcome.pure]
          exact ⟨Nat.zero_le _, Nat.zero_le _, True.intro⟩
      | succ j =>
          exact resources_congr _ _ m (workBound n frontendFactor exponent)
            (program_two_eq label savingFactor frontendFactor exponent)
            (runner_resources label (0 : Fin (j + 2))
              savingFactor frontendFactor exponent (family label 0) m)

theorem workBound_sqrt (n frontendFactor exponent : ℕ) :
    (workBound n frontendFactor exponent : ℝ) ≤
      2 * workFactor frontendFactor exponent * (n + 1) *
        Real.sqrt ((n : ℝ) + 1) * (ell n : ℝ) ^ (exponent + 142) := by
  have ht := t_le_twice_sqrt n
  simp only [workBound, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  calc
    _ ≤ (workFactor frontendFactor exponent : ℝ) * (n + 1) *
        (2 * Real.sqrt ((n : ℝ) + 1)) * (ell n : ℝ) ^ (exponent + 142) := by
      gcongr
    _ = _ := by ring

theorem metric_queries_sqrt {n length : ℕ} (label : Vector (Fin n) length)
    (savingFactor frontendFactor exponent : ℕ) (m : Sym2 (Fin n) → ℝ)
    (seed : ((program savingFactor frontendFactor exponent label).compile m).Seed) :
    (((((program savingFactor frontendFactor exponent label).compile m).tree seed).output
        Code.emptyBits).metricQueries : ℝ) ≤
      2 * workFactor frontendFactor exponent * (n + 1) *
        Real.sqrt ((n : ℝ) + 1) * (ell n : ℝ) ^ (exponent + 142) :=
  (Nat.cast_le.mpr (program_resources label savingFactor frontendFactor exponent m seed).2.1).trans
    (workBound_sqrt n frontendFactor exponent)

end SteinerUpperBound.ConcreteEstimator
