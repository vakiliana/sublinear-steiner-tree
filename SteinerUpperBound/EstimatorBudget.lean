module

public import SteinerUpperBound.EstimatorBootstrap.Resources
public import SteinerUpperBound.EstimatorClocks

@[expose] public section

namespace SteinerUpperBound.EstimatorBudget

open QueryProgram EstimatorParameters

variable {M Q : Type*}

structure PublicBudget where
  savingWork : ℕ
  savingPositive : ℕ
  frontendWork : ℕ
  frontendPositive : ℕ
  factory : EstimatorClocks.FactoryBudget
  outer : ℕ
deriving DecidableEq, Repr

def canonical (n count savingFactor frontendFactor outerFactor exponent : ℕ) : PublicBudget :=
  let sw := savingFactor * (n + 1) * t n * ell n ^ exponent
  let sp := savingFactor * t n * ell n ^ exponent
  let fw := frontendFactor * (n + 1) * t n * ell n ^ (exponent + 140)
  let fp := frontendFactor * t n * ell n ^ (exponent + 140)
  ⟨sw, sp, fw, fp, EstimatorClocks.factory count fw fp,
    100 * (outerFactor * (n + 1) * t n * ell n ^ (exponent + 142) + 1)⟩

theorem canonical_factory (n count savingFactor frontendFactor outerFactor exponent : ℕ) :
    (canonical n count savingFactor frontendFactor outerFactor exponent).factory =
      EstimatorClocks.factory count
        (canonical n count savingFactor frontendFactor outerFactor exponent).frontendWork
        (canonical n count savingFactor frontendFactor outerFactor exponent).frontendPositive := rfl

def power (a : ℕ) : ℕ → Code M Q ℕ
  | 0 => .tick 0 (.pure 1)
  | e + 1 => (power a e).bind (fun x => .tick 1 (.pure (x * a)))

def powered (a e : ℕ) : Outcome ℕ :=
  ⟨a ^ e, 2 * e + 1, 0, 0, 0⟩

theorem power_evaluates (m : M → ℝ) (bits : Q → Bool) (a e : ℕ) :
    Code.Evaluates m bits (power a e) (powered a e) := by
  induction e with
  | zero => intro F; rfl
  | succ e ih =>
      intro F
      rw [power, Code.evaluate_bind, ih]
      simp only [Code.evaluate, powered, Outcome.add, Outcome.combine, Outcome.pure, pow_succ,
        Nat.add_zero]
      congr 2

def assemble (n count savingFactor frontendFactor outerFactor : ℕ)
    (p : PublicParameters) (savePower extraPower : ℕ) : PublicBudget :=
  let sw := savingFactor * (n + 1) * p.threshold * savePower
  let sp := savingFactor * p.threshold * savePower
  let frontPower := savePower * extraPower
  let fw := frontendFactor * (n + 1) * p.threshold * frontPower
  let fp := frontendFactor * p.threshold * frontPower
  ⟨sw, sp, fw, fp, EstimatorClocks.factory count fw fp,
    100 * (outerFactor * (n + 1) * p.threshold * (frontPower * (p.hop * p.hop)) + 1)⟩

theorem assemble_canonical (n count savingFactor frontendFactor outerFactor exponent : ℕ) :
    assemble n count savingFactor frontendFactor outerFactor (parameters n count)
        (ell n ^ exponent) (ell n ^ 140) =
      canonical n count savingFactor frontendFactor outerFactor exponent := by
  have hp : ell n ^ exponent * ell n ^ 140 = ell n ^ (exponent + 140) := (pow_add _ _ _).symm
  have hq : ell n ^ (exponent + 140) * (ell n * ell n) = ell n ^ (exponent + 142) := by
    rw [← pow_two, ← pow_add]
  simp only [assemble, canonical, parameters, hopBudget, hp, hq]

def program (n count savingFactor frontendFactor outerFactor exponent : ℕ) : Code M Q PublicBudget :=
  (setupProgram n count).bind (fun p =>
    (power p.hop exponent).bind (fun savePower =>
      (power p.hop 140).bind (fun extraPower =>
        .tick 100 (.pure (assemble n count savingFactor frontendFactor outerFactor p savePower extraPower)))))

def result (n count savingFactor frontendFactor outerFactor exponent : ℕ) : Outcome PublicBudget :=
  ⟨canonical n count savingFactor frontendFactor outerFactor exponent,
    (Setup.setupPlan n count).work + 2 * exponent + 383, 0, 0, 0⟩

theorem program_evaluates (m : M → ℝ) (bits : Q → Bool)
    (n count savingFactor frontendFactor outerFactor exponent : ℕ) :
    Code.Evaluates m bits (program n count savingFactor frontendFactor outerFactor exponent)
      (result n count savingFactor frontendFactor outerFactor exponent) := by
  intro F
  rw [program, Code.evaluate_bind, setupProgram_evaluates,
    Code.evaluate_bind, power_evaluates, Code.evaluate_bind, power_evaluates]
  simp only [Code.evaluate, Outcome.combine, Outcome.add, Outcome.pure, powered,
    Nat.add_zero]
  simp only [show (parameters n count).hop = ell n from rfl]
  rw [assemble_canonical]
  simp only [result]
  have hw : (Setup.setupPlan n count).work + (2 * exponent + 1 + (2 * 140 + 1 + (100 + 1))) =
      (Setup.setupPlan n count).work + 2 * exponent + 383 := by omega
  exact congrArg (fun w => F
    ⟨canonical n count savingFactor frontendFactor outerFactor exponent, w, 0, 0, 0⟩) hw

theorem work (n count savingFactor frontendFactor outerFactor exponent : ℕ) :
    (result n count savingFactor frontendFactor outerFactor exponent).work ≤
      Setup.workBudget n + 2 * exponent + 383 := by
  have h := Setup.setupPlan_work_le n count
  dsimp only [result]
  omega

end SteinerUpperBound.EstimatorBudget
