module

public import SteinerUpperBound.SavingEstimator
public import SteinerUpperBound.EstimatorClocks

@[expose] public section

namespace SteinerUpperBound.SavingEstimator.Clocked

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical

variable {Q : Type} {n k : ℕ}

def budget (p : EstimatorParameters.PublicParameters) (AW AP : ℕ) : EstimatorClocks.Budget :=
  EstimatorClocks.byHeight p.heights AW AP

theorem budget_public (n count AW AP : ℕ) :
    budget (EstimatorParameters.parameters n count) AW AP = EstimatorClocks.stage n AW AP := rfl

theorem setup_evaluates {M : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : EstimatorParameters.PublicParameters) (AW AP : ℕ) :
    Code.Evaluates m bits (EstimatorClocks.fromParametersProgram p AW AP)
      ⟨budget p AW AP, 9, 0, 0, 0⟩ := by
  intro F
  rfl

def flatten (r : Option (Option (LargeCoverProgram.Answer Q n))) : Option (ℝ × Cache Q) :=
  r.join.bind (fun answer => answer.value.map (fun Z => (Z, answer.cache)))

noncomputable def afterBudget (bd : EstimatorClocks.Budget)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (p : EstimatorParameters.PublicParameters) (cache : Cache Q) :
    Code (Sym2 (Fin n)) Q (Option (ℝ × Cache Q)) :=
  (EstimatorClocks.clocked bd (SavingEstimator.fromParameters terminals root key a p cache)).bind
    (fun r => .tick 15 (.pure (flatten r)))

noncomputable def fromParameters (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ) (p : EstimatorParameters.PublicParameters) (AW AP : ℕ) (cache : Cache Q) :
    Code (Sym2 (Fin n)) Q (Option (ℝ × Cache Q)) :=
  (EstimatorClocks.fromParametersProgram p AW AP).bind
    (fun bd => afterBudget bd terminals root key a p cache)

theorem fromParameters_value (m : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (p : EstimatorParameters.PublicParameters) (AW AP : ℕ) (cache : Cache Q)
    (F : Option (ℝ × Cache Q) → ℝ) :
    (fromParameters terminals root key a p AW AP cache).evaluate m bits (fun o => F o.value) =
      (EstimatorClocks.clocked (budget p AW AP)
        (SavingEstimator.fromParameters terminals root key a p cache)).evaluate m bits
          (fun o => F (flatten o.value)) := by
  rw [fromParameters, Mean.evaluate_bind_value, setup_evaluates, afterBudget, Mean.evaluate_bind_value]
  rfl

theorem fromParameters_valueProbability (m : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (p : EstimatorParameters.PublicParameters) (AW AP : ℕ) (cache : Cache Q)
    (P : Option (ℝ × Cache Q) → Prop) :
    Code.valueProbability m bits (fromParameters terminals root key a p AW AP cache) P =
      Code.valueProbability m bits
        (EstimatorClocks.clocked (budget p AW AP)
          (SavingEstimator.fromParameters terminals root key a p cache))
        (fun r => P (flatten r)) :=
  fromParameters_value m bits terminals root key a p AW AP cache (fun r => if P r then 1 else 0)

theorem fromParameters_work (m : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (p : EstimatorParameters.PublicParameters) (AW AP : ℕ) (cache : Cache Q) :
    (fromParameters terminals root key a p AW AP cache).evaluate m bits (fun o => (o.work : ℝ)) =
      25 + (EstimatorClocks.clocked (budget p AW AP)
        (SavingEstimator.fromParameters terminals root key a p cache)).evaluate m bits (fun o => (o.work : ℝ)) := by
  rw [fromParameters, Code.evaluate_work_bind, setup_evaluates, afterBudget, Mean.work_bind_tick]
  norm_num only [Nat.cast_ofNat]
  ring

theorem fromParameters_positive (m : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (p : EstimatorParameters.PublicParameters) (AW AP : ℕ) (cache : Cache Q) :
    (fromParameters terminals root key a p AW AP cache).evaluate m bits (fun o => (o.positiveReplies : ℝ)) =
      (EstimatorClocks.clocked (budget p AW AP)
        (SavingEstimator.fromParameters terminals root key a p cache)).evaluate m bits
          (fun o => (o.positiveReplies : ℝ)) := by
  rw [fromParameters, Code.evaluate_positive_bind, setup_evaluates, afterBudget, Mean.positive_bind_tick]
  simp

theorem fromParameters_expected (m : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (p : EstimatorParameters.PublicParameters) (AW AP : ℕ) (cache : Cache Q) :
    (fromParameters terminals root key a p AW AP cache).evaluate m bits (fun o => (o.work : ℝ)) ≤
        (budget p AW AP).workBudget + 25 ∧
      (fromParameters terminals root key a p AW AP cache).evaluate m bits (fun o => (o.positiveReplies : ℝ)) ≤
        (budget p AW AP).disclosureBudget + 1 := by
  have h := EstimatorClocks.clocked_expected_resources m bits
    (SavingEstimator.fromParameters terminals root key a p cache) (budget p AW AP)
  rw [fromParameters_work, fromParameters_positive]
  constructor <;> linarith [h.1, h.2]

end SteinerUpperBound.SavingEstimator.Clocked
