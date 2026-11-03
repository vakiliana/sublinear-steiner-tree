module

public import SteinerUpperBound.SavingEstimator.Configuration

@[expose] public section

namespace SteinerUpperBound.SavingEstimator

open QueryProgram Covers.OracleProgram
open scoped Classical

variable {Q : Type} {n k : ℕ}

noncomputable def fromParameters (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ) (p : EstimatorParameters.PublicParameters) (cache : Cache Q) :
    Code (Sym2 (Fin n)) Q (LargeCoverProgram.Answer Q n) :=
  (configure n (k + 1) p).bind (fun cfg => .tick 11
    (LargeCoverProgram.program cfg terminals root key a
      (PortGraph.RuntimeAdapter.builder key a terminals cfg.cutoff) cache))

theorem fromParameters_value (m : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (p : EstimatorParameters.PublicParameters) (cache : Cache Q) (F : LargeCoverProgram.Answer Q n → ℝ) :
    (fromParameters terminals root key a p cache).evaluate m bits (fun o => F o.value) =
      (LargeCoverProgram.program (configuration n (k + 1) p) terminals root key a
        (PortGraph.RuntimeAdapter.builder key a terminals (configuration n (k + 1) p).cutoff) cache).evaluate
          m bits (fun o => F o.value) := by
  rw [fromParameters, Mean.evaluate_bind_value, configure_evaluates]
  rfl

theorem fromParameters_valueProbability (m : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (p : EstimatorParameters.PublicParameters) (cache : Cache Q) (P : LargeCoverProgram.Answer Q n → Prop) :
    Code.valueProbability m bits (fromParameters terminals root key a p cache) P =
      Code.valueProbability m bits
        (LargeCoverProgram.program (configuration n (k + 1) p) terminals root key a
          (PortGraph.RuntimeAdapter.builder key a terminals (configuration n (k + 1) p).cutoff) cache) P :=
  fromParameters_value m bits terminals root key a p cache (fun r => if P r then 1 else 0)

end SteinerUpperBound.SavingEstimator
