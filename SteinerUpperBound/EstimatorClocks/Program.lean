module

public import SteinerUpperBound.EstimatorClocks.Selection
public import SteinerUpperBound.EstimatorParameters.Configuration

@[expose] public section

namespace SteinerUpperBound.EstimatorClocks

open QueryProgram

variable {M Q : Type*}

namespace Arithmetic

def add (a b : ℕ) : Code M Q ℕ := .tick 0 (.pure (a + b))
def mul (a b : ℕ) : Code M Q ℕ := .tick 0 (.pure (a * b))

end Arithmetic

/-- Six actual integer instructions and two field writes. -/
def byHeightProgram (height workAccount positiveAccount : ℕ) : Code M Q Budget :=
  (Arithmetic.add height 1).bind (fun h =>
    (Arithmetic.mul amplification h).bind (fun factor =>
      (Arithmetic.add workAccount 1).bind (fun aw =>
        (Arithmetic.mul factor aw).bind (fun work =>
          (Arithmetic.add positiveAccount 1).bind (fun ap =>
            (Arithmetic.mul factor ap).bind (fun positive =>
              .tick 1 (.pure ⟨work, positive⟩)))))))

/-- The logarithm has already been computed by public setup; only its use in the
height bound is charged here. -/
def fromEllProgram (knownEll workAccount positiveAccount : ℕ) : Code M Q Budget :=
  (Arithmetic.mul EstimatorParameters.heightFactor knownEll).bind
    (fun height => byHeightProgram height workAccount positiveAccount)

def fromParametersProgram (p : EstimatorParameters.PublicParameters)
    (workAccount positiveAccount : ℕ) : Code M Q Budget :=
  .tick 0 (byHeightProgram p.heights workAccount positiveAccount)

/-- Seven actual integer instructions and three field writes. -/
def factoryProgram (k workAccount positiveAccount : ℕ) : Code M Q FactoryBudget :=
  (Arithmetic.add workAccount 1).bind (fun aw =>
    (Arithmetic.mul amplification aw).bind (fun work =>
      (Arithmetic.add positiveAccount 1).bind (fun ap =>
        (Arithmetic.mul amplification ap).bind (fun threshold =>
          (Arithmetic.add threshold 14).bind (fun padded =>
            (Arithmetic.mul 2 k).bind (fun twice =>
              (Arithmetic.mul twice padded).bind (fun positive =>
                .tick 2 (.pure ⟨⟨work, positive⟩, threshold⟩))))))))

theorem byHeightProgram_evaluates (m : M → ℝ) (bits : Q → Bool)
    (height workAccount positiveAccount : ℕ) :
    Code.Evaluates m bits (byHeightProgram height workAccount positiveAccount)
      ⟨byHeight height workAccount positiveAccount, 8, 0, 0, 0⟩ := by
  intro F
  rfl

theorem fromEllProgram_evaluates (m : M → ℝ) (bits : Q → Bool)
    (n workAccount positiveAccount : ℕ) :
    Code.Evaluates m bits (fromEllProgram (EstimatorParameters.ell n) workAccount positiveAccount)
      ⟨stage n workAccount positiveAccount, 9, 0, 0, 0⟩ := by
  intro F
  rfl

theorem fromParametersProgram_evaluates (m : M → ℝ) (bits : Q → Bool)
    (n k workAccount positiveAccount : ℕ) (p : EstimatorParameters.PublicParameters)
    (hp : p = EstimatorParameters.parameters n k) :
    Code.Evaluates m bits (fromParametersProgram p workAccount positiveAccount)
      ⟨stage n workAccount positiveAccount, 9, 0, 0, 0⟩ := by
  subst p
  intro F
  rfl

theorem factoryProgram_evaluates (m : M → ℝ) (bits : Q → Bool)
    (k workAccount positiveAccount : ℕ) :
    Code.Evaluates m bits (factoryProgram k workAccount positiveAccount)
      ⟨factory k workAccount positiveAccount, 10, 0, 0, 0⟩ := by
  intro F
  rfl

end SteinerUpperBound.EstimatorClocks
