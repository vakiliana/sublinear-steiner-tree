module

public import SteinerUpperBound.QueryProgram.Loops

@[expose] public section

namespace SteinerUpperBound.QueryProgram

instance outcomeMonad : Monad Outcome where
  pure := Outcome.pure
  bind a k := a.combine (k a.value)
  map := Outcome.map

instance codeMonad (M Q : Type*) : Monad (Code M Q) where
  pure := Code.pure
  bind := Code.bind
  map := Code.map

namespace Code

def operation {M Q R : Type*} (work : ℕ) (r : R) : Code M Q R :=
  .tick work (.pure r)

theorem operation_evaluates {M Q R : Type*} (m : M → ℝ) (b : Q → Bool)
    (work : ℕ) (r : R) :
    Evaluates m b (operation work r) ((Outcome.pure r).add (work + 1) 0 0 0) := by
  intro F
  rfl

end Code

end SteinerUpperBound.QueryProgram
