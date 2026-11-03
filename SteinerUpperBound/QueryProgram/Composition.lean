module

public import SteinerUpperBound.QueryProgram.Cap

@[expose] public section

namespace SteinerUpperBound.QueryProgram

open SteinerLowerBound
open scoped Classical

namespace Outcome

def map {R S : Type*} (f : R → S) (o : Outcome R) : Outcome S :=
  ⟨f o.value, o.work, o.metricQueries, o.retentionQueries, o.positiveReplies⟩

end Outcome

namespace Code

variable {M Q R S : Type*}

theorem evaluate_bind (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (k : R → Code M Q S) (F : Outcome S → ℝ) :
    (p.bind k).evaluate m b F =
      p.evaluate m b (fun a =>
        (k a.value).evaluate m b (fun o => F (a.combine o))) := by
  induction p generalizing F with
  | pure r => simp only [bind, evaluate, Outcome.pure, Outcome.combine, Nat.zero_add]
  | metric q next ih =>
      simp only [bind, evaluate]
      simpa only [Outcome.add, Outcome.combine, Nat.add_assoc] using
        ih (m q) (fun o => F (o.add 1 1 0 0))
  | retained q next ih =>
      simp only [bind, evaluate]
      simpa only [Outcome.add, Outcome.combine, Nat.add_assoc] using
        ih (b q) (fun o => F (o.add 1 0 1 (if b q then 1 else 0)))
  | uniform n next ih =>
      simp only [bind, evaluate]
      apply congrArg (Law.uniform (Fin (n + 1))).expect
      funext a
      simpa only [Outcome.add, Outcome.combine, Nat.add_assoc] using
        ih a (fun o => F (o.add 1 0 0 0))
  | coin rate next ih =>
      simp only [bind, evaluate]
      apply congrArg (CategoricalCoupling.bernoulli rate).expect
      funext a
      simpa only [Outcome.add, Outcome.combine, Nat.add_assoc] using
        ih a (fun o => F (o.add 2 0 0 0))
  | tick n next ih =>
      simp only [bind, evaluate]
      simpa only [Outcome.add, Outcome.combine, Nat.add_assoc] using
        ih (fun o => F (o.add (n + 1) 0 0 0))

theorem evaluate_map (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (f : R → S) (F : Outcome S → ℝ) :
    (p.map f).evaluate m b F = p.evaluate m b (fun o => F (o.map f)) := by
  simp only [map, evaluate_bind, evaluate, Outcome.pure, Outcome.combine, Outcome.map,
    Nat.add_zero]

def Evaluates (m : M → ℝ) (b : Q → Bool) (p : Code M Q R) (o : Outcome R) : Prop :=
  ∀ F, p.evaluate m b F = F o

theorem evaluates_pure (m : M → ℝ) (b : Q → Bool) (r : R) :
    Evaluates m b (.pure r) (.pure r) := fun _ => rfl

theorem Evaluates.bind (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (k : R → Code M Q S) (a : Outcome R) (o : Outcome S)
    (hp : Evaluates m b p a) (hk : Evaluates m b (k a.value) o) :
    Evaluates m b (p.bind k) (a.combine o) := by
  intro F
  rw [evaluate_bind, hp, hk]

theorem evaluates_metric (m : M → ℝ) (b : Q → Bool) (q : M) :
    Evaluates m b (.metric q .pure) ⟨m q, 1, 1, 0, 0⟩ := by
  intro F
  rfl

theorem evaluates_retained (m : M → ℝ) (b : Q → Bool) (q : Q) :
    Evaluates m b (.retained q .pure) ⟨b q, 1, 0, 1, if b q then 1 else 0⟩ := by
  intro F
  rfl

theorem Evaluates.tick (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (a : Outcome R) (hp : Evaluates m b p a) (n : ℕ) :
    Evaluates m b (.tick n p) (a.add (n + 1) 0 0 0) := by
  intro F
  exact hp _

end Code

end SteinerUpperBound.QueryProgram
