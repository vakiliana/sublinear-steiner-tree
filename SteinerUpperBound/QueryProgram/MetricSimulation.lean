module

public import SteinerUpperBound.QueryProgram.Consequences

@[expose] public section

namespace SteinerUpperBound.QueryProgram

open SteinerLowerBound
open scoped Classical

namespace Outcome

def metricWork {R : Type*} (extra : ℕ) (o : Outcome R) : Outcome R :=
  {o with work := o.work + (extra + 1) * o.metricQueries}

end Outcome

namespace Code

variable {M Q R : Type*}

def mapMetric (response : M → ℝ → ℝ) (extra : ℕ) : Code M Q R → Code M Q R
  | .pure r => .pure r
  | .metric q next => .metric q (fun a =>
      .tick extra ((next (response q a)).mapMetric response extra))
  | .retained q next => .retained q (fun a => (next a).mapMetric response extra)
  | .uniform n next => .uniform n (fun a => (next a).mapMetric response extra)
  | .coin rate next => .coin rate (fun a => (next a).mapMetric response extra)
  | .tick n next => .tick n (next.mapMetric response extra)

theorem evaluate_mapMetric (m : M → ℝ) (bits : Q → Bool)
    (response : M → ℝ → ℝ) (extra : ℕ) (p : Code M Q R) (F : Outcome R → ℝ) :
    (p.mapMetric response extra).evaluate m bits F =
      p.evaluate (fun q => response q (m q)) bits (fun o => F (o.metricWork extra)) := by
  induction p generalizing F with
  | pure r =>
      simp only [mapMetric, evaluate, Outcome.metricWork, Outcome.pure, Nat.mul_zero,
        Nat.add_zero]
  | metric q next ih =>
      simp only [mapMetric, evaluate]
      simpa only [Outcome.metricWork, Outcome.add, Nat.mul_add, Nat.mul_one, Nat.mul_zero,
        Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (response q (m q))
          (fun o => F ((o.add (extra + 1) 0 0 0).add 1 1 0 0))
  | retained q next ih =>
      simp only [mapMetric, evaluate]
      simpa only [Outcome.metricWork, Outcome.add, Nat.mul_zero, Nat.zero_add,
        Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (bits q) (fun o => F (o.add 1 0 1 (if bits q then 1 else 0)))
  | uniform n next ih =>
      simp only [mapMetric, evaluate]
      apply congrArg (Law.uniform (Fin (n + 1))).expect
      funext a
      simpa only [Outcome.metricWork, Outcome.add, Nat.mul_zero, Nat.zero_add,
        Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih a (fun o => F (o.add 1 0 0 0))
  | coin rate next ih =>
      simp only [mapMetric, evaluate]
      apply congrArg (CategoricalCoupling.bernoulli rate).expect
      funext a
      simpa only [Outcome.metricWork, Outcome.add, Nat.mul_zero, Nat.zero_add,
        Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih a (fun o => F (o.add 2 0 0 0))
  | tick n next ih =>
      simp only [mapMetric, evaluate]
      simpa only [Outcome.metricWork, Outcome.add, Nat.mul_zero, Nat.zero_add,
        Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (fun o => F (o.add (n + 1) 0 0 0))

theorem mapMetric_value (m : M → ℝ) (bits : Q → Bool)
    (response : M → ℝ → ℝ) (extra : ℕ) (p : Code M Q R) (F : R → ℝ) :
    (p.mapMetric response extra).evaluate m bits (fun o => F o.value) =
      p.evaluate (fun q => response q (m q)) bits (fun o => F o.value) := by
  rw [evaluate_mapMetric]
  rfl

theorem mapMetric_queries (m : M → ℝ) (bits : Q → Bool)
    (response : M → ℝ → ℝ) (extra : ℕ) (p : Code M Q R) :
    (p.mapMetric response extra).evaluate m bits (fun o => (o.metricQueries : ℝ)) =
      p.evaluate (fun q => response q (m q)) bits (fun o => (o.metricQueries : ℝ)) := by
  rw [evaluate_mapMetric]
  rfl

theorem mapMetric_work (m : M → ℝ) (bits : Q → Bool)
    (response : M → ℝ → ℝ) (extra : ℕ) (p : Code M Q R) :
    (p.mapMetric response extra).evaluate m bits (fun o => (o.work : ℝ)) =
      p.evaluate (fun q => response q (m q)) bits (fun o => (o.work : ℝ)) +
        ((extra + 1 : ℕ) : ℝ) *
          p.evaluate (fun q => response q (m q)) bits (fun o => (o.metricQueries : ℝ)) := by
  rw [evaluate_mapMetric]
  simp only [Outcome.metricWork, Nat.cast_add, Nat.cast_mul, evaluate_add]
  congr 1
  rw [← compile_expect (fun q => response q (m q)) bits p
      (fun o => ((extra : ℝ) + ((1 : ℕ) : ℝ)) * (o.metricQueries : ℝ)),
    ← compile_expect (fun q => response q (m q)) bits p (fun o => (o.metricQueries : ℝ))]
  exact Law.expect_const_mul _ _ _

end Code

end SteinerUpperBound.QueryProgram
