module

public import SteinerLowerBound.QueryModel
public import SteinerLowerBound.LawOperations

@[expose] public section

namespace SteinerUpperBound.QueryProgram

open SteinerLowerBound
open scoped Classical

structure Outcome (R : Type*) where
  value : R
  work : ℕ
  metricQueries : ℕ
  retentionQueries : ℕ
  positiveReplies : ℕ

namespace Outcome

def pure {R : Type*} (r : R) : Outcome R := ⟨r, 0, 0, 0, 0⟩

def add {R : Type*} (w m q z : ℕ) (o : Outcome R) : Outcome R :=
  ⟨o.value, w + o.work, m + o.metricQueries, q + o.retentionQueries,
    z + o.positiveReplies⟩

def combine {R S : Type*} (a : Outcome R) (b : Outcome S) : Outcome S :=
  ⟨b.value, a.work + b.work, a.metricQueries + b.metricQueries,
    a.retentionQueries + b.retentionQueries, a.positiveReplies + b.positiveReplies⟩

@[simp]
theorem add_combine {R S : Type*} (w m q z : ℕ) (a : Outcome R) (b : Outcome S) :
    combine (add w m q z a) b = add w m q z (combine a b) := by
  cases a
  cases b
  simp only [add, combine, Nat.add_assoc]

end Outcome

inductive Code (M Q R : Type*)
  | pure : R → Code M Q R
  | metric : M → (ℝ → Code M Q R) → Code M Q R
  | retained : Q → (Bool → Code M Q R) → Code M Q R
  | uniform : (n : ℕ) → (Fin (n + 1) → Code M Q R) → Code M Q R
  | coin : Rate → (Bool → Code M Q R) → Code M Q R
  | tick : ℕ → Code M Q R → Code M Q R

namespace Code

variable {M Q R S : Type*}

def bind (p : Code M Q R) (k : R → Code M Q S) : Code M Q S :=
  match p with
  | .pure r => k r
  | .metric q next => .metric q (fun a => (next a).bind k)
  | .retained q next => .retained q (fun a => (next a).bind k)
  | .uniform n next => .uniform n (fun a => (next a).bind k)
  | .coin rate next => .coin rate (fun a => (next a).bind k)
  | .tick n next => .tick n (next.bind k)

def map (f : R → S) (p : Code M Q R) : Code M Q S :=
  p.bind (fun r => .pure (f r))

noncomputable def evaluate (m : M → ℝ) (b : Q → Bool) :
    Code M Q R → (Outcome R → ℝ) → ℝ
  | .pure r, F => F (.pure r)
  | .metric q next, F => (next (m q)).evaluate m b (fun o => F (o.add 1 1 0 0))
  | .retained q next, F =>
      (next (b q)).evaluate m b (fun o => F (o.add 1 0 1 (if b q then 1 else 0)))
  | .uniform n next, F =>
      (Law.uniform (Fin (n + 1))).expect
        (fun a => (next a).evaluate m b (fun o => F (o.add 1 0 0 0)))
  | .coin rate next, F =>
      (CategoricalCoupling.bernoulli rate).expect
        (fun a => (next a).evaluate m b (fun o => F (o.add 2 0 0 0)))
  | .tick n next, F => next.evaluate m b (fun o => F (o.add (n + 1) 0 0 0))

noncomputable def probability (m : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (E : Set (Outcome R)) : ℝ :=
  p.evaluate m b (fun o => if o ∈ E then 1 else 0)

end Code

end SteinerUpperBound.QueryProgram
