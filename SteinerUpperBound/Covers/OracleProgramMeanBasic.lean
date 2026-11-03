module

public import SteinerUpperBound.Covers.OracleProgram
public import SteinerUpperBound.ScoreSampling
public import SteinerUpperBound.EstimationAlgebra

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram.Mean

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {M Q U : Type*}

abbrev Callback (M Q U : Type*) :=
  U → Cache Q → Code M Q (ℝ × Cache Q)

/-- Only cache-threading, actual callback calls, and charged additions occur
here. No retained set or analysis kernel is a runtime input. -/
noncomputable def scores (callback : Callback M Q U) :
    (s : ℕ) → (Fin s → U) → Cache Q → Code M Q (ℝ × Cache Q)
  | 0, _, cache => .tick 1 (.pure (0, cache))
  | s + 1, labels, cache => .tick 2
      ((callback (labels 0) cache).bind (fun head =>
        (scores callback s (Fin.tail labels) head.2).bind (fun tail =>
          .tick 2 (.pure (head.1 + tail.1, tail.2)))))

structure Result (Q : Type*) (k s : ℕ) where
  value : Option ℝ
  sample : Sampler.Records Q k s
  cache : Cache Q
  lower : ℝ
  upper : ℝ

noncomputable def finish {k s : ℕ} (ξ : ℝ) (r : Sampler.Records Q k s)
    (value : Option ℝ) (cache : Cache Q) : Result Q k s :=
  ⟨value, r, cache,
    Rejection.lowerEstimate (Fintype.card (Fin (k + 1))) s r.store.proposals ξ,
    Rejection.upperEstimate (Fintype.card (Fin (k + 1))) s r.store.proposals ξ⟩

/-- The sampler is run once. Failed rejection rows and proposal aborts produce
`none`, rather than treating a root fallback as an accepted observation. -/
noncomputable def afterSample {k s : ℕ} (ξ : ℝ)
    (callback : Callback M Q (Fin (k + 1))) (r : Sampler.Records Q k s) :
    Code M Q (Result Q k s) :=
  .tick 7 (match r.labels with
    | none => .tick 31 (.pure (finish ξ r none r.store.cache))
    | some labels =>
      if r.successful then
        (scores callback s labels r.store.cache).bind (fun z =>
          .tick 31 (.pure (finish ξ r (some (z.1 / s)) z.2)))
      else .tick 31 (.pure (finish ξ r none r.store.cache)))

noncomputable def program {k : ℕ} (query : Fin (k + 1) → Q) (root : Fin (k + 1))
    (C s B : ℕ) (cache : Cache Q) (ξ : ℝ)
    (callback : Callback M Q (Fin (k + 1))) : Code M Q (Result Q k s) :=
  (Sampler.program query root C s B cache).bind (afterSample ξ callback)

theorem evaluate_bind_value {R S : Type*} (m : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (next : R → Code M Q S) (F : S → ℝ) :
    (p.bind next).evaluate m b (fun o => F o.value) =
      p.evaluate m b (fun a => (next a.value).evaluate m b (fun o => F o.value)) := by
  exact Code.evaluate_bind m b p next _

theorem evaluate_congr_runs {R : Type*} (m : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (F G : Outcome R → ℝ)
    (h : ∀ o, Runs m b p o → F o = G o) :
    p.evaluate m b F = p.evaluate m b G := by
  rw [← Code.compile_expect, ← Code.compile_expect]
  unfold Compiled.expect
  apply congrArg (p.compile m).law.expect
  funext seed
  exact h _ (runs_compile m b p seed)

theorem evaluate_mono_runs {R : Type*} (m : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (F G : Outcome R → ℝ)
    (h : ∀ o, Runs m b p o → F o ≤ G o) :
    p.evaluate m b F ≤ p.evaluate m b G := by
  rw [← Code.compile_expect, ← Code.compile_expect]
  unfold Compiled.expect
  exact (p.compile m).law.expect_mono (fun seed => h _ (runs_compile m b p seed))

theorem runs_bind_inv {R S : Type*} (m : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (next : R → Code M Q S) (o : Outcome S)
    (h : Runs m b (p.bind next) o) :
    ∃ a : Outcome R, ∃ z : Outcome S,
      Runs m b p a ∧ Runs m b (next a.value) z ∧ o = a.combine z := by
  induction p generalizing o with
  | pure r =>
    exact ⟨.pure r, o, .pure r, h, by simp [Outcome.pure, Outcome.combine]⟩
  | metric q cont ih =>
    cases h with
    | metric h =>
      obtain ⟨a, z, ha, hz, rfl⟩ := ih (m q) _ h
      exact ⟨a.add 1 1 0 0, z, .metric ha, hz, by
        simp [Outcome.add, Outcome.combine, Nat.add_assoc]⟩
  | retained q cont ih =>
    cases h with
    | retained h =>
      obtain ⟨a, z, ha, hz, rfl⟩ := ih (b q) _ h
      exact ⟨a.add 1 0 1 (if b q then 1 else 0), z, .retained ha, hz, by
        simp [Outcome.add, Outcome.combine, Nat.add_assoc]⟩
  | uniform n cont ih =>
    cases h with
    | uniform u h =>
      obtain ⟨a, z, ha, hz, rfl⟩ := ih u _ h
      exact ⟨a.add 1 0 0 0, z, .uniform u ha, hz, by
        simp [Outcome.add, Outcome.combine, Nat.add_assoc]⟩
  | coin rate cont ih =>
    cases h with
    | coin u h =>
      obtain ⟨a, z, ha, hz, rfl⟩ := ih u _ h
      exact ⟨a.add 2 0 0 0, z, .coin u ha, hz, by
        simp [Outcome.add, Outcome.combine, Nat.add_assoc]⟩
  | tick n cont ih =>
    cases h with
    | tick h =>
      obtain ⟨a, z, ha, hz, rfl⟩ := ih _ h
      exact ⟨a.add (n + 1) 0 0 0, z, .tick ha, hz, by
        simp [Outcome.add, Outcome.combine, Nat.add_assoc]⟩

end SteinerUpperBound.Covers.OracleProgram.Mean
