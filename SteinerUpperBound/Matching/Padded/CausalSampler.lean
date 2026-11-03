module

public import SteinerUpperBound.Matching.Padded.Sparse
public import SteinerUpperBound.QueryProgram.Loops

@[expose] public section

/-!
# Causal QueryProgram realization of the arithmetic samplers

The compiler emits actual uniform-integer instructions. `spend k` charges
exactly `k` work units despite `QueryProgram.Code.tick n` charging `n + 1`.
No metric or retained query is introduced by this compiler.
-/

namespace SteinerUpperBound.Matching.Padded.Causal

open SteinerLowerBound
open scoped Classical BigOperators

abbrev Code := SteinerUpperBound.QueryProgram.Code
abbrev Outcome := SteinerUpperBound.QueryProgram.Outcome

variable {M T A : Type*}

def spend : ℕ → Code M T A → Code M T A
  | 0, p => p
  | n + 1, p => .tick n p

noncomputable def expect (m : M → ℝ) (b : T → Bool) (p : Code M T A) (f : A → ℝ) : ℝ :=
  p.evaluate m b (fun o => f o.value)

theorem expect_bind {B : Type*} (m : M → ℝ) (b : T → Bool) (p : Code M T A)
    (k : A → Code M T B) (f : B → ℝ) :
    expect m b (p.bind k) f = expect m b p (fun a => expect m b (k a) f) := by
  rw [expect, SteinerUpperBound.QueryProgram.Code.evaluate_bind]
  rfl

@[simp] theorem expect_pure (m : M → ℝ) (b : T → Bool) (a : A) (f : A → ℝ) :
    expect m b (.pure a) f = f a := rfl

theorem evaluate_spend (m : M → ℝ) (b : T → Bool) (n : ℕ) (p : Code M T A)
    (F : Outcome A → ℝ) :
    (spend n p).evaluate m b F = p.evaluate m b (fun o => F (o.add n 0 0 0)) := by
  cases n with
  | zero => simp [spend, SteinerUpperBound.QueryProgram.Outcome.add]
  | succ n => rfl

@[simp] theorem expect_spend (m : M → ℝ) (b : T → Bool) (n : ℕ) (p : Code M T A)
    (f : A → ℝ) : expect m b (spend n p) f = expect m b p f := by
  rw [expect, evaluate_spend]
  rfl

def compile : Program ℕ A → Code M T A
  | .ret a => .pure a
  | .tick n p => spend n (compile p)
  | .draw 0 hn _ => (Nat.not_lt_zero 0 hn).elim
  | .draw (n + 1) _ next => .uniform n (fun i => compile (next i))

theorem value_law (m : M → ℝ) (b : T → Bool) (p : Program ℕ A) (f : A → ℝ) :
    expect m b (compile p) f = p.expect f := by
  induction p with
  | ret a => simp [compile]
  | tick n p ih => simpa only [compile, expect_spend, Program.expect_tick] using ih
  | draw n hn next ih =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [compile, expect, SteinerUpperBound.QueryProgram.Code.evaluate]
      rw [Program.expect_draw]
      change (∑ i : Fin (n + 1), ((Fintype.card (Fin (n + 1)) : ℝ)⁻¹) *
        expect m b (compile (next i)) f) = _
      simp only [Fintype.card_fin]
      apply Finset.sum_congr rfl
      intro i _
      rw [ih i]

theorem work_spend (m : M → ℝ) (b : T → Bool) (n : ℕ) (p : Code M T A) :
    (spend n p).evaluate m b (fun o => (o.work : ℝ)) =
      n + p.evaluate m b (fun o => (o.work : ℝ)) := by
  rw [evaluate_spend]
  simp only [SteinerUpperBound.QueryProgram.Outcome.add, Nat.cast_add]
  rw [SteinerUpperBound.QueryProgram.Code.evaluate_add,
    SteinerUpperBound.QueryProgram.Code.evaluate_const]

theorem work_law (m : M → ℝ) (b : T → Bool) (p : Program ℕ A) :
    (compile p).evaluate m b (fun o => (o.work : ℝ)) =
      p.expectedCost (fun n : ℕ => (n : ℝ)) 1 := by
  induction p with
  | ret a => simp [compile, SteinerUpperBound.QueryProgram.Code.evaluate,
      SteinerUpperBound.QueryProgram.Outcome.pure]
  | tick n p ih =>
    rw [compile, work_spend, Program.expectedCost_tick, ih]
  | draw n hn next ih =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [compile, SteinerUpperBound.QueryProgram.Code.evaluate,
        SteinerUpperBound.QueryProgram.Outcome.add, Nat.cast_add, Nat.cast_one]
      simp_rw [SteinerUpperBound.QueryProgram.Code.evaluate_add,
        SteinerUpperBound.QueryProgram.Code.evaluate_const, ih]
      rw [Program.expectedCost_draw, Law.expect_add, Law.expect_const]
      simp [Law.expect, Law.uniform]

theorem metric_queries_zero (m : M → ℝ) (b : T → Bool) (p : Program ℕ A) :
    (compile p).evaluate m b (fun o => (o.metricQueries : ℝ)) = 0 := by
  induction p with
  | ret a => simp [compile, SteinerUpperBound.QueryProgram.Code.evaluate,
      SteinerUpperBound.QueryProgram.Outcome.pure]
  | tick n p ih =>
    rw [compile, evaluate_spend]
    simpa only [SteinerUpperBound.QueryProgram.Outcome.add, Nat.zero_add] using ih
  | draw n hn next ih =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [compile, SteinerUpperBound.QueryProgram.Code.evaluate,
        SteinerUpperBound.QueryProgram.Outcome.add, Nat.zero_add]
      simp_rw [ih]
      exact Law.expect_const _ _

theorem geometric_work (m : M → ℝ) (b : T → Bool) (r : ℚ) (n : ℕ) :
    (compile (Geometric.sample r n)).evaluate m b (fun o => (o.work : ℝ)) ≤
      Geometric.operationBound n := by
  rw [work_law]
  have hh := Program.expected_bound _ _ _ (fun _ => 0) _ (Geometric.sample_cost_bound r n)
  simpa only [Program.expect_const, add_zero] using hh

theorem sparse_work (m : M → ℝ) (b : T → Bool) (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (n start : ℕ) :
    (compile (Sparse.sample r n start)).evaluate m b (fun o => (o.work : ℝ)) ≤
      (Sparse.operationBound n : ℝ) * ((1 - (r : ℝ)) * n + 1) := by
  rw [work_law]
  have hh := Sparse.expectedCost_le r n start
  have hc := Sparse.weighted_count r h0 h1 n start (fun _ => 1)
  have hcount : (Sparse.sample r n start).expect (fun xs => (xs.length : ℝ)) =
      (1 - (r : ℝ)) * n := by simpa using hc
  rw [hcount] at hh
  exact hh

end SteinerUpperBound.Matching.Padded.Causal
