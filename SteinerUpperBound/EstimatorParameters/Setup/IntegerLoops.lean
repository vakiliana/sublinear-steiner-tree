module

public import SteinerUpperBound.EstimatorParameters.Configuration
public import SteinerUpperBound.QueryProgram

@[expose] public section

namespace SteinerUpperBound.EstimatorParameters.Setup

open QueryProgram

variable {M Q : Type*}

/-- Compare, divide by two, and branch are charged before each recursive call. -/
def logCode (n : ℕ) : Code M Q ℕ :=
  .tick 3 (if n < 2 then .pure 0 else
    (logCode (n / 2)).bind (fun j => .tick 1 (.pure (j + 1))))
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem logCode_evaluates (m : M → ℝ) (bits : Q → Bool) (n : ℕ) :
    Code.Evaluates m bits (logCode n) ⟨Nat.log2 n, 6 * Nat.log2 n + 4, 0, 0, 0⟩ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F
    by_cases hn : n < 2
    · have hlog : Nat.log2 n = 0 := by
        rw [Nat.log2_eq_log_two]
        exact Nat.log_of_lt hn
      rw [logCode, if_pos hn]
      simp [Code.evaluate, Outcome.add, Outcome.pure, hlog]
    · have hsmall : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
      have hlog : Nat.log2 n = Nat.log2 (n / 2) + 1 := by
        simp only [Nat.log2_eq_log_two]
        exact Nat.log_of_one_lt_of_le (by decide) (by omega)
      rw [logCode, if_neg hn]
      simp only [Code.evaluate, Code.evaluate_bind]
      rw [ih (n / 2) hsmall]
      simp only [Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure, hlog]
      congr 2 <;> omega

def sqrtValue : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
      if n < 4 then if n = 0 then 0 else 1
      else
        let s := sqrtValue fuel (n / 4)
        if (2 * s + 1) * (2 * s + 1) ≤ n then 2 * s + 1 else 2 * s

def sqrtWork : ℕ → ℕ → ℕ
  | 0, _ => 2
  | fuel + 1, n => if n < 4 then 7 else 11 + sqrtWork fuel (n / 4)

/-- The two-bit square-root recurrence executes integer division, multiplication,
and the square test; the recursive result is not supplied as a primitive. -/
def sqrtLoop : ℕ → ℕ → Code M Q ℕ
  | 0, _ => .tick 1 (.pure 0)
  | fuel + 1, n => .tick 3 (if n < 4 then .tick 2 (.pure (if n = 0 then 0 else 1))
      else (sqrtLoop fuel (n / 4)).bind (fun s =>
        .tick 6 (.pure (if (2 * s + 1) * (2 * s + 1) ≤ n then 2 * s + 1 else 2 * s))))

theorem sqrtLoop_evaluates (m : M → ℝ) (bits : Q → Bool) (fuel n : ℕ) :
    Code.Evaluates m bits (sqrtLoop fuel n) ⟨sqrtValue fuel n, sqrtWork fuel n, 0, 0, 0⟩ := by
  induction fuel generalizing n with
  | zero => intro F; rfl
  | succ fuel ih =>
    intro F
    by_cases hn : n < 4
    · simp [sqrtLoop, sqrtValue, sqrtWork, hn, Code.evaluate, Outcome.add, Outcome.pure]
    · simp only [sqrtLoop, sqrtValue, sqrtWork, hn, ite_false, Code.evaluate, Code.evaluate_bind]
      rw [ih]
      simp only [Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure]
      congr 2 <;> omega

theorem sqrtWork_bound (fuel n : ℕ) : sqrtWork fuel n ≤ 11 * fuel + 7 := by
  induction fuel generalizing n with
  | zero => simp [sqrtWork]
  | succ fuel ih =>
    have h := ih (n / 4)
    simp only [sqrtWork]
    split_ifs <;> omega

theorem sqrtValue_correct (fuel n : ℕ) (hn : n < 2 ^ fuel) : sqrtValue fuel n = Nat.sqrt n := by
  induction fuel generalizing n with
  | zero =>
    have he : n = 0 := by simpa using hn
    simp [he, sqrtValue]
  | succ fuel ih =>
    by_cases hsmall : n < 4
    · interval_cases n <;> norm_num [sqrtValue]
    · have hp : n / 4 < 2 ^ fuel := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mpr
        rw [pow_succ] at hn
        nlinarith [Nat.zero_le (2 ^ fuel)]
      have hrec := ih (n / 4) hp
      rw [sqrtValue, if_neg hsmall, hrec]
      let s := Nat.sqrt (n / 4)
      have hs : s * s ≤ n / 4 := Nat.sqrt_le _
      have hs' : n / 4 < (s + 1) * (s + 1) := Nat.lt_succ_sqrt _
      have hdiv := Nat.mul_div_le n 4
      have hlower : (2 * s) * (2 * s) ≤ n := by nlinarith
      have hupper : n < (2 * s + 2) * (2 * s + 2) := by
        have h := (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mp hs'
        nlinarith
      change (if (2 * s + 1) * (2 * s + 1) ≤ n then 2 * s + 1 else 2 * s) = Nat.sqrt n
      split_ifs with htest
      · apply Nat.eq_sqrt.mpr
        constructor <;> nlinarith
      · apply Nat.eq_sqrt.mpr
        constructor <;> nlinarith

def integerSqrt (n : ℕ) : Code M Q ℕ :=
  (logCode n).bind (fun j => .tick 1 (sqrtLoop (j + 1) n))

def integerSqrtWork (n : ℕ) : ℕ :=
  6 * Nat.log2 n + 4 + 2 + sqrtWork (Nat.log2 n + 1) n

theorem integerSqrt_evaluates (m : M → ℝ) (bits : Q → Bool) (n : ℕ) :
    Code.Evaluates m bits (integerSqrt n) ⟨Nat.sqrt n, integerSqrtWork n, 0, 0, 0⟩ := by
  intro F
  rw [integerSqrt, Code.evaluate_bind, logCode_evaluates]
  simp only [Code.evaluate]
  rw [sqrtLoop_evaluates]
  have hv := sqrtValue_correct (Nat.log2 n + 1) n Nat.lt_log2_self
  simp only [hv, Outcome.add, Outcome.combine, integerSqrtWork]
  congr 2 <;> omega

theorem integerSqrtWork_bound (n : ℕ) : integerSqrtWork n ≤ 17 * Nat.log2 n + 24 := by
  have h := sqrtWork_bound (Nat.log2 n + 1) n
  unfold integerSqrtWork
  omega

end SteinerUpperBound.EstimatorParameters.Setup
