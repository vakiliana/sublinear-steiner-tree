module

public import SteinerUpperBound.Matching.Padded.Commands

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Buckets

open scoped Classical BigOperators

def bound (i : ℕ) : ℕ := if i = 0 then 0 else 2 ^ (i - 1)

@[simp] theorem bound_zero : bound 0 = 0 := by simp [bound]
@[simp] theorem bound_succ (i : ℕ) : bound (i + 1) = 2 ^ i := by simp [bound]

theorem bound_strictMono : StrictMono bound := by
  apply strictMono_nat_of_lt_succ
  intro i
  cases i with
  | zero => simp
  | succ i =>
    simp only [bound_succ, pow_succ]
    have hp : 0 < 2 ^ i := pow_pos (by decide) _
    omega

theorem bound_mono : Monotone bound := bound_strictMono.monotone

theorem adjacent (i j : ℕ) : bound j ≤ bound i ∨ bound (i + 1) ≤ bound j := by
  rcases le_or_gt j i with h | h
  · exact Or.inl (bound_mono h)
  · exact Or.inr (bound_mono h)

theorem double_lower (i : ℕ) : 2 * bound i ≤ bound (i + 1) := by
  cases i with
  | zero => simp
  | succ i => simp [pow_succ, Nat.mul_comm]

theorem probability_le_increment (Q i : ℕ) (hQ : bound (i + 1) ≤ Q) :
    (Range.probability Q (bound i) (bound (i + 1)) : ℝ) ≤
      2 * ((bound (i + 1) - bound i : ℕ) : ℝ) / (Q : ℝ) := by
  have hab := bound_strictMono (Nat.lt_succ_self i)
  have haQ : bound i < Q := hab.trans_le hQ
  have hpQ : (0 : ℝ) < Q := by exact_mod_cast Nat.zero_lt_of_lt haQ
  have hden : (0 : ℝ) < (Q - bound i : ℕ) := by exact_mod_cast (by omega : 0 < Q - bound i)
  have htwice : 2 * bound i ≤ Q := (double_lower i).trans hQ
  have htwiceR : (2 : ℝ) * bound i ≤ Q := by exact_mod_cast htwice
  have hsub : ((Q - bound i : ℕ) : ℝ) = Q - (bound i : ℝ) := by
    rw [Nat.cast_sub haQ.le]
  simp only [Range.probability, Rat.cast_div, Rat.cast_natCast]
  rw [div_le_div_iff₀ hden hpQ, hsub]
  have hinc : (0 : ℝ) ≤ (bound (i + 1) - bound i : ℕ) := Nat.cast_nonneg _
  nlinarith

end SteinerUpperBound.Matching.Padded.Buckets
