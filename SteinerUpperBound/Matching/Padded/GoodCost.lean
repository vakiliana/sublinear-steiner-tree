module

public import SteinerUpperBound.Matching.Padded.OracleWork
public import SteinerUpperBound.Matching.Padded.TraceMoment
public import SteinerUpperBound.Matching.Padded.BucketExpectation

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E] (P : Parameters S)

theorem Execution.oracle_good_cost (A : Account S) (v : V) :
    (Execution.law S P v).expect (fun x => if Function.Injective x.2 then
      (Oracle.vertex S P v).cost (Command.oracleCharge A) 0 x.1 else 0) ≤
      A.rate * (P.rankExponent + P.sortHeight + 12 : ℕ) +
        requestWork S P A * (Execution.law S P v).expect (fun x =>
          if Function.Injective x.2 then Cache.requestValue S P.rankCard (fun _ => 1)
            ((Oracle.vertex S P v).output x.1).cache else 0) +
        32 * A.rate * (Execution.law S P v).expect (fun x =>
          if Function.Injective x.2 then agedTrace (-1) ((Oracle.vertex S P v).output x.1).calls else 0) := by
  have hp (x : Execution.Space S P v) :
      (if Function.Injective x.2 then (Oracle.vertex S P v).cost (Command.oracleCharge A) 0 x.1 else 0) ≤
        A.rate * (P.rankExponent + P.sortHeight + 12 : ℕ) +
          requestWork S P A * (if Function.Injective x.2 then
            Cache.requestValue S P.rankCard (fun _ => 1) ((Oracle.vertex S P v).output x.1).cache else 0) +
          32 * A.rate * (if Function.Injective x.2 then
            agedTrace (-1) ((Oracle.vertex S P v).output x.1).calls else 0) := by
    have h := Oracle.vertex_oracle_bound S P A v x.1
    unfold oraclePost at h
    by_cases hn : Function.Injective x.2
    · simp only [hn, ↓reduceIte]
      linarith
    · simp only [hn, ↓reduceIte, mul_zero, add_zero]
      exact mul_nonneg A.rate_nonneg (Nat.cast_nonneg _)
  have hh := (Execution.law S P v).expect_mono hp
  simpa only [Law.expect_add, Law.expect_const, Law.expect_const_mul] using hh

theorem Execution.oracle_good_expectation [Nonempty V] (A : Account S) (D : ℕ) :
    (Law.uniform V).expect (fun v => (Execution.law S P v).expect (fun x =>
      if Function.Injective x.2 then
        (Oracle.vertex S P v).cost (Command.oracleCharge A) 0 x.1 else 0)) ≤
      A.rate * (P.rankExponent + P.sortHeight + 12 : ℕ) +
        requestWork S P A * (1 + (4 * Fintype.card E : ℝ) * G.callBudget / Fintype.card V) +
        32 * A.rate *
          ((D + 1 : ℝ) * ((2 * Fintype.card E : ℝ) * G.callBudget / Fintype.card V) +
            ((Fintype.card E + 1 : ℝ) * (2 * Fintype.card E) * (2 * Fintype.card E + 1)) *
              (Rank.uniform (E := E)).prob {ρ | G.LongStack D ρ}) := by
  have hh := (Law.uniform V).expect_mono (fun v => Execution.oracle_good_cost S P A v)
  rw [Law.expect_add, Law.expect_add, Law.expect_const, Law.expect_const_mul, Law.expect_const_mul] at hh
  have hr : 0 ≤ requestWork S P A := by
    unfold requestWork
    exact mul_nonneg (mul_nonneg (by norm_num) A.rate_nonneg) (Nat.cast_nonneg _)
  exact hh.trans (add_le_add
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (expected_good_totalRequests S P) hr))
    (mul_le_mul_of_nonneg_left (expected_good_agedTrace S P D)
      (mul_nonneg (by norm_num) A.rate_nonneg)))

theorem Execution.good_cost_split (A : Account S) (v : V) :
    (Execution.law S P v).expect (fun x => if Function.Injective x.2 then
      (Oracle.vertex S P v).cost (Command.charge A) A.rate x.1 else 0) ≤
      (Oracle.vertex S P v).expectedCost (Command.bucketCharge A) A.rate +
        (Execution.law S P v).expect (fun x => if Function.Injective x.2 then
          (Oracle.vertex S P v).cost (Command.oracleCharge A) 0 x.1 else 0) := by
  have hp (x : Execution.Space S P v) :
      (if Function.Injective x.2 then
        (Oracle.vertex S P v).cost (Command.charge A) A.rate x.1 else 0) ≤
      (Oracle.vertex S P v).cost (Command.bucketCharge A) A.rate x.1 +
        if Function.Injective x.2 then (Oracle.vertex S P v).cost (Command.oracleCharge A) 0 x.1 else 0 := by
    by_cases hn : Function.Injective x.2
    · simp only [hn, ↓reduceIte, Command.split_cost, le_refl]
    · simp only [hn, ↓reduceIte, add_zero]
      exact Program.cost_nonneg _ _ _ (Command.bucketCharge_nonneg A) A.rate_nonneg _
  have hh := (Execution.law S P v).expect_mono hp
  rw [Law.expect_add] at hh
  have hcost := Program.completedLaw_cost (Oracle.vertex S P v)
    (fun r => Cache.completion S P.rankCard P.rankCard_pos r.cache) (Command.bucketCharge A) A.rate
  dsimp only [Execution.law] at hh
  rw [hcost] at hh
  exact hh

end SteinerUpperBound.Matching.Padded
