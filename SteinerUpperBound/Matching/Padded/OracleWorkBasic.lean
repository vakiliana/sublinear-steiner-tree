module

public import SteinerUpperBound.Matching.Padded.BucketProgram
public import SteinerUpperBound.Matching.Padded.KernelSupport
public import SteinerUpperBound.Matching.Padded.Ledger

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

namespace Program

variable {C A B : Type*}

theorem expectedCost_zero (p : Program C A) : p.expectedCost (fun _ => 0) 0 = 0 := by
  induction p with
  | ret a => simp
  | tick c p ih => simp only [expectedCost_tick, zero_add, ih]
  | draw n hn next ih => simp [expectedCost_draw, ih]

theorem cost_zero_of_expect (p : Program C A) (charge : C → ℝ) (rate : ℝ)
    (hc : ∀ c, 0 ≤ charge c) (hr : 0 ≤ rate) (h : p.expectedCost charge rate = 0)
    (leaf : p.Outcomes) : p.cost charge rate leaf = 0 := by
  have hsingle : p.mass leaf * p.cost charge rate leaf ≤ p.expectedCost charge rate :=
    Finset.single_le_sum (f := fun x => p.mass x * p.cost charge rate x)
      (fun x _ => mul_nonneg (p.mass_nonneg x) (p.cost_nonneg charge rate hc hr x)) (Finset.mem_univ _)
  rw [h] at hsingle
  have hle : p.cost charge rate leaf ≤ 0 := by
    by_contra hn
    exact (not_le_of_gt (mul_pos (p.mass_pos leaf) (lt_of_not_ge hn))) hsingle
  exact le_antisymm hle (p.cost_nonneg charge rate hc hr leaf)

theorem forEach_expectedCost_zero (step : B → A → Program C A) (xs : List B) (charge : C → ℝ)
    (rate : ℝ) (h : ∀ i ∈ xs, ∀ a, (step i a).expectedCost charge rate = 0) (a : A) :
    (forEach step xs a).expectedCost charge rate = 0 := by
  induction xs generalizing a with
  | nil => simp [forEach]
  | cons i xs ih =>
    rw [forEach, expectedCost_bind, h i (by simp) a]
    simp only [zero_add]
    have ht (a' : A) := ih (fun j hj => h j (by simp [hj])) a'
    simp_rw [ht]
    exact expect_const _ _

end Program

namespace Cache

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ) (hQ : 0 < Q)

theorem arithmetic_oracle_zero {A : Type*} (account : Account S) (p : Program ℕ A) :
    (Command.liftArithmetic (S := S) p).expectedCost (Command.oracleCharge account) 0 = 0 := by
  rw [Command.liftArithmetic, Program.expectedCost_relabel]
  exact Program.expectedCost_zero p

theorem selectedStep_oracle_zero (A : Account S) (a b : ℕ) (v : V) (i : ℕ) (s : Cache S Q) :
    (selectedStep S Q hQ a b v i s).expectedCost (Command.oracleCharge A) 0 = 0 := by
  unfold selectedStep
  split_ifs with hi
  · simp only [Command.testSlot, Program.bind, Program.expectedCost_tick, Command.oracleCharge, zero_add]
    cases ht : S.test ⟨v, ⟨i, hi⟩⟩ with
    | none => exact Program.expectedCost_ret _ _ _
    | some hit =>
      obtain ⟨e, reverse⟩ := hit
      simp only [Program.expectedCost_tick, Command.oracleCharge, zero_add]
      split_ifs
      · rw [Program.expectedCost_bind, arithmetic_oracle_zero]
        simp only [Program.expectedCost_ret, Program.expect_const, zero_add]
      · exact Program.expectedCost_ret _ _ _
  · exact Program.expectedCost_ret _ _ _

theorem collect_oracle_zero (A : Account S) (a b : ℕ) (v : V) (s : Cache S Q) :
    (collect S Q hQ a b v s).expectedCost (Command.oracleCharge A) 0 = 0 := by
  unfold collect
  dsimp only
  rw [Program.expectedCost_bind, arithmetic_oracle_zero]
  have hstep (i : ℕ) (xs : List (Entry S Q)) :
      (collectStep S Q hQ a b v s i xs).expectedCost (Command.oracleCharge A) 0 = 0 := by
    rw [collectStep, Program.expectedCost_bind, selectedStep_oracle_zero]
    simp only [Program.expectedCost_tick, Program.expectedCost_ret, Command.oracleCharge,
      Program.expect_const, zero_add]
  have ht (selected : List ℕ) :
      (Program.forEach (collectStep S Q hQ a b v s) selected []).expectedCost (Command.oracleCharge A) 0 = 0 :=
    Program.forEach_expectedCost_zero _ selected _ _ (fun i _ => hstep i) []
  simp_rw [ht]
  simp only [Program.expect_const, zero_add]

theorem extend_oracle_zero (A : Account S) (height : ℕ) (v : V) (s : Cache S Q) :
    (extend S Q hQ height v s).expectedCost (Command.oracleCharge A) 0 = 0 := by
  unfold extend
  dsimp only
  split_ifs
  · rw [Program.expectedCost_bind, collect_oracle_zero]
    simp only [Program.expectedCost_tick, Program.expectedCost_ret, Command.oracleCharge,
      Program.expect_const, zero_add]
  · exact Program.expectedCost_ret _ _ _

theorem extend_oracle_cost (A : Account S) (height : ℕ) (v : V) (s : Cache S Q)
    (leaf : (extend S Q hQ height v s).Outcomes) :
    (extend S Q hQ height v s).cost (Command.oracleCharge A) 0 leaf = 0 :=
  Program.cost_zero_of_expect _ _ _ (Command.oracleCharge_nonneg A) (le_refl _)
    (extend_oracle_zero S Q hQ A height v s) leaf

theorem nextLoop_oracle_bound (A : Account S) (height : ℕ) (v : V) (cursor fuel : ℕ) (s : Cache S Q) :
    (nextLoop S Q hQ height v cursor fuel s).Bound (Command.oracleCharge A) 0 (fun _ => 0)
      (6 * A.rate * fuel) := by
  have hrate := A.rate_nonneg
  induction fuel generalizing s with
  | zero => exact Program.bound_ret _ _ _ _ _ (by simp)
  | succ fuel ih =>
    rw [nextLoop]
    apply Program.bound_tick
    have he : 6 * A.rate * ((fuel + 1 : ℕ) : ℝ) - Command.oracleCharge A (.oracle 6) =
        6 * A.rate * fuel := by simp only [Command.oracleCharge, Nat.cast_add, Nat.cast_one]; ring
    rw [he]
    cases ha : available S Q v cursor s with
    | some x => exact Program.bound_ret _ _ _ _ _ (by positivity)
    | none =>
      split_ifs
      · apply Program.bound_bind _ _ _ _ (fun _ => 6 * A.rate * fuel) _ _
        · intro leaf
          rw [extend_oracle_cost]
          exact le_of_eq (zero_add _)
        · exact ih
      · exact Program.bound_ret _ _ _ _ _ (by positivity)

theorem next_oracle_bound (A : Account S) (height maxLevel : ℕ) (v : V) (cursor : ℕ) (s : Cache S Q) :
    (next S Q hQ height maxLevel v cursor s).Bound (Command.oracleCharge A) 0 (fun _ => 0)
      (6 * A.rate * (maxLevel + 1 : ℕ)) := by
  unfold next
  split_ifs
  · exact nextLoop_oracle_bound S Q hQ A height v cursor (maxLevel + 1) _
  · apply Program.bound_tick
    simpa only [Command.oracleCharge, sub_zero] using
      nextLoop_oracle_bound S Q hQ A height v cursor (maxLevel + 1)
        { s with requests := Function.update s.requests v (s.requests v + 1),
                 prepared := Function.update s.prepared v true }

variable [Fintype V] [Fintype E]

theorem next_requestValue_supported (P : Parameters S) (v : V) (cursor : ℕ) (s : Cache S P.rankCard) :
    (next S P.rankCard P.rankCard_pos P.sortHeight (P.rankExponent + 1) v cursor s).Supported
      (fun answer => requestValue S P.rankCard (fun _ => 1) answer.2 =
        requestValue S P.rankCard (fun _ => 1) s + 1) := by
  apply (Joint.next P.rankCard_pos P.sortHeight (P.rankExponent + 1) v cursor s).supported
  intro ranks _
  exact idealNext_requestValue S P.rankCard P.sortHeight (P.rankExponent + 1) (fun _ => 1)
    v cursor s ranks

end Cache

end SteinerUpperBound.Matching.Padded
