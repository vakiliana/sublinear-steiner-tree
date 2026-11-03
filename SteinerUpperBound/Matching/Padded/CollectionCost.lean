module

public import SteinerUpperBound.Matching.Padded.CacheFacts

@[expose] public section

/-!
# Exact expected cost of sparse bucket collection

This bound does not need a simultaneous concentration event for the slot coins.
Fresh sampling at each opened bucket gives its expected weighted slot cost
directly. The sampler's actual arithmetic is included.
-/

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

namespace Program

variable {C A S : Type*}

theorem forEach_cost_le (step : A → S → Program C S) (xs : List A) (c : A → ℝ)
    (charge : C → ℝ) (r : ℝ)
    (hc : ∀ a ∈ xs, ∀ s, (step a s).expectedCost charge r ≤ c a) (s : S) :
    (forEach step xs s).expectedCost charge r ≤ (xs.map c).sum := by
  induction xs generalizing s with
  | nil => simp [forEach]
  | cons a xs ih =>
    rw [forEach, expectedCost_bind]
    have ht (s' : S) : (forEach step xs s').expectedCost charge r ≤ (xs.map c).sum :=
      ih (fun b hb => hc b (by simp [hb])) s'
    have hh := (step a s).expect_mono ht
    rw [expect_const] at hh
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (hc a (by simp) s) hh

end Program

theorem sum_map_const_mul {A : Type*} (xs : List A) (c : A → ℝ) (r : ℝ) :
    (xs.map (fun x => r * c x)).sum = r * (xs.map c).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

namespace Cache

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ) (hQ : 0 < Q)

theorem slotCost_sum (A : Account S) (v : V) :
    (∑ i ∈ Finset.range (S.length v), slotCost S A v i) = A.W v := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [slotCost, i.isLt, ↓reduceDIte]

theorem rate_times_length_le (A : Account S) (v : V) :
    A.rate * S.length v ≤ A.W v := by
  calc
    _ = ∑ _i : Fin (S.length v), A.rate := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun i _ => A.rate_le_slot ⟨v, i⟩

theorem selected_processing_cost (A : Account S) (a b : ℕ) (v : V) (s : Cache S Q)
    (selected : List ℕ) (entries : List (Entry S Q)) :
    (Program.forEach (collectStep S Q hQ a b v s)
      selected entries).expectedCost (Command.charge A) A.rate ≤
        17 * (selected.map (slotCost S A v)).sum := by
  have hh := Program.forEach_cost_le
    (collectStep S Q hQ a b v s)
    selected (fun i => 17 * slotCost S A v i) (Command.charge A) A.rate
    (fun i _ xs => by
      rw [collectStep, Program.expectedCost_bind]
      simp only [Program.expectedCost_tick, Program.expectedCost_ret, Command.charge,
        Program.expect_const, add_zero]
      have hs := selectedStep_cost S Q hQ A a b v i s
      by_cases hi : i < S.length v
      · have hb := A.rate_le_slot (⟨v, ⟨i, hi⟩⟩ : Slot S.length)
        simp only [slotCost, hi, ↓reduceDIte] at hs ⊢
        norm_num only [Nat.cast_ofNat]
        nlinarith
      · simp only [slotCost, hi, ↓reduceDIte] at hs ⊢
        norm_num only [Nat.cast_ofNat]
        nlinarith [A.rate_nonneg]) entries
  simpa only [sum_map_const_mul] using hh

theorem collect_expectedCost (A : Account S) (a b : ℕ) (hab : a < b) (hbQ : b ≤ Q)
    (v : V) (s : Cache S Q) :
    (collect S Q hQ a b v s).expectedCost (Command.charge A) A.rate ≤
      (Sparse.operationBound (S.length v) + 17 : ℕ) *
        ((Range.probability Q a b : ℝ) * A.W v + A.Cstar) := by
  let p := Range.probability Q a b
  let n := S.length v
  let sampler := Sparse.sample (1 - p) n 0
  have hp := Range.probability_bounds Q a b hab hbQ
  have hr0 : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
  have hr1 : 1 - p ≤ 1 := by dsimp only [p]; linarith [hp.1]
  have hcount : sampler.expect (fun xs => (xs.length : ℝ)) = (p : ℝ) * n := by
    have hh := Sparse.weighted_count (1 - p) hr0 hr1 n 0 (fun _ => 1)
    simpa [sampler, Rat.cast_sub, Rat.cast_one] using hh
  have hweight : sampler.expect (fun xs => (xs.map (slotCost S A v)).sum) =
      (p : ℝ) * A.W v := by
    have hh := Sparse.weighted_count (1 - p) hr0 hr1 n 0 (slotCost S A v)
    simpa [sampler, n, Rat.cast_sub, Rat.cast_one, slotCost_sum S A v] using hh
  have hsample : A.rate * sampler.expectedCost (fun k : ℕ => (k : ℝ)) 1 ≤
      (Sparse.operationBound n : ℝ) * ((p : ℝ) * A.W v + A.Cstar) := by
    have hs := Sparse.expectedCost_le (1 - p) n 0
    change sampler.expectedCost (fun k : ℕ => (k : ℝ)) 1 ≤ _ at hs
    rw [hcount] at hs
    have hb := mul_le_mul_of_nonneg_left hs A.rate_nonneg
    have hw := rate_times_length_le S A v
    have hpR : (0 : ℝ) ≤ p := by exact_mod_cast hp.1
    have hwp := mul_le_mul_of_nonneg_left hw hpR
    have hbr := mul_le_mul_of_nonneg_left
      (add_le_add hwp A.rate_le_Cstar) (Nat.cast_nonneg (Sparse.operationBound n) : (0 : ℝ) ≤ _)
    nlinarith
  have hprocess :
      (Command.liftArithmetic (S := S) sampler).expect (fun selected =>
        (Program.forEach (collectStep S Q hQ a b v s)
          selected []).expectedCost (Command.charge A) A.rate) ≤
        17 * (p : ℝ) * A.W v := by
    calc
      _ ≤ (Command.liftArithmetic (S := S) sampler).expect
          (fun selected => 17 * (selected.map (slotCost S A v)).sum) :=
        Program.expect_mono _ (fun selected => selected_processing_cost S Q hQ A a b v s selected [])
      _ = 17 * (p : ℝ) * A.W v := by
        rw [Command.expect_arithmetic, Program.expect_const_mul, hweight]
        ring
  unfold collect
  dsimp only
  rw [Program.expectedCost_bind, Command.cost_arithmetic]
  change A.rate * sampler.expectedCost (fun k : ℕ => (k : ℝ)) 1 + _ ≤ _
  have hn : (0 : ℝ) ≤ (p : ℝ) * A.W v :=
    mul_nonneg (by exact_mod_cast hp.1) (A.W_nonneg v)
  apply (add_le_add hsample hprocess).trans
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  nlinarith [A.Cstar_nonneg]

end Cache

end SteinerUpperBound.Matching.Padded
