module

public import SteinerUpperBound.Matching.Padded.SortingCredit

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

namespace Program

variable {C A : Type*}

theorem Supported.mono {p : Program C A} {P Q : A → Prop} (hp : p.Supported P)
    (h : ∀ a, P a → Q a) : p.Supported Q := fun leaf => h _ (hp leaf)

theorem expect_le_of_supported (p : Program C A) (f : A → ℝ) (b : ℝ)
    (h : p.Supported (fun a => f a ≤ b)) : p.expect f ≤ b := by
  have hh := p.law.expect_mono h
  simpa only [Law.expect_const, Program.expect] using hh

end Program

namespace Command

variable {V E : Type*} {G : Graph V E} {S : Slots G}

theorem bucketCharge_le (A : Account S) (c : Command S) : bucketCharge A c ≤ charge A c := by
  cases c <;> simp only [bucketCharge]
  · exact le_refl _
  · exact charge_nonneg A _
  · exact le_refl _
  · exact le_refl _

end Command

namespace Cache

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ) (hQ : 0 < Q)

theorem collectStep_length (a b : ℕ) (v : V) (s : Cache S Q)
    (i : ℕ) (xs : List (Entry S Q)) :
    (collectStep S Q hQ a b v s i xs).Supported (fun ys => ys.length ≤ xs.length + 1) := by
  unfold collectStep
  refine Program.supported_bind _ _ (fun _ => True) _ (fun _ => trivial) ?_
  intro hit _
  apply Program.supported_tick
  apply Program.supported_ret
  cases hit <;> simp [addEntry]

theorem selected_collection_length (a b : ℕ) (v : V) (s : Cache S Q)
    (selected : List ℕ) (xs : List (Entry S Q)) :
    (Program.forEach (collectStep S Q hQ a b v s) selected xs).Supported
      (fun ys => ys.length ≤ xs.length + selected.length) := by
  induction selected generalizing xs with
  | nil => exact Program.supported_ret _ _ (by simp)
  | cons i selected ih =>
    rw [Program.forEach]
    refine Program.supported_bind _ _ _ _ (collectStep_length S Q hQ a b v s i xs) ?_
    intro ys hy
    exact (ih ys).mono (fun zs hz => by simp only [List.length_cons]; omega)

theorem collect_expectedLength (a b : ℕ) (hab : a < b) (hbQ : b ≤ Q) (v : V) (s : Cache S Q) :
    (collect S Q hQ a b v s).expect (fun xs => (xs.length : ℝ)) ≤
      (Range.probability Q a b : ℝ) * S.length v := by
  let p := Range.probability Q a b
  have hp := Range.probability_bounds Q a b hab hbQ
  have hr0 : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
  have hr1 : 1 - p ≤ 1 := by dsimp only [p]; linarith [hp.1]
  unfold collect
  dsimp only
  rw [Program.expect_bind]
  calc
    _ ≤ (Command.liftArithmetic (S := S) (Sparse.sample (1 - p) (S.length v) 0)).expect
        (fun selected => (selected.length : ℝ)) := by
      apply Program.expect_mono
      intro selected
      apply Program.expect_le_of_supported
      exact (selected_collection_length S Q hQ a b v s selected []).mono
        (fun ys hy => by exact_mod_cast (by simpa using hy : ys.length ≤ selected.length))
    _ = _ := by
      rw [Command.expect_arithmetic]
      have hh := Sparse.weighted_count (1 - p) hr0 hr1 (S.length v) 0 (fun _ => 1)
      simpa [p, Rat.cast_sub, Rat.cast_one] using hh

theorem collect_rateLength (A : Account S) (a b : ℕ) (hab : a < b) (hbQ : b ≤ Q)
    (v : V) (s : Cache S Q) :
    A.rate * (collect S Q hQ a b v s).expect (fun xs => (xs.length : ℝ)) ≤
      (Range.probability Q a b : ℝ) * A.W v := by
  have hl := mul_le_mul_of_nonneg_left (collect_expectedLength S Q hQ a b hab hbQ v s) A.rate_nonneg
  have hw := rate_times_length_le S A v
  have hp : (0 : ℝ) ≤ (Range.probability Q a b : ℝ) :=
    by exact_mod_cast (Range.probability_bounds Q a b hab hbQ).1
  have hwp := mul_le_mul_of_nonneg_left hw hp
  nlinarith

def extensionCoefficient (H height n : ℕ) : ℕ :=
  Sparse.operationBound n + 17 + (32 + 2 * H * sortScale height) + (sortScale height + 4)

variable [Fintype V]

theorem extend_amortized (A : Account S) (H height : ℕ) (v : V) (s : Cache S Q)
    (hb : Buckets.bound (s.level v + 1) ≤ Q) :
    (extend S Q hQ height v s).expectedCost (Command.bucketCharge A) A.rate +
        (extend S Q hQ height v s).expect (credit S Q A H height) ≤
      credit S Q A H height s + (extensionCoefficient H height (S.length v) : ℝ) *
        ((Range.probability Q (boundary S Q s v) (Buckets.bound (s.level v + 1)) : ℝ) * A.W v + A.Cstar) := by
  let a := boundary S Q s v
  let b := Buckets.bound (s.level v + 1)
  let p := Range.probability Q a b
  let K := Sparse.operationBound (S.length v) + 17
  let C := 32 + 2 * H * sortScale height
  let D := sortScale height + 4
  have hab : a < b := Buckets.bound_strictMono (Nat.lt_succ_self _)
  have hc : (collect S Q hQ a b v s).expectedCost (Command.bucketCharge A) A.rate ≤
      (K : ℝ) * ((p : ℝ) * A.W v + A.Cstar) :=
    (Program.expectedCost_mono _ _ _ _ _ (Command.bucketCharge_le A) (le_refl _)).trans
      (collect_expectedCost S Q hQ A a b hab hb v s)
  have hl := collect_rateLength S Q hQ A a b hab hb v s
  have hp : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Range.probability_bounds Q a b hab hb).1
  have hv := collect_valid S Q hQ a b v s
  have hfinish :
      (collect S Q hQ a b v s).expect (fun xs =>
        A.rate * (finish S Q height v s xs).operations +
          credit S Q A H height (finish S Q height v s xs).value) ≤
        credit S Q A H height s +
          (C : ℝ) * (A.rate * (collect S Q hQ a b v s).expect (fun xs => (xs.length : ℝ))) +
          A.rate * D := by
    have hh := (collect S Q hQ a b v s).law.expect_mono
      (fun leaf => finish_amortized S Q A H height v s _ (hv leaf))
    change (collect S Q hQ a b v s).expect (fun xs =>
      A.rate * (finish S Q height v s xs).operations +
        credit S Q A H height (finish S Q height v s xs).value) ≤
      (collect S Q hQ a b v s).expect (fun xs =>
        credit S Q A H height s +
          A.rate * ((32 + 2 * H * sortScale height : ℕ) * (xs.length : ℝ) + sortScale height + 4)) at hh
    simp only [Program.expect_add, Program.expect_const, Program.expect_const_mul] at hh ⊢
    convert hh using 1 <;>
      (try simp only [C, D, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]) <;> ring
  have hcl := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg C : (0 : ℝ) ≤ _)
  have hdl := mul_le_mul_of_nonneg_right A.rate_le_Cstar (Nat.cast_nonneg D : (0 : ℝ) ≤ _)
  unfold extend
  simp only [hb, ↓reduceIte, Program.expectedCost_bind, Program.expectedCost_tick,
    Program.expectedCost_ret, Program.expect_bind, Program.expect_tick, Program.expect_ret,
    Command.bucketCharge, Command.charge, add_zero]
  rw [add_assoc, ← Program.expect_add]
  change (collect S Q hQ a b v s).expectedCost (Command.bucketCharge A) A.rate + _ ≤ _
  have hw : (0 : ℝ) ≤ (p : ℝ) * A.W v := mul_nonneg hp (A.W_nonneg v)
  have hCC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hDD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hco : (extensionCoefficient H height (S.length v) : ℝ) = (K : ℝ) + C + D := by
    dsimp only [extensionCoefficient, K, C, D]
    push_cast
    ring
  rw [hco]
  nlinarith [mul_nonneg hCC A.Cstar_nonneg, mul_nonneg hDD hw]

end Cache

end SteinerUpperBound.Matching.Padded
