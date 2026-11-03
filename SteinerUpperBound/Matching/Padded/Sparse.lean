module

public import SteinerUpperBound.Matching.Padded.Geometric

@[expose] public section

/-!
# Sparse Bernoulli index generation

`sample` jumps directly from one successful index to the next using the
implemented geometric sampler. `dense` is a reference law, not the access
implementation, and performs no slot tests.
-/

namespace SteinerUpperBound.Matching.Padded.Sparse

open SteinerLowerBound
open scoped Classical BigOperators

def successMass (r : ℚ) (k : ℕ) : ℝ := ((r ^ k * (1 - r) : ℚ) : ℝ)

@[simp] theorem successMass_zero (r : ℚ) : successMass r 0 = 1 - (r : ℝ) := by
  simp [successMass]

@[simp] theorem successMass_succ (r : ℚ) (k : ℕ) :
    successMass r (k + 1) = (r : ℝ) * successMass r k := by
  simp only [successMass, pow_succ, Rat.cast_mul]
  ring

def dense (r : ℚ) : ℕ → ℕ → Program ℕ (List ℕ)
  | 0, _ => .ret []
  | n + 1, start =>
    (IntegerCoin.sample (1 - r)).bind fun b =>
      (dense r n (start + 1)).bind fun xs =>
        .ret (match b with | true => start :: xs | false => xs)

theorem expect_dense_succ (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (n start : ℕ)
    (f : List ℕ → ℝ) :
    (dense r (n + 1) start).expect f =
      (1 - (r : ℝ)) * (dense r n (start + 1)).expect (fun xs => f (start :: xs)) +
        (r : ℝ) * (dense r n (start + 1)).expect f := by
  have hp0 : 0 ≤ 1 - r := sub_nonneg.mpr h1
  have hp1 : 1 - r ≤ 1 := by linarith
  rw [dense, Program.expect_bind, IntegerCoin.expect_sample _ hp0 hp1]
  simp only [Program.expect_bind, Program.expect_ret, Rat.cast_sub, Rat.cast_one]
  ring

theorem dense_first_success (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (n start : ℕ)
    (f : List ℕ → ℝ) :
    (dense r n start).expect f =
      (∑ k ∈ Finset.range n, successMass r k *
        (dense r (n - k - 1) (start + k + 1)).expect (fun xs => f ((start + k) :: xs))) +
          ((r ^ n : ℚ) : ℝ) * f [] := by
  induction n generalizing start f with
  | zero => simp [dense]
  | succ n ih =>
    rw [expect_dense_succ r h0 h1 n start f, ih (start + 1) f]
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.add_zero, successMass_zero]
    have hsum :
        (∑ k ∈ Finset.range n, successMass r (k + 1) *
          (dense r (n + 1 - (k + 1) - 1) (start + (k + 1) + 1)).expect
            (fun xs => f ((start + (k + 1)) :: xs))) =
        (r : ℝ) * ∑ k ∈ Finset.range n, successMass r k *
          (dense r (n - k - 1) (start + 1 + k + 1)).expect
            (fun xs => f ((start + 1 + k) :: xs)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hi : n + 1 - (k + 1) - 1 = n - k - 1 := by omega
      have hs : start + (k + 1) = start + 1 + k := by omega
      rw [hi, hs, successMass_succ]
      ring
    rw [hsum]
    simp only [pow_succ, Rat.cast_mul]
    ring

def sample (r : ℚ) (n start : ℕ) : Program ℕ (List ℕ) :=
  if _hn : n = 0 then .ret [] else
    .tick 5 ((Geometric.sample r n).bind fun k =>
      if _hk : k < n then
        (sample r (n - k - 1) (start + k + 1)).bind fun xs =>
          .tick 2 (.ret ((start + k) :: xs))
      else .ret [])
termination_by n
decreasing_by omega

theorem expect_sample (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (n start : ℕ)
    (f : List ℕ → ℝ) :
    (sample r n start).expect f = (dense r n start).expect f := by
  induction n using Nat.strong_induction_on generalizing start f with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp [sample, dense]
    · rw [sample]
      simp only [hn, ↓reduceDIte, Program.expect_tick, Program.expect_bind]
      rw [Geometric.expect_sample r h0 h1 n]
      have hsum :
          (∑ k ∈ Finset.range n, ((r ^ k * (1 - r) : ℚ) : ℝ) *
            (if hk : k < n then
              ((sample r (n - k - 1) (start + k + 1)).bind fun xs =>
                .tick 2 (.ret ((start + k) :: xs))) else .ret []).expect f) =
          ∑ k ∈ Finset.range n, successMass r k *
            (dense r (n - k - 1) (start + k + 1)).expect
              (fun xs => f ((start + k) :: xs)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn := Finset.mem_range.mp hk
        simp only [hkn, ↓reduceDIte, Program.expect_bind, Program.expect_tick,
          Program.expect_ret]
        rw [ih (n - k - 1) (by omega) (start + k + 1) (fun xs => f ((start + k) :: xs))]
        rfl
      rw [hsum]
      simp only [lt_self_iff_false, ↓reduceDIte, Program.expect_ret]
      exact (dense_first_success r h0 h1 n start f).symm

theorem dense_weighted_count (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (n start : ℕ)
    (c : ℕ → ℝ) :
    (dense r n start).expect (fun xs => (xs.map c).sum) =
      (1 - (r : ℝ)) * ∑ k ∈ Finset.range n, c (start + k) := by
  induction n generalizing start with
  | zero => simp [dense]
  | succ n ih =>
    rw [expect_dense_succ r h0 h1]
    have heq : (fun xs : List ℕ => ((start :: xs).map c).sum) =
        fun xs => c start + (xs.map c).sum := by funext xs; rfl
    rw [heq, Program.expect_add, Program.expect_const, ih]
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have hs : (∑ k ∈ Finset.range n, c (start + (k + 1))) =
        ∑ k ∈ Finset.range n, c (start + 1 + k) := by
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      omega
    rw [hs]
    ring

/-- In particular, expected selected slot cost is exactly the Bernoulli rate times `W`. -/
theorem weighted_count (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (n start : ℕ)
    (c : ℕ → ℝ) :
    (sample r n start).expect (fun xs => (xs.map c).sum) =
      (1 - (r : ℝ)) * ∑ k ∈ Finset.range n, c (start + k) := by
  rw [expect_sample r h0 h1, dense_weighted_count r h0 h1]

def Valid (start n : ℕ) (xs : List ℕ) : Prop :=
  xs.Pairwise (· < ·) ∧ ∀ i ∈ xs, start ≤ i ∧ i < start + n

theorem sample_supported (r : ℚ) (n start : ℕ) :
    (sample r n start).Supported (Valid start n) := by
  induction n using Nat.strong_induction_on generalizing start with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp only [sample, ↓reduceDIte]
      exact Program.supported_ret _ _ ⟨by simp, by simp⟩
    · rw [sample]
      simp only [hn, ↓reduceDIte]
      apply Program.supported_tick
      refine Program.supported_bind (Geometric.sample r n) _
        (fun k => k ≤ n) (Valid start n) (Geometric.sample_supported r n) ?_
      intro k _
      split_ifs with hk
      · refine Program.supported_bind
          (sample r (n - k - 1) (start + k + 1)) _
          (Valid (start + k + 1) (n - k - 1)) (Valid start n)
          (ih (n - k - 1) (by omega) (start + k + 1)) ?_
        intro xs hxs
        apply Program.supported_tick
        apply Program.supported_ret
        refine ⟨List.pairwise_cons.mpr ⟨?_, hxs.1⟩, ?_⟩
        · intro i hi
          have hh := (hxs.2 i hi).1
          omega
        · intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact ⟨by omega, by omega⟩
          · have hh := hxs.2 i hi
            exact ⟨by omega, by omega⟩
      · exact Program.supported_ret _ _ ⟨by simp, by simp⟩

theorem operationBound_mono {n N : ℕ} (h : n ≤ N) :
    Geometric.operationBound n ≤ Geometric.operationBound N := by
  have hl : Geometric.height n ≤ Geometric.height N :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right h 1)) 1
  unfold Geometric.operationBound
  exact Nat.mul_le_mul_left 128 (pow_le_pow_left₀ (Nat.zero_le _)
    (Nat.add_le_add_right hl 1) 2)

def operationBound (N : ℕ) : ℕ := Geometric.operationBound N + 8

/-- Every execution pays logarithmic-squared overhead per selected index plus one. -/
theorem sample_cost_bound (r : ℚ) (n start N : ℕ) (hnN : n ≤ N) :
    (sample r n start).Bound (fun k : ℕ => (k : ℝ)) 1
      (fun xs => -(operationBound N : ℝ) * ((xs.length : ℝ) + 1)) 0 := by
  induction n using Nat.strong_induction_on generalizing start with
  | h n ih =>
    let K : ℝ := operationBound N
    let G : ℝ := Geometric.operationBound N
    have hKG : K = G + 8 := by simp only [K, G, operationBound, Nat.cast_add, Nat.cast_ofNat]
    have hG : 0 ≤ G := Nat.cast_nonneg _
    have hK : 0 ≤ K := Nat.cast_nonneg _
    by_cases hn : n = 0
    · subst n
      simp only [sample, ↓reduceDIte]
      apply Program.bound_ret
      simp only [List.length_nil, Nat.cast_zero, zero_add]
      linarith
    · rw [sample]
      simp only [hn, ↓reduceDIte]
      have hgeo : (Geometric.sample r n).Bound (fun k : ℕ => (k : ℝ)) 1
          (fun _ => -G - 5) (-5) := by
        intro x
        have hx := Geometric.sample_cost_bound r n x
        have hle : (Geometric.operationBound n : ℝ) ≤ G := by
          change (Geometric.operationBound n : ℝ) ≤ (Geometric.operationBound N : ℝ)
          exact_mod_cast operationBound_mono hnN
        change _ + (-G - 5) ≤ -5
        linarith
      have hk : ∀ k : ℕ,
          (if hk : k < n then
            ((sample r (n - k - 1) (start + k + 1)).bind fun xs =>
              .tick 2 (.ret ((start + k) :: xs))) else .ret []).Bound
            (fun k : ℕ => (k : ℝ)) 1
            (fun xs => -K * ((xs.length : ℝ) + 1)) (-G - 5) := by
        intro k
        split_ifs with hkn
        · have hi := ih (n - k - 1) (by omega) (start + k + 1)
            (by omega : n - k - 1 ≤ N)
          have hb := Program.bound_bind (sample r (n - k - 1) (start + k + 1))
            (fun xs => .tick 2 (.ret ((start + k) :: xs))) (fun k : ℕ => (k : ℝ)) 1
            (fun xs => 2 - K * ((xs.length : ℝ) + 2))
            (fun xs => -K * ((xs.length : ℝ) + 1)) (2 - K)
            (fun x => by
              have hx := hi x
              change _ + (2 - K * (_ + 2)) ≤ 2 - K
              linarith)
            (fun xs => by
              intro x
              simp only [Program.cost, Program.output, List.length_cons,
                Nat.cast_add, Nat.cast_ofNat, add_zero]
              ring_nf
              exact le_refl _)
          intro x
          have hx := hb x
          exact hx.trans (by linarith)
        · apply Program.bound_ret
          simp only [List.length_nil, Nat.cast_zero, zero_add]
          linarith
      have hb := Program.bound_bind (Geometric.sample r n) _
        (fun k : ℕ => (k : ℝ)) 1 (fun _ => -G - 5)
        (fun xs : List ℕ => -K * ((xs.length : ℝ) + 1)) (-5) hgeo hk
      apply Program.bound_tick
      simpa only [K, zero_sub, Nat.cast_ofNat] using hb

theorem expectedCost_le (r : ℚ) (n start : ℕ) :
    (sample r n start).expectedCost (fun k : ℕ => (k : ℝ)) 1 ≤
      (operationBound n : ℝ) *
        ((sample r n start).expect (fun xs => (xs.length : ℝ)) + 1) := by
  have hh := Program.expected_bound _ _ _
    (fun xs : List ℕ => -(operationBound n : ℝ) * ((xs.length : ℝ) + 1)) 0
    (sample_cost_bound r n start n (le_refl _))
  rw [Program.expect_const_mul, Program.expect_add, Program.expect_const] at hh
  linarith

end SteinerUpperBound.Matching.Padded.Sparse
