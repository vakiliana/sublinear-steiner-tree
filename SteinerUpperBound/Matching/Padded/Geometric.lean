module

public import SteinerUpperBound.Matching.Padded.Binary

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Geometric

open SteinerLowerBound
open scoped Classical BigOperators

def survival (r : ℚ) (n k : ℕ) : ℚ := if k ≤ n then r ^ k else 0

def weight (r : ℚ) (n k : ℕ) : ℚ := survival r n k - survival r n (k + 1)

theorem survival_nonneg (r : ℚ) (hr : 0 ≤ r) (n k : ℕ) :
    0 ≤ survival r n k := by
  unfold survival
  split_ifs <;> first | exact pow_nonneg hr _ | exact le_refl _

theorem survival_antitone (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (n : ℕ) :
    Antitone (survival r n) := by
  apply antitone_nat_of_succ_le
  intro k
  by_cases hk : k < n
  · have hk' : k + 1 ≤ n := by omega
    simp only [survival, hk', Nat.le_of_lt hk, ↓reduceIte, pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg h0 _) h1
  · by_cases he : k = n
    · subst k
      simpa [survival] using (pow_nonneg h0 n)
    · have hk' : ¬ k ≤ n := by omega
      have hk'' : ¬ k + 1 ≤ n := by omega
      simp [survival, hk', hk'']

theorem weight_nonneg (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (n k : ℕ) :
    0 ≤ weight r n k :=
  sub_nonneg.mpr (survival_antitone r h0 h1 n (Nat.le_succ k))

theorem weight_before (r : ℚ) (n k : ℕ) (hk : k < n) :
    weight r n k = r ^ k * (1 - r) := by
  have hk' : k + 1 ≤ n := by omega
  simp only [weight, survival, Nat.le_of_lt hk, hk', ↓reduceIte, pow_succ]
  ring

@[simp] theorem weight_last (r : ℚ) (n : ℕ) : weight r n n = r ^ n := by
  simp [weight, survival]

theorem total_weight (r : ℚ) (n lo len : ℕ) :
    Binary.total (weight r n) lo len = survival r n lo - survival r n (lo + len) := by
  induction len with
  | zero => simp [Binary.total]
  | succ len ih =>
    simp only [Binary.total, Finset.sum_range_succ] at ih ⊢
    rw [ih]
    unfold weight
    have he : lo + (len + 1) = lo + len + 1 := by omega
    rw [he]
    ring

def power (r : ℚ) (n k : ℕ) : Arithmetic ℚ :=
  if k ≤ n then Arithmetic.fastPow r k else ⟨0, 1⟩

@[simp] theorem power_value (r : ℚ) (n k : ℕ) :
    (power r n k).value = survival r n k := by
  unfold power survival
  split_ifs <;> simp [Arithmetic.fastPow_value]

theorem power_operations (r : ℚ) (n k : ℕ) :
    (power r n k).operations ≤ 16 * (Nat.log 2 (n + 1) + 1) := by
  unfold power
  split_ifs with hk
  · exact (Arithmetic.fastPow_operations r k).trans
      (Nat.mul_le_mul_left 16 (Nat.add_le_add_right
        (Nat.log_mono_right (show k ≤ n + 1 by omega)) 1))
  · dsimp only
    omega

def massFn (r : ℚ) (n lo len : ℕ) : Arithmetic ℚ :=
  let a := power r n lo
  let b := power r n (lo + len)
  ⟨a.value - b.value, a.operations + b.operations + 4⟩

theorem massFn_value (r : ℚ) (n lo len : ℕ) :
    (massFn r n lo len).value = Binary.total (weight r n) lo len := by
  simp only [massFn, power_value, total_weight]

theorem massFn_operations (r : ℚ) (n lo len : ℕ) :
    (massFn r n lo len).operations ≤ 32 * (Nat.log 2 (n + 1) + 1) + 4 := by
  have ha := power_operations r n lo
  have hb := power_operations r n (lo + len)
  dsimp only [massFn]
  omega

def height (n : ℕ) : ℕ := Nat.log 2 (n + 1) + 1

def sample (r : ℚ) (n : ℕ) : Program ℕ ℕ :=
  Binary.sample (massFn r n) (height n) 0 (n + 1)

theorem sample_supported (r : ℚ) (n : ℕ) :
    (sample r n).Supported (fun k => k ≤ n) := by
  have hs := Binary.sample_supported (massFn r n) (height n) 0 (n + 1) (by omega)
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n + 1)).le
  unfold sample
  intro x
  have hx := hs x
  omega

/-- Exact truncated geometric law; `n` is the no-success sentinel. -/
theorem expect_sample (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (n : ℕ) (f : ℕ → ℝ) :
    (sample r n).expect f =
      (∑ k ∈ Finset.range n, ((r ^ k * (1 - r) : ℚ) : ℝ) * f k) +
        ((r ^ n : ℚ) : ℝ) * f n := by
  have hh := Binary.sample_weighted (massFn r n) (weight r n)
    (weight_nonneg r h0 h1 n) (n + 1)
    (fun lo len _ => massFn_value r n lo len) (height n) 0 (n + 1) (by omega)
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n + 1)).le (by omega) f
  have hm : (massFn r n 0 (n + 1)).value = 1 := by
    rw [massFn_value, total_weight]
    simp [survival]
  rw [hm, Rat.cast_one, one_mul] at hh
  rw [sample, hh]
  unfold Binary.weighted
  rw [Finset.sum_range_succ]
  simp only [Nat.zero_add, weight_last]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [weight_before r n k (Finset.mem_range.mp hk)]

def operationBound (n : ℕ) : ℕ := 128 * (height n + 1) ^ 2

/-- Pathwise arithmetic/draw bound for the implemented CDF binary search. -/
theorem sample_cost_bound (r : ℚ) (n : ℕ) :
    (sample r n).Bound (fun k : ℕ => (k : ℝ)) 1 (fun _ => 0) (operationBound n) := by
  have hb := Binary.sample_cost_bound (massFn r n) (n + 1)
    (32 * height n + 4) (fun lo len _ => massFn_operations r n lo len)
    (height n) 0 (n + 1) (by omega)
  intro x
  have hx := hb x
  have hnum : (height n + 1) * (2 * (32 * height n + 4) + 16) ≤ operationBound n := by
    have haux (H : ℕ) : (H + 1) * (2 * (32 * H + 4) + 16) ≤ 128 * (H + 1) ^ 2 := by
      have hh : 2 * (32 * H + 4) + 16 ≤ 128 * (H + 1) := by omega
      calc
        _ ≤ (H + 1) * (128 * (H + 1)) := Nat.mul_le_mul_left _ hh
        _ = _ := by ring
    exact haux (height n)
  exact hx.trans (by exact_mod_cast hnum)

end SteinerUpperBound.Matching.Padded.Geometric
