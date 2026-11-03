module

public import SteinerUpperBound.Matching.Padded.Semantics

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Range

open SteinerLowerBound
open scoped Classical BigOperators

def embedding (Q lo hi : ℕ) (h : lo < hi ∧ hi ≤ Q) :
    Fin (hi - lo) ↪ Fin Q where
  toFun i := ⟨lo + i.val, by have := i.isLt; omega⟩
  inj' i j he := by
    apply Fin.ext
    have hh := congrArg Fin.val he
    change lo + i.val = lo + j.val at hh
    omega

def sample (Q : ℕ) (hQ : 0 < Q) (lo hi : ℕ) : Program ℕ (Fin Q) :=
  if h : lo < hi ∧ hi ≤ Q then
    .tick 1 (.draw (hi - lo) (by omega) fun i => .ret (embedding Q lo hi h i))
  else .ret ⟨0, hQ⟩

noncomputable def law (Q : ℕ) (hQ : 0 < Q) (lo hi : ℕ) : Law (Fin Q) :=
  if h : lo < hi ∧ hi ≤ Q then by
    letI : Nonempty (Fin (hi - lo)) := ⟨⟨0, by omega⟩⟩
    exact (Law.uniform (Fin (hi - lo))).map (embedding Q lo hi h)
  else Law.pure ⟨0, hQ⟩

theorem expect_sample (Q : ℕ) (hQ : 0 < Q) (lo hi : ℕ) (f : Fin Q → ℝ) :
    (sample Q hQ lo hi).expect f = (law Q hQ lo hi).expect f := by
  unfold sample law
  split_ifs
  · rw [Program.expect_tick, Program.expect_draw, Law.expect_map]
    simp only [Program.expect_ret, Law.expect, Law.uniform, Fintype.card_fin]
  · simp [Law.expect_pure]

theorem sample_supported (Q : ℕ) (hQ : 0 < Q) (lo hi : ℕ)
    (h : lo < hi ∧ hi ≤ Q) :
    (sample Q hQ lo hi).Supported (fun r => lo ≤ r.val ∧ r.val < hi) := by
  unfold sample
  simp only [h]
  intro x
  change lo ≤ lo + x.1.val ∧ lo + x.1.val < hi
  have hx := x.1.isLt
  omega

theorem sample_cost_le (Q : ℕ) (hQ : 0 < Q) (lo hi : ℕ) :
    (sample Q hQ lo hi).Bound (fun n : ℕ => (n : ℝ)) 1 (fun _ => 0) 2 := by
  unfold sample
  split_ifs
  · intro x
    change ((1 : ℕ) : ℝ) + (1 + 0) + 0 ≤ 2
    norm_num
  · exact Program.bound_ret _ _ _ _ _ (by norm_num)

theorem mass (Q : ℕ) (hQ : 0 < Q) (lo hi : ℕ) (h : lo < hi ∧ hi ≤ Q) (r : Fin Q) :
    (law Q hQ lo hi).mass r =
      if lo ≤ r.val ∧ r.val < hi then (((hi - lo : ℕ) : ℝ)⁻¹) else (0 : ℝ) := by
  classical
  rw [law, dite_eq_left h]
  simp only [Law.map, Law.uniform, Fintype.card_fin]
  by_cases hr : lo ≤ r.val ∧ r.val < hi
  · simp only [hr]
    let i : Fin (hi - lo) := ⟨r.val - lo, by omega⟩
    have he : embedding Q lo hi h i = r := by
      apply Fin.ext
      change lo + (r.val - lo) = r.val
      omega
    have hi (j : Fin (hi - lo)) :
        embedding Q lo hi h j = r ↔ j = i := by
      rw [← he]
      exact (embedding Q lo hi h).injective.eq_iff
    simp_rw [hi]
    simp
  · simp only [hr, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro i _
    have he : embedding Q lo hi h i ≠ r := by
      intro heq
      have hh := congrArg Fin.val heq
      change lo + i.val = r.val at hh
      have hb := i.isLt
      exact hr ⟨by omega, by omega⟩
    simp [he]

def probability (Q a b : ℕ) : ℚ :=
  ((b - a : ℕ) : ℚ) / ((Q - a : ℕ) : ℚ)

theorem probability_bounds (Q a b : ℕ) (hab : a < b) (hbQ : b ≤ Q) :
    0 ≤ probability Q a b ∧ probability Q a b ≤ 1 := by
  have hqa : (0 : ℚ) < (Q - a : ℕ) := by exact_mod_cast (by omega : 0 < Q - a)
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hqa.le
  · apply (div_le_one hqa).mpr
    exact_mod_cast (by omega : b - a ≤ Q - a)

/-- Single-coordinate posterior identity, including the final bucket `b = Q`. -/
theorem reveal_identity (Q : ℕ) (hQ : 0 < Q) (a b : ℕ)
    (hab : a < b) (hbQ : b ≤ Q) (f : Option (Fin Q) → Fin Q → ℝ) :
    (law Q hQ a Q).expect (fun r => f (if r.val < b then some r else none) r) =
      (IntegerCoin.sample (probability Q a b)).expect (fun hit =>
        match hit with
        | true => (sample Q hQ a b).expect (fun r => f (some r) r)
        | false => (law Q hQ b Q).expect (fun r => f none r)) := by
  have hprob := probability_bounds Q a b hab hbQ
  rw [IntegerCoin.expect_sample _ hprob.1 hprob.2]
  simp only
  rw [expect_sample Q hQ a b]
  unfold Law.expect
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  have haQ : a < Q := hab.trans_le hbQ
  have hba : (b - a : ℕ) ≠ 0 := by omega
  have hQa : (Q - a : ℕ) ≠ 0 := by omega
  have hbaR : ((b - a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hba
  have hQaR : ((Q - a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hQa
  have hpr : (probability Q a b : ℝ) =
      ((b - a : ℕ) : ℝ) / (Q - a : ℕ) := by simp [probability]
  rw [hpr, mass Q hQ a Q ⟨haQ, le_refl _⟩ r, mass Q hQ a b ⟨hab, hbQ⟩ r]
  by_cases hb : b < Q
  · have hQb : (Q - b : ℕ) ≠ 0 := by omega
    have hQbR : ((Q - b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hQb
    rw [mass Q hQ b Q ⟨hb, le_refl _⟩ r]
    have hsum : ((Q - a : ℕ) : ℝ) =
        ((b - a : ℕ) : ℝ) + ((Q - b : ℕ) : ℝ) := by
      exact_mod_cast (by omega : Q - a = (b - a) + (Q - b))
    by_cases hrb : r.val < b
    · have hbn : ¬ b ≤ r.val := by omega
      by_cases har : a ≤ r.val <;>
        simp only [har, hrb, hbn, r.isLt, and_true, ↓reduceIte] <;>
        field_simp <;> ring
    · have hbr : b ≤ r.val := by omega
      have har : a ≤ r.val := by omega
      simp only [har, hrb, hbr, r.isLt, and_self, and_false, ↓reduceIte]
      field_simp
      rw [hsum]
      ring
  · have hb' : b = Q := by omega
    subst b
    have hp1 : ((Q - a : ℕ) : ℝ) / (Q - a : ℕ) = 1 := div_self hQaR
    rw [hp1]
    simp [r.isLt]

end SteinerUpperBound.Matching.Padded.Range
