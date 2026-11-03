module

public import SteinerUpperBound.FinitePhase.Spacing

@[expose] public section

namespace SteinerUpperBound.FinitePhase

open SteinerLowerBound
open scoped Classical BigOperators

instance phaseNonempty : Nonempty (Fin count) :=
  ⟨⟨0, by norm_num [count]⟩⟩

noncomputable def law : Law (Fin count) := Law.uniform _

noncomputable def badEdge (base : ℝ) (height : Fin count → ℕ) (w : ℝ) (j : Fin count) : ℝ :=
  ∑ i : Fin (height j + 1), if Window base j i.val w then scale base j i.val else 0

theorem badEdge_nonneg (base : ℝ) (hb : 0 < base) (height : Fin count → ℕ)
    (w : ℝ) (j : Fin count) : 0 ≤ badEdge base height w j := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact (scale_pos base hb j i.val).le
  · rfl

theorem sum_badEdge_le (base : ℝ) (hb : 0 < base) (height : Fin count → ℕ)
    (w : ℝ) (hw : 0 ≤ w) :
    (∑ j, badEdge base height w j) ≤ w / contraction := by
  by_cases hex : ∃ j, ∃ i : Fin (height j + 1), Window base j i.val w
  · obtain ⟨j, i, hi⟩ := hex
    have hother (k : Fin count) (hkj : k ≠ j) : badEdge base height w k = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      have hn : ¬ Window base k t.val w := by
        intro h
        exact hkj (window_unique base hb h hi).1
      simp only [hn, ite_false]
    have hsame : badEdge base height w j = scale base j i.val := by
      unfold badEdge
      rw [Finset.sum_eq_single i]
      · simp only [hi, ite_true]
      · intro t _ hti
        have hn : ¬ Window base j t.val w := by
          intro h
          exact hti (Fin.ext (window_unique base hb h hi).2)
        simp only [hn, ite_false]
      · simp
    calc
      _ = badEdge base height w j := by
        apply Finset.sum_eq_single
        · intro k _ hkj
          exact hother k hkj
        · simp
      _ = scale base j i.val := hsame
      _ ≤ w / contraction := by
        apply (le_div_iff₀ contraction_pos).mpr
        simpa only [mul_comm] using hi.1
  · have hzero (j : Fin count) : badEdge base height w j = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬ Window base j i.val w := fun h => hex ⟨j, i, h⟩
      simp only [hn, ite_false]
    simp only [hzero, Finset.sum_const_zero]
    exact div_nonneg hw contraction_pos.le

theorem expect_uniform (f : Fin count → ℝ) :
    law.expect f = (∑ j, f j) / count := by
  simp only [law, Law.uniform, Law.expect, Fintype.card_fin, ← Finset.mul_sum]
  ring

theorem badEdge_mean (base : ℝ) (hb : 0 < base) (height : Fin count → ℕ)
    (w : ℝ) (hw : 0 ≤ w) :
    law.expect (badEdge base height w) ≤ w / (contraction * count) := by
  rw [expect_uniform]
  calc
    _ ≤ (w / contraction) / (count : ℝ) :=
      div_le_div_of_nonneg_right (sum_badEdge_le base hb height w hw) (Nat.cast_nonneg _)
    _ = _ := div_div _ _ _

noncomputable def profile (base : ℝ) (height : Fin count → ℕ) (weights : List ℝ)
    (j : Fin count) : ℝ :=
  (weights.map (fun w => badEdge base height w j)).sum

theorem profile_nonneg (base : ℝ) (hb : 0 < base) (height : Fin count → ℕ)
    (weights : List ℝ) (j : Fin count) : 0 ≤ profile base height weights j := by
  induction weights with
  | nil => exact le_rfl
  | cons w l ih =>
      exact add_nonneg (badEdge_nonneg base hb height w j) ih

theorem profile_mean (base : ℝ) (hb : 0 < base) (height : Fin count → ℕ)
    (weights : List ℝ) (hw : ∀ w ∈ weights, 0 ≤ w) :
    law.expect (profile base height weights) ≤ weights.sum / (contraction * count) := by
  induction weights with
  | nil =>
      change law.expect (fun _ => 0) ≤ 0 / _
      simp only [Law.expect_const, zero_div, le_refl]
  | cons w l ih =>
      have htail := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
      have hhead := badEdge_mean base hb height w (hw w List.mem_cons_self)
      have hfun : profile base height (w :: l) =
          fun j => badEdge base height w j + profile base height l j := by
        funext j
        rfl
      rw [hfun, Law.expect_add, List.sum_cons, add_div]
      exact add_le_add hhead htail

theorem profile_tail (base : ℝ) (hb : 0 < base) (height : Fin count → ℕ)
    (weights : List ℝ) (hw : ∀ w ∈ weights, 0 ≤ w) (hpos : 0 < weights.sum) :
    law.prob {j | weights.sum / 200 < 2 * profile base height weights j} ≤ 1 / 1000 := by
  have hn : ∀ j, 0 ≤ 2 * profile base height weights j :=
    fun j => mul_nonneg (by norm_num) (profile_nonneg base hb height weights j)
  have hm := law.markov_gt hn (show 0 < weights.sum / 200 by positivity)
  have he : law.expect (fun j => 2 * profile base height weights j) ≤
      2 * (weights.sum / (contraction * count)) := by
    rw [Law.expect_const_mul]
    exact mul_le_mul_of_nonneg_left (profile_mean base hb height weights hw) (by norm_num)
  calc
    _ ≤ law.expect (fun j => 2 * profile base height weights j) / (weights.sum / 200) := hm
    _ ≤ (2 * (weights.sum / (contraction * count))) / (weights.sum / 200) :=
      div_le_div_of_nonneg_right he (by positivity)
    _ = 400 / (contraction * count) := by
      field_simp [ne_of_gt hpos, contraction, delta, count]
      <;> ring
    _ ≤ _ := by norm_num [contraction, delta, count]

end SteinerUpperBound.FinitePhase
