module

public import SteinerUpperBound.Structural.Statistics

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open scoped Classical BigOperators

structure Grid where
  intervals : ℕ
  q : ℝ
  first : ℝ
  ratio_gt_one : 1 < q
  first_pos : 0 < first

namespace Grid

noncomputable def scale (g : Grid) (i : ℕ) : ℝ := g.first * g.q ^ i

noncomputable def width (g : Grid) (i : ℕ) : ℝ := g.scale (i + 1) - g.scale i

theorem ratio_pos (g : Grid) : 0 < g.q := lt_trans (by norm_num) g.ratio_gt_one

@[simp] theorem scale_zero (g : Grid) : g.scale 0 = g.first := by simp [scale]

theorem scale_pos (g : Grid) (i : ℕ) : 0 < g.scale i :=
  mul_pos g.first_pos (pow_pos g.ratio_pos _)

theorem scale_succ (g : Grid) (i : ℕ) : g.scale (i + 1) = g.q * g.scale i := by
  simp only [scale, pow_succ]
  ring

theorem scale_le_succ (g : Grid) (i : ℕ) : g.scale i ≤ g.scale (i + 1) := by
  rw [scale_succ]
  nlinarith [g.scale_pos i, g.ratio_gt_one]

theorem scale_mono (g : Grid) : Monotone g.scale :=
  monotone_nat_of_le_succ g.scale_le_succ

theorem width_nonneg (g : Grid) (i : ℕ) : 0 ≤ g.width i :=
  sub_nonneg.mpr (g.scale_le_succ i)

theorem width_eq (g : Grid) (i : ℕ) : g.width i = (g.q - 1) * g.scale i := by
  rw [width, scale_succ]
  ring

theorem sum_widths (g : Grid) :
    (∑ i ∈ Finset.range g.intervals, g.width i) = g.scale g.intervals - g.first := by
  rw [show (fun i => g.width i) = (fun i => g.scale (i + 1) - g.scale i) from rfl,
    Finset.sum_range_sub, scale_zero]

theorem sum_scales (g : Grid) :
    (∑ i ∈ Finset.range g.intervals, g.scale i) =
      (g.scale g.intervals - g.first) / (g.q - 1) := by
  have h := g.sum_widths
  simp_rw [g.width_eq] at h
  rw [← Finset.mul_sum] at h
  apply (eq_div_iff (sub_ne_zero.mpr g.ratio_gt_one.ne')).mpr
  nlinarith

noncomputable abbrev toStructural (g : Grid) (hq : g.q = Structural.omega) : Structural.Grid :=
  { intervals := g.intervals
    scale := fun i => g.scale i.val
    positive := fun i => g.scale_pos i.val
    ratio := fun i => by
      change g.scale (i.val + 1) = Structural.omega * g.scale i.val
      rw [← hq]
      exact g.scale_succ i.val }

end Grid

noncomputable def relativeStart (k : ℕ) (zeta theta : ℝ) : ℝ :=
  zeta * theta / (4 * k)

/-- Bounded scalar iteration returns the first crossing, not the budget endpoint. -/
noncomputable def firstAbove (q x : ℝ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 => if 4 < x then 0 else 1 + firstAbove q (x * q) fuel

theorem firstAbove_le (q x : ℝ) (fuel : ℕ) : firstAbove q x fuel ≤ fuel := by
  induction fuel generalizing x with
  | zero => exact le_rfl
  | succ fuel ih =>
    simp only [firstAbove]
    split_ifs
    · exact Nat.zero_le _
    · have h := ih (x * q)
      omega

theorem firstAbove_spec (q x : ℝ) (fuel : ℕ) (hcross : 4 < x * q ^ fuel) :
    4 < x * q ^ firstAbove q x fuel ∧
      ∀ j < firstAbove q x fuel, x * q ^ j ≤ 4 := by
  induction fuel generalizing x with
  | zero => exact ⟨hcross, by simp [firstAbove]⟩
  | succ fuel ih =>
    by_cases hx : 4 < x
    · simp [firstAbove, hx]
    · have ht : 4 < (x * q) * q ^ fuel := by
        simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hcross
      obtain ⟨hnew, hmin⟩ := ih (x * q) ht
      simp only [firstAbove, hx, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · simpa only [pow_add, pow_one, mul_assoc, mul_left_comm, mul_comm] using hnew
      · intro j hj
        cases j with
        | zero => simpa only [pow_zero, mul_one] using le_of_not_gt hx
        | succ j =>
          have h := hmin j (by omega)
          simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

theorem firstAbove_last_le (q x : ℝ) (hq : 0 ≤ q) (hx : x ≤ 4) (fuel : ℕ)
    (hcross : 4 < x * q ^ fuel) : x * q ^ firstAbove q x fuel ≤ 4 * q := by
  obtain ⟨hyes, hmin⟩ := firstAbove_spec q x fuel hcross
  have hpos : 0 < firstAbove q x fuel := by
    by_contra h
    have he : firstAbove q x fuel = 0 := by omega
    simpa only [he, pow_zero, mul_one, not_lt.mpr hx] using hyes
  have hh := mul_le_mul_of_nonneg_right
    (hmin (firstAbove q x fuel - 1) (by omega)) hq
  have he : firstAbove q x fuel = (firstAbove q x fuel - 1) + 1 := by omega
  calc
    _ = (x * q ^ (firstAbove q x fuel - 1)) * q := by
      conv_lhs => rw [he, pow_succ]
      ring
    _ ≤ _ := hh

structure GridConstants (q zeta : ℝ) where
  block : ℕ
  offset : ℕ
  doubling : (2 : ℝ) ≤ q ^ block
  offset_large : 16 ≤ zeta * (2 : ℝ) ^ offset

theorem gridConstants_exist (q zeta : ℝ) (hq : 1 < q) (hz : 0 < zeta) :
    Nonempty (GridConstants q zeta) := by
  obtain ⟨B, hB⟩ := pow_unbounded_of_one_lt (2 : ℝ) hq
  obtain ⟨D, hD⟩ := pow_unbounded_of_one_lt (16 / zeta) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨⟨B, D, hB.le, ?_⟩⟩
  have h := (div_lt_iff₀ hz).mp hD
  nlinarith

namespace GridConstants

noncomputable def budget {q zeta : ℝ} (c : GridConstants q zeta) (k : ℕ) : ℕ :=
  c.block * (c.offset + Nat.log2 (k + 1) + 1)

theorem budget_log_bound {q zeta : ℝ} (c : GridConstants q zeta) (k : ℕ) :
    c.budget k + 1 ≤ (c.block * (c.offset + 1) + 1) * (1 + Nat.log2 (k + 1)) := by
  unfold budget
  nlinarith [Nat.zero_le (c.block * c.offset * Nat.log2 (k + 1))]

theorem budget_crosses {q zeta : ℝ} (c : GridConstants q zeta)
    (k : ℕ) (hk : 0 < k) (theta : ℝ) (ht : 1 ≤ theta) (hz : 0 < zeta) :
    4 < relativeStart k zeta theta * q ^ c.budget k := by
  have hlogN : k + 1 < 2 ^ (Nat.log2 (k + 1) + 1) := Nat.lt_log2_self
  have hlog : (k : ℝ) + 1 < (2 : ℝ) ^ (Nat.log2 (k + 1) + 1) := by exact_mod_cast hlogN
  have hpow : (2 : ℝ) ^ (c.offset + Nat.log2 (k + 1) + 1) ≤ q ^ c.budget k := by
    unfold budget
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) c.doubling _
  have hlarge := mul_le_mul_of_nonneg_right c.offset_large
    (show (0 : ℝ) ≤ 2 ^ (Nat.log2 (k + 1) + 1) by positivity)
  have hprod : 16 * (k : ℝ) < zeta * (2 : ℝ) ^ (c.offset + Nat.log2 (k + 1) + 1) := by
    rw [show c.offset + Nat.log2 (k + 1) + 1 = c.offset + (Nat.log2 (k + 1) + 1) by omega,
      pow_add]
    nlinarith
  have htheta := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ zeta * (2 : ℝ) ^ (c.offset + Nat.log2 (k + 1) + 1) by positivity)
  have hscale := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ zeta * theta by positivity)
  unfold relativeStart
  rw [div_mul_eq_mul_div, lt_div_iff₀ (show (0 : ℝ) < 4 * k by positivity)]
  nlinarith

end GridConstants

noncomputable abbrev generate (k : ℕ) (q zeta theta R : ℝ) (fuel : ℕ)
    (hk : 0 < k) (hq : 1 < q) (hz : 0 < zeta) (ht : 0 < theta) (hR : 0 < R) : Grid :=
  { intervals := firstAbove q (relativeStart k zeta theta) fuel
    q := q
    first := relativeStart k zeta theta * R
    ratio_gt_one := hq
    first_pos := mul_pos (div_pos (mul_pos hz ht) (by positivity)) hR }

theorem generated_scale (k : ℕ) (q zeta theta R : ℝ) (fuel : ℕ)
    (hk : 0 < k) (hq : 1 < q) (hz : 0 < zeta) (ht : 0 < theta) (hR : 0 < R) (i : ℕ) :
    (generate k q zeta theta R fuel hk hq hz ht hR).scale i =
      ((zeta * R / k) / 4) * theta * q ^ i := by
  dsimp only [Grid.scale, generate, relativeStart]
  ring

theorem generated_endpoints (k : ℕ) (q zeta theta R : ℝ)
    (hk : 2 ≤ k) (hq : 1 < q) (hq2 : q ≤ 2) (hz : 0 < zeta) (hz1 : zeta ≤ 1)
    (ht : 1 ≤ theta) (htq : theta < q) (hR : 0 < R) (c : GridConstants q zeta) :
    let g := generate k q zeta theta R (c.budget k) (by omega) hq hz (by linarith) hR
    g.first < (zeta * R / k) / 2 ∧
      4 * R < g.scale g.intervals ∧ g.scale g.intervals ≤ 4 * q * R ∧
      g.intervals + 1 ≤ (c.block * (c.offset + 1) + 1) * (1 + Nat.log2 (k + 1)) := by
  dsimp only
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hx : relativeStart k zeta theta ≤ 4 := by
    unfold relativeStart
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * k)]
    have htheta : 0 ≤ theta := by linarith
    have hzt := mul_le_mul_of_nonneg_right hz1 htheta
    have hk2R : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hcross := c.budget_crosses k (by omega) theta ht hz
  have hyes := (firstAbove_spec q (relativeStart k zeta theta) (c.budget k) hcross).1
  have hlast := firstAbove_last_le q _ (by linarith) hx (c.budget k) hcross
  refine ⟨?_, ?_, ?_, ?_⟩
  · change relativeStart k zeta theta * R < _
    unfold relativeStart
    have htheta : theta < 2 := htq.trans_le hq2
    have hm := mul_lt_mul_of_pos_left htheta
      (show 0 < zeta * R / (4 * k) by positivity)
    calc
      zeta * theta / (4 * k) * R = (zeta * R / (4 * k)) * theta := by ring
      _ < (zeta * R / (4 * k)) * 2 := hm
      _ = _ := by ring
  · change 4 * R < (relativeStart k zeta theta * R) * q ^ _
    nlinarith [mul_lt_mul_of_pos_right hyes hR]
  · change (relativeStart k zeta theta * R) * q ^ _ ≤ 4 * q * R
    nlinarith [mul_le_mul_of_nonneg_right hlast hR.le]
  · exact (Nat.add_le_add_right (firstAbove_le _ _ _) 1).trans (c.budget_log_bound k)

theorem generated_sum_scales (g : Grid) (R : ℝ) (hR : 0 ≤ R)
    (hlast : g.scale g.intervals ≤ 4 * g.q * R) :
    (∑ i ∈ Finset.range g.intervals, g.scale i) ≤ 5 * g.q / (g.q - 1) * R := by
  rw [g.sum_scales]
  have hq : 0 < g.q - 1 := sub_pos.mpr g.ratio_gt_one
  apply (div_le_iff₀ hq).mpr
  have hqr : 0 ≤ g.q * R := mul_nonneg g.ratio_pos.le hR
  have he : (5 * g.q / (g.q - 1) * R) * (g.q - 1) = 5 * g.q * R := by
    field_simp
  rw [he]
  linarith [g.first_pos]

end SteinerUpperBound.MSTApproximation
