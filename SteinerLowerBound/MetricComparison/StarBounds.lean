module

public import SteinerLowerBound.MetricComparison.LocalMasses

@[expose] public section

namespace SteinerLowerBound.MetricComparison

open scoped BigOperators Classical
open HardDistribution

variable {S Ω : Type*} [Fintype S]

noncomputable def scale (k : Setup S Ω) : ℝ :=
  1 + |k.H0 * k.M ^ k.d| + |anchorConstant k.d k.H0 k.M| +
    |24 * (k.H0 * k.M ^ k.d) * (k.d.choose 3 : ℝ) / k.d|

theorem scale_ge_one (k : Setup S Ω) : 1 ≤ scale k := by
  unfold scale
  linarith [abs_nonneg (k.H0 * k.M ^ k.d),
    abs_nonneg (anchorConstant k.d k.H0 k.M),
    abs_nonneg (24 * (k.H0 * k.M ^ k.d) * (k.d.choose 3 : ℝ) / k.d)]

theorem scale_pos (k : Setup S Ω) : 0 < scale k :=
  lt_of_lt_of_le (by norm_num) (scale_ge_one k)

theorem amplitude_le_scale (k : Setup S Ω) : k.H0 * k.M ^ k.d ≤ scale k := by
  unfold scale
  linarith [le_abs_self (k.H0 * k.M ^ k.d),
    abs_nonneg (anchorConstant k.d k.H0 k.M),
    abs_nonneg (24 * (k.H0 * k.M ^ k.d) * (k.d.choose 3 : ℝ) / k.d)]

theorem anchor_le_scale (k : Setup S Ω) : anchorConstant k.d k.H0 k.M ≤ scale k := by
  unfold scale
  linarith [abs_nonneg (k.H0 * k.M ^ k.d),
    le_abs_self (anchorConstant k.d k.H0 k.M),
    abs_nonneg (24 * (k.H0 * k.M ^ k.d) * (k.d.choose 3 : ℝ) / k.d)]

theorem triple_le_scale (k : Setup S Ω) :
    24 * (k.H0 * k.M ^ k.d) * (k.d.choose 3 : ℝ) / k.d ≤ scale k := by
  unfold scale
  linarith [abs_nonneg (k.H0 * k.M ^ k.d),
    abs_nonneg (anchorConstant k.d k.H0 k.M),
    le_abs_self (24 * (k.H0 * k.M ^ k.d) * (k.d.choose 3 : ℝ) / k.d)]

theorem amplitude_nonneg (k : Setup S Ω) (w : S → Ω) : 0 ≤ k.H0 * k.M ^ k.d := by
  have hs : 0 < Fintype.card S := by have := k.d_ge_three; have := k.enough_special; omega
  obtain ⟨u⟩ := Fintype.card_pos_iff.mp hs
  have hM : 0 ≤ k.M := (k.bounded (w u)).1.trans (k.bounded (w u)).2
  exact mul_nonneg k.H0_nonneg (pow_nonneg hM _)

noncomputable def prescribed (k : Setup S Ω) (w : S → Ω) (P : Finset S) : ℝ :=
  ∑ H : Subsets S k.d, if P ⊆ H.val then
    starMass k.d k.H0 k.R (fun u => k.value (w u)) H else 0

theorem prescribed_nonneg (k : Setup S Ω) (w : S → Ω) (P : Finset S) :
    0 ≤ prescribed k w P := by
  apply Finset.sum_nonneg
  intro H _
  split_ifs
  · exact starMass_nonneg k.d k.H0_nonneg k.R_pos.le (fun u => (k.bounded (w u)).1) H
  · rfl

theorem starEvidence_nonneg (k : Setup S Ω) (w : S → Ω) (h : History S) :
    0 ≤ starEvidence k w h := by
  apply Finset.sum_nonneg
  intro H _
  split_ifs
  · exact starMass_nonneg k.d k.H0_nonneg k.R_pos.le (fun u => (k.bounded (w u)).1) H
  · rfl

theorem starEvidence_le_prescribed (k : Setup S Ω) (w : S → Ω) (h : History S) :
    starEvidence k w h ≤ prescribed k w h.positive := by
  apply Finset.sum_le_sum
  intro H _
  change (if h.compatible H.val then
    starMass k.d k.H0 k.R (fun u => k.value (w u)) H else 0) ≤
      if h.positive ⊆ H.val then
        starMass k.d k.H0 k.R (fun u => k.value (w u)) H else 0
  by_cases hh : h.compatible H.val
  · simp only [hh, hh.1, ↓reduceIte, le_refl]
  · simp only [hh, ↓reduceIte]
    split_ifs
    · exact starMass_nonneg k.d k.H0_nonneg k.R_pos.le (fun u => (k.bounded (w u)).1) H
    · rfl

theorem prescribed_scaled (k : Setup S Ω) (w : S → Ω) (P : Finset S)
    (hP : P.card ≤ k.d) :
    prescribed k w P * ((Fintype.card S).choose P.card : ℝ) ≤
      k.H0 * k.M ^ k.d * (k.d.choose P.card : ℝ) / ((k.d : ℝ) * k.R) := by
  classical
  have hc : ((Fintype.card S).choose k.d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos k.enough_special).ne'
  have hd : (k.d : ℝ) ≠ 0 := by
    exact_mod_cast (show k.d ≠ 0 by have := k.d_ge_three; omega)
  have hid : ((Fintype.card S).choose k.d : ℝ) * (k.d.choose P.card : ℝ) =
      ((Fintype.card S).choose P.card : ℝ) *
        ((Fintype.card S - P.card).choose (k.d - P.card) : ℝ) := by
    exact_mod_cast (Nat.choose_mul (n := Fintype.card S) hP)
  calc
    _ ≤ (((Fintype.card S - P.card).choose (k.d - P.card) : ℝ) *
        (k.H0 / ((k.d : ℝ) * k.R * (Fintype.card S).choose k.d) * k.M ^ k.d)) *
          ((Fintype.card S).choose P.card : ℝ) :=
      mul_le_mul_of_nonneg_right
        (prescribed_mass_le k.d P hP k.H0_nonneg k.R_pos.le
          (fun u => (k.bounded (w u)).1) (fun u => (k.bounded (w u)).2))
        (Nat.cast_nonneg _)
    _ = _ := by
      field_simp [hc, hd, k.R_pos.ne']
      nlinarith [congrArg (fun z : ℝ => k.H0 * k.M ^ k.d * z) hid]

theorem prescribed_one (k : Setup S Ω) (w : S → Ω) (P : Finset S) (hP : P.card = 1) :
    prescribed k w P ≤ scale k / (k.R * Fintype.card S) := by
  have hm : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (show 0 < Fintype.card S by
      have := k.d_ge_three; have := k.enough_special; omega)
  have hd : (0 : ℝ) < k.d := by
    exact_mod_cast (show 0 < k.d by have := k.d_ge_three; omega)
  have h := prescribed_scaled k w P (by have := k.d_ge_three; omega)
  simp only [hP, Nat.choose_one_right] at h
  have hid : k.H0 * k.M ^ k.d * k.d / ((k.d : ℝ) * k.R) =
      k.H0 * k.M ^ k.d / k.R := by field_simp
  rw [hid] at h
  have h' : prescribed k w P ≤ k.H0 * k.M ^ k.d / (k.R * Fintype.card S) := by
    rw [le_div_iff₀ (mul_pos k.R_pos hm)]
    have hh := (le_div_iff₀ k.R_pos).mp h
    nlinarith
  exact h'.trans (div_le_div_of_nonneg_right (amplitude_le_scale k) (mul_pos k.R_pos hm).le)

theorem prescribed_pair (k : Setup S Ω) (w : S → Ω) (P : Finset S) (hP : P.card = 2) :
    prescribed k w P ≤ beta S * scale k / k.R := by
  have hβ : 0 < beta S :=
    beta_pos (by have := k.d_ge_three; have := k.enough_special; omega)
  have hh := anchor_mass_le k.d (by have := k.d_ge_three; omega) k.enough_special
    (⟨P, hP⟩ : Subsets S 2) k.H0_nonneg k.R_pos
    (fun u => (k.bounded (w u)).1) (fun u => (k.bounded (w u)).2)
  have he : (∑ H : Subsets S k.d, if P ⊆ H.val then
      starMass k.d k.H0 k.R (fun u => k.value (w u)) H / beta S else 0) =
      prescribed k w P / beta S := by
    simp only [prescribed, Finset.sum_div, ite_div, zero_div]
  rw [he] at hh
  have hu := hh.trans (div_le_div_of_nonneg_right (anchor_le_scale k) k.R_pos.le)
  rw [div_le_iff₀ hβ] at hu
  calc
    _ ≤ (scale k / k.R) * beta S := hu
    _ = _ := by ring

theorem prescribed_three (k : Setup S Ω) (w : S → Ω)
    (hm : 4 ≤ Fintype.card S) (P : Finset S) (hP : P.card = 3) :
    prescribed k w P ≤ beta S * scale k / (k.R * Fintype.card S) := by
  have hm' : (4 : ℝ) ≤ Fintype.card S := by exact_mod_cast hm
  have hm₀ : (0 : ℝ) < Fintype.card S := by linarith
  have hm₂ : (0 : ℝ) < (Fintype.card S : ℝ) - 2 := by linarith
  have hc₂ : (0 : ℝ) < (Fintype.card S).choose 2 := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ Fintype.card S)
  have hc₃ : (0 : ℝ) < (Fintype.card S).choose 3 := by
    exact_mod_cast Nat.choose_pos (by omega : 3 ≤ Fintype.card S)
  have hd : (0 : ℝ) < k.d := by
    exact_mod_cast (show 0 < k.d by have := k.d_ge_three; omega)
  have hid : ((Fintype.card S).choose 3 : ℝ) * 3 =
      ((Fintype.card S).choose 2 : ℝ) * ((Fintype.card S : ℝ) - 2) := by
    have hh := Nat.choose_mul (n := Fintype.card S) (k := 3) (s := 2) (by omega)
    norm_num at hh
    have hh' := congrArg (fun z : ℕ => (z : ℝ)) hh
    push_cast at hh'
    rwa [Nat.cast_sub (by omega : 2 ≤ Fintype.card S), Nat.cast_ofNat] at hh'
  have hc₃eq : ((Fintype.card S).choose 3 : ℝ) =
      ((Fintype.card S).choose 2 : ℝ) * ((Fintype.card S : ℝ) - 2) / 3 := by linarith
  have h := prescribed_scaled k w P (by have := k.d_ge_three; omega)
  simp only [hP] at h
  have hh : prescribed k w P ≤
      (k.H0 * k.M ^ k.d * (k.d.choose 3 : ℝ) / ((k.d : ℝ) * k.R)) /
        ((Fintype.card S).choose 3 : ℝ) := (le_div_iff₀ hc₃).mpr h
  have hnorm :
      (k.H0 * k.M ^ k.d * (k.d.choose 3 : ℝ) / ((k.d : ℝ) * k.R)) /
        ((Fintype.card S).choose 3 : ℝ) =
        beta S * (12 * (k.H0 * k.M ^ k.d) * (k.d.choose 3 : ℝ) / k.d) /
          (k.R * ((Fintype.card S : ℝ) - 2)) := by
    rw [hc₃eq]
    unfold beta
    field_simp
    <;> ring
  rw [hnorm] at hh
  have hnum : 0 ≤ beta S *
      (12 * (k.H0 * k.M ^ k.d) * (k.d.choose 3 : ℝ) / k.d) := by
    have := amplitude_nonneg k w
    have := (beta_pos (S := S) (by omega : 2 ≤ Fintype.card S)).le
    positivity
  have hden : k.R * Fintype.card S ≤ 2 * (k.R * ((Fintype.card S : ℝ) - 2)) := by
    nlinarith [k.R_pos]
  calc
    _ ≤ _ := hh
    _ ≤ beta S * (24 * (k.H0 * k.M ^ k.d) * (k.d.choose 3 : ℝ) / k.d) /
        (k.R * Fintype.card S) := by
      apply (div_le_div_iff₀ (mul_pos k.R_pos hm₂) (mul_pos k.R_pos hm₀)).mpr
      have hs := mul_le_mul_of_nonneg_left hden hnum
      convert hs using 1 <;> ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (triple_le_scale k)
        (beta_pos (S := S) (by omega : 2 ≤ Fintype.card S)).le)
      (mul_pos k.R_pos hm₀).le

theorem starTotal_le_scale (k : Setup S Ω) (w : S → Ω) :
    starTotal k.d k.H0 k.R (fun u => k.value (w u)) ≤ scale k / k.R := by
  have hd : (1 : ℝ) ≤ k.d := by
    exact_mod_cast (show 1 ≤ k.d by have := k.d_ge_three; omega)
  have h := starTotal_le k.d k.enough_special k.H0_nonneg k.R_pos
    (fun u => (k.bounded (w u)).1) (fun u => (k.bounded (w u)).2)
  exact h.trans ((div_le_div_of_nonneg_left (amplitude_nonneg k w)
    k.R_pos (by nlinarith [k.R_pos])).trans
      (div_le_div_of_nonneg_right (amplitude_le_scale k) k.R_pos.le))

end SteinerLowerBound.MetricComparison
