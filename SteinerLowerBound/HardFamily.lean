module

public import SteinerLowerBound.CostGap
public import SteinerLowerBound.AdaptiveProposals

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace HardFamily

open HardDistribution WeightConstruction

structure Family (η : ℝ) (s : ℕ) where
  d : ℕ
  H0 : ℝ
  d_ge_four : 4 ≤ d
  H0_pos : 0 < H0
  H0_product : η * H0 = 60000
  cluster_budget : 300 ≤ η * d
  star_budget : 60000 * H0 ≤ η * d
  weights : WeightLaws (s + 2) (η / 10000) (1 / (1 + 1 / (2 * (d : ℝ))))

theorem exists_family {η : ℝ} (hη : 0 < η) (s : ℕ) : Nonempty (Family η s) := by
  let H0 := 60000 / η
  have hH0 : 0 < H0 := by dsimp [H0]; positivity
  obtain ⟨d, hd⟩ := exists_nat_gt (max (4 : ℝ) (max (300 / η) (60000 * H0 / η)))
  have hd₄ : 4 ≤ d := by
    have := (le_max_left (4 : ℝ) _).trans_lt hd
    exact_mod_cast this.le
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h₁ : 300 ≤ η * d := by
    have hb : 300 / η ≤ (d : ℝ) :=
      ((le_max_left (300 / η) _).trans (le_max_right (4 : ℝ) _)).trans hd.le
    have := (div_le_iff₀ hη).mp hb
    nlinarith
  have h₂ : 60000 * H0 ≤ η * d := by
    have hb : 60000 * H0 / η ≤ (d : ℝ) :=
      ((le_max_right (300 / η) _).trans (le_max_right (4 : ℝ) _)).trans hd.le
    have := (div_le_iff₀ hη).mp hb
    nlinarith
  obtain ⟨weights⟩ := moment_matched_weights_lower (s + 2) (by omega)
    (η / 10000) (1 / (2 * (d : ℝ))) (by positivity) (by positivity)
  exact ⟨
    { d := d
      H0 := H0
      d_ge_four := hd₄
      H0_pos := hH0
      H0_product := by dsimp [H0]; field_simp
      cluster_budget := h₁
      star_budget := h₂
      weights := weights }⟩

variable {η : ℝ} {s : ℕ}

namespace Family

theorem bound_ge_one (f : Family η s) : 1 ≤ f.weights.bound := by
  have h := f.weights.yes.expect_mono (fun ω => (f.weights.bounded ω).2)
  rw [f.weights.mean_yes, Law.expect_const] at h
  exact h

noncomputable def normalized (f : Family η s) (ω : f.weights.Carrier) : Rate :=
  ⟨f.weights.value ω / f.weights.bound,
    div_nonneg (f.weights.bounded ω).1 (le_trans zero_le_one (bound_ge_one f)),
    (div_le_one (lt_of_lt_of_le zero_lt_one (bound_ge_one f))).mpr (f.weights.bounded ω).2⟩

theorem normalized_moments (f : Family η s) :
    Law.MatchingMoments f.weights.yes f.weights.no
      (fun ω => (f.normalized ω : ℝ)) (fun ω => (f.normalized ω : ℝ)) (s + 2) :=
  f.weights.moments.scale f.weights.bound

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I] [Fintype C]
variable [Nonempty G] [Nonempty I]

noncomputable abbrev setup (f : Family η s) (hm : f.d ≤ Fintype.card S)
    (hRmass : 2 * f.H0 * f.weights.bound ^ f.d ≤ (f.d : ℝ) * Fintype.card I) :
    Setup S f.weights.Carrier where
  d := f.d
  H0 := f.H0
  R := Fintype.card I
  M := f.weights.bound
  value := f.weights.value
  d_ge_three := by have := f.d_ge_four; omega
  enough_special := hm
  H0_nonneg := f.H0_pos.le
  R_pos := by exact_mod_cast Fintype.card_pos
  bounded := f.weights.bounded
  valid := by
    have hd₀ : (0 : ℝ) < f.d := by exact_mod_cast (show 0 < f.d from lt_of_lt_of_le (by norm_num) f.d_ge_four)
    have hI₀ : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    rw [div_le_iff₀ (mul_pos hd₀ hI₀)]
    nlinarith

theorem cost_separation (f : Family η s) (hη : 0 < η)
    (hm : f.d ≤ Fintype.card S)
    (hRmass : 2 * f.H0 * f.weights.bound ^ f.d ≤ (f.d : ℝ) * Fintype.card I)
    (hS : (Fintype.card S : ℝ) = (f.d : ℝ) * Fintype.card G)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * Fintype.card I)
    {ell : ℝ} (hEll₀ : 0 ≤ ell) (hEll₂ : ell ≤ 2) :
    let k := f.setup (S := S) (I := I) hm hRmass
    let offset := ell * Fintype.card G * ((Fintype.card I : ℝ) - 1)
    (k.law (C := C) f.weights.yes).prob
        {σ | Testing.yesCost η (Fintype.card S) offset < k.instanceOpt (G := G) (I := I) ell σ} ≤ 1 / 100 ∧
      (k.law (C := C) f.weights.no).prob
        {σ | k.instanceOpt (G := G) (I := I) ell σ < Testing.noCost η (Fintype.card S) offset} ≤ 1 / 100 := by
  classical
  let k := f.setup (S := S) (I := I) hm hRmass
  let m : ℝ := Fintype.card S
  let A : ℝ := Fintype.card G
  let R : ℝ := Fintype.card I
  let a := 1 / (1 + 1 / (2 * (f.d : ℝ)))
  let u := η * m / 150
  let z := η * m / 300
  let b := η * m / 50
  let offset := ell * A * (R - 1)
  have hm₀ : 0 < m := by
    have hd := f.d_ge_four
    dsimp [m]
    exact_mod_cast (show 0 < Fintype.card S by omega)
  have hd₀ : (0 : ℝ) < f.d := by
    have hd := f.d_ge_four
    exact_mod_cast (show 0 < f.d by omega)
  have hR₀ : 0 < R := by dsimp [R]; exact_mod_cast Fintype.card_pos
  have hu : 0 < u := by dsimp [u]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpow : 1 / 2 ≤ a ^ f.d := HardDistribution.Setup.floor_power f.d (by have := f.d_ge_four; omega)
  have hden : 0 < 1 + f.H0 * a ^ f.d := by have := f.H0_pos; positivity
  have hdenlarge : 30000 ≤ η * (1 + f.H0 * a ^ f.d) := by
    have hp : 30000 ≤ η * f.H0 * a ^ f.d := by rw [f.H0_product]; linarith
    nlinarith
  have hunc : (m / (1 + f.H0 * a ^ f.d)) / u ≤ 1 / 200 := by
    rw [div_le_iff₀ hu, div_le_iff₀ hden]
    have hscaled := mul_le_mul_of_nonneg_right hdenlarge hm₀.le
    dsimp [u]
    nlinarith
  have hstars : (((Fintype.card C : ℝ) * f.H0 / ((f.d : ℝ) * R))) / z ≤ 1 / 200 := by
    have heq : (Fintype.card C : ℝ) * f.H0 / ((f.d : ℝ) * R) = f.H0 * m / f.d := by
      rw [hC]
      dsimp [m, R]
      field_simp
    rw [heq, div_le_iff₀ hz, div_le_iff₀ hd₀]
    have hscaled := mul_le_mul_of_nonneg_right f.star_budget hm₀.le
    dsimp [z]
    nlinarith
  have hyes := k.yes_cost_probability (G := G) (I := I) (C := C) f.weights.yes hEll₂
    f.weights.mean_yes a ha f.weights.yes_support hC u z hu hz
  have hthreshold :
      offset + 2 * A + m - 2 + u + 2 * z ≤ Testing.yesCost η m offset := by
    have hscaled := mul_le_mul_of_nonneg_right f.cluster_budget (show 0 ≤ A by positivity)
    have hmA : m = (f.d : ℝ) * A := hS
    dsimp [u, z, Testing.yesCost]
    rw [hmA]
    nlinarith
  have hy : (k.law (C := C) f.weights.yes).prob
      {σ | Testing.yesCost η m offset < k.instanceOpt (G := G) (I := I) ell σ} ≤ 1 / 100 := by
    apply ((Law.prob_mono _ ?_).trans hyes).trans
    · change (m / (1 + f.H0 * a ^ f.d)) / u +
        ((Fintype.card C : ℝ) * f.H0 / ((f.d : ℝ) * R)) / z ≤ 1 / 100
      linarith
    · intro σ hσ
      exact lt_of_le_of_lt hthreshold hσ
  have hn := k.no_cost_probability (G := G) (I := I) (C := C) f.weights.no hEll₂ b hb
  have hnoerror : ((Fintype.card S : ℝ) * f.weights.no.prob {ω | 0 < f.weights.value ω}) / b ≤ 1 / 200 := by
    calc
      _ ≤ (m * (η / 10000)) / b :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left f.weights.no_positive hm₀.le) hb.le
      _ = 1 / 200 := by dsimp [b]; field_simp; ring
  have hnthreshold : Testing.noCost η m offset ≤ ell * A * R + 2 * m - 2 - b := by
    dsimp [Testing.noCost, offset, b]
    nlinarith [mul_nonneg hEll₀ (show 0 ≤ A by positivity)]
  have hn' : (k.law (C := C) f.weights.no).prob
      {σ | k.instanceOpt (G := G) (I := I) ell σ < Testing.noCost η m offset} ≤ 1 / 100 := by
    apply ((Law.prob_mono _ ?_).trans hn).trans
    · exact hnoerror.trans (by norm_num)
    · intro σ hσ
      exact lt_of_lt_of_le hσ hnthreshold
  exact ⟨hy, hn'⟩

end Family

end HardFamily

end SteinerLowerBound
