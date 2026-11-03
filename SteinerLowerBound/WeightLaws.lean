module

public import SteinerLowerBound.MomentMatching

@[expose] public section

/-!
# Existence of the weight laws

This uses an inductive alternative to the interpolation proof in the paper.
If two laws match through order `s`, mixing each with a small affine copy of
the other cancels moment `s + 1`. The translation keeps the YES support away
from zero; taking the dilation large makes the added mass and mean small.
-/

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace WeightConstruction

theorem affine_power (L z : ℝ) (n : ℕ) :
    (1 + L * z) ^ n =
      ∑ j ∈ Finset.range (n + 1), ((n.choose j : ℝ) * L ^ j) * z ^ j := by
  rw [add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_pow, one_pow, mul_one]
  ring

theorem affine_difference {Ω : Type*} [Fintype Ω] {μ ν : Law Ω}
    {x : Ω → ℝ} {s : ℕ} (h : Law.MatchingMoments μ ν x x s)
    (L : ℝ) (n : ℕ) (hn : n ≤ s + 1) :
    μ.expect (fun ω => (1 + L * x ω) ^ n) -
        ν.expect (fun ω => (1 + L * x ω) ^ n) =
      L ^ n * (μ.expect (fun ω => x ω ^ n) - ν.expect (fun ω => x ω ^ n)) := by
  cases n with
  | zero => simp
  | succ k =>
      have expansion (z : ℝ) :
          (1 + L * z) ^ (k + 1) =
            (∑ j ∈ Finset.range (k + 1), ((k + 1).choose j : ℝ) * L ^ j * z ^ j) +
              L ^ (k + 1) * z ^ (k + 1) := by
        rw [affine_power, Finset.sum_range_succ]
        simp
      simp_rw [expansion, Law.expect_add, Law.expect_sum]
      have hsum :
          (∑ j ∈ Finset.range (k + 1),
            μ.expect (fun ω => ((k + 1).choose j : ℝ) * L ^ j * x ω ^ j)) =
          ∑ j ∈ Finset.range (k + 1),
            ν.expect (fun ω => ((k + 1).choose j : ℝ) * L ^ j * x ω ^ j) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp_rw [mul_comm (_ * L ^ j), Law.expect_mul_const]
        rw [h j (by have := Finset.mem_range.mp hj; omega)]
      rw [hsum]
      simp_rw [mul_comm (L ^ (k + 1)), Law.expect_mul_const]
      ring

noncomputable def liftedValue {Ω : Type*} (x : Ω → ℝ) (L : ℝ) : Ω ⊕ Ω → ℝ :=
  Sum.elim x (fun ω => 1 + L * x ω)

noncomputable def extendYes {Ω : Type*} [Fintype Ω] (μ ν : Law Ω)
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : Law (Ω ⊕ Ω) :=
  Law.mix (1 - p) (sub_nonneg.mpr hp₁) (by linarith)
    (μ.map Sum.inl) (ν.map Sum.inr)

noncomputable def extendNo {Ω : Type*} [Fintype Ω] (μ ν : Law Ω)
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : Law (Ω ⊕ Ω) :=
  Law.mix (1 - p) (sub_nonneg.mpr hp₁) (by linarith)
    (ν.map Sum.inl) (μ.map Sum.inr)

theorem expect_extend_yes {Ω : Type*} [Fintype Ω] (μ ν : Law Ω)
    (x : Ω → ℝ) (L p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (f : ℝ → ℝ) :
    (extendYes μ ν p hp₀ hp₁).expect (fun z => f (liftedValue x L z)) =
      (1 - p) * μ.expect (fun ω => f (x ω)) +
        p * ν.expect (fun ω => f (1 + L * x ω)) := by
  simp [extendYes, Law.expect_mix, Law.expect_map, liftedValue]

theorem expect_extend_no {Ω : Type*} [Fintype Ω] (μ ν : Law Ω)
    (x : Ω → ℝ) (L p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (f : ℝ → ℝ) :
    (extendNo μ ν p hp₀ hp₁).expect (fun z => f (liftedValue x L z)) =
      (1 - p) * ν.expect (fun ω => f (x ω)) +
        p * μ.expect (fun ω => f (1 + L * x ω)) := by
  simp [extendNo, Law.expect_mix, Law.expect_map, liftedValue]

theorem extend_moments {Ω : Type*} [Fintype Ω] {μ ν : Law Ω}
    {x : Ω → ℝ} {s : ℕ} (h : Law.MatchingMoments μ ν x x s)
    (L p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hp : p * (1 + L ^ (s + 1)) = 1) :
    Law.MatchingMoments (extendYes μ ν p hp₀ hp₁) (extendNo μ ν p hp₀ hp₁)
      (liftedValue x L) (liftedValue x L) (s + 1) := by
  intro j hj
  rw [expect_extend_yes μ ν x L p hp₀ hp₁ (fun z => z ^ j),
    expect_extend_no μ ν x L p hp₀ hp₁ (fun z => z ^ j)]
  have ha := affine_difference h L j hj
  apply sub_eq_zero.mp
  have hd :
      ((1 - p) * μ.expect (fun ω => x ω ^ j) +
          p * ν.expect (fun ω => (1 + L * x ω) ^ j)) -
        ((1 - p) * ν.expect (fun ω => x ω ^ j) +
          p * μ.expect (fun ω => (1 + L * x ω) ^ j)) =
      (1 - p - p * L ^ j) *
        (μ.expect (fun ω => x ω ^ j) - ν.expect (fun ω => x ω ^ j)) := by
    calc
      _ = (1 - p) * (μ.expect (fun ω => x ω ^ j) - ν.expect (fun ω => x ω ^ j)) -
          p * (μ.expect (fun ω => (1 + L * x ω) ^ j) -
            ν.expect (fun ω => (1 + L * x ω) ^ j)) := by ring
      _ = _ := by rw [ha]; ring
  rw [hd]
  by_cases hj' : j ≤ s
  · rw [h j hj', sub_self, mul_zero]
  · have hjeq : j = s + 1 := by omega
    subst j
    have hz : 1 - p - p * L ^ (s + 1) = 0 := by nlinarith [hp]
    rw [hz, zero_mul]

structure RawWeights (s : ℕ) (δ κ : ℝ) where
  Carrier : Type
  [finite : Fintype Carrier]
  yes : Law Carrier
  no : Law Carrier
  value : Carrier → ℝ
  nonneg : ∀ ω, 0 ≤ value ω
  moments : Law.MatchingMoments yes no value value s
  yes_support : ∀ ω, 0 < yes.mass ω → 1 ≤ value ω
  mean_lower : 1 ≤ yes.expect value
  mean_upper : yes.expect value ≤ 1 + κ
  no_positive : no.prob {ω | 0 < value ω} ≤ δ

attribute [instance] RawWeights.finite

noncomputable def base (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) :
    RawWeights 1 δ κ := by
  let p := δ / (1 + δ)
  let B := (1 + δ) / δ
  have hp₀ : 0 ≤ p := le_of_lt (div_pos hδ (by linarith))
  have hp₁ : p ≤ 1 := (div_le_one (by linarith : 0 < 1 + δ)).mpr (by linarith)
  have hB : 0 < B := div_pos (by linarith) hδ
  have hpB : p * B = 1 := by
    dsimp [p, B]
    field_simp
  have hpδ : p ≤ δ := by
    dsimp [p]
    rw [div_le_iff₀ (by linarith : 0 < 1 + δ)]
    nlinarith
  let x : Fin 3 → ℝ := fun i => if i = 0 then 0 else if i = 1 then 1 else B
  let μ : Law (Fin 3) := Law.pure 1
  let ν : Law (Fin 3) := Law.mix p hp₀ hp₁ (Law.pure 2) (Law.pure 0)
  have hx₀ : ∀ i, 0 ≤ x i := by
    intro i
    dsimp [x]
    split_ifs <;> positivity
  have hμ : μ.expect x = 1 := by simp [μ, x]
  have hν : ν.expect x = 1 := by
    simp [ν, Law.expect_mix, x, hpB]
  refine
    { Carrier := Fin 3
      yes := μ
      no := ν
      value := x
      nonneg := hx₀
      moments := ?_
      yes_support := ?_
      mean_lower := hμ.ge
      mean_upper := by rw [hμ]; linarith
      no_positive := ?_ }
  · intro j hj
    interval_cases j
    · simp
    · simpa only [pow_one] using hμ.trans hν.symm
  · intro i hi
    have hi' : i = 1 := by
      by_contra h
      simp [μ, Law.pure, h] at hi
    simp [x, hi']
  · simpa [ν, Law.prob_mix, Law.prob_pure, x, hB] using hpδ

theorem raw_weights_exist (s : ℕ) (hs : 1 ≤ s) (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) :
    Nonempty (RawWeights s δ κ) := by
  induction s generalizing δ κ with
  | zero => omega
  | succ s ih =>
      by_cases hs₀ : s = 0
      · subst s
        exact ⟨base δ κ hδ hκ⟩
      obtain ⟨w⟩ := ih (by omega) (δ / 2) (κ / 2) (by linarith) (by linarith)
      let m := w.yes.expect w.value
      have hm₀ : 0 ≤ m := le_trans (by norm_num) w.mean_lower
      obtain ⟨L, hL⟩ := exists_gt (max (max (1 : ℝ) (2 / δ)) (2 * (m + 1) / κ))
      have hL₁ : 1 < L :=
        (le_trans (le_max_left _ _) (le_max_left _ _)).trans_lt hL
      have hLδ : 2 / δ < L :=
        (le_trans (le_max_right _ _) (le_max_left _ _)).trans_lt hL
      have hLκ : 2 * (m + 1) / κ < L := (le_max_right _ _).trans_lt hL
      have hL₀ : 0 < L := by linarith
      let q := 1 / (1 + L ^ (s + 1))
      have hden : 0 < 1 + L ^ (s + 1) := by positivity
      have hq₀ : 0 ≤ q := (one_div_pos.mpr hden).le
      have hq₂ : q ≤ 1 / L ^ 2 := by
        apply one_div_le_one_div_of_le (pow_pos hL₀ 2)
        have := pow_le_pow_right₀ hL₁.le (show 2 ≤ s + 1 by omega)
        linarith
      have hqL : q ≤ 1 / L :=
        hq₂.trans (one_div_le_one_div_of_le hL₀ (by nlinarith))
      have hq₁ : q ≤ 1 := hqL.trans ((div_le_one hL₀).mpr hL₁.le)
      have hqδ : q ≤ δ / 2 := by
        apply hqL.trans
        rw [div_le_iff₀ hL₀]
        have := (div_le_iff₀ hδ).mp hLδ.le
        nlinarith
      have hinc :
          q * (1 + (L - 1) * m) ≤ κ / 2 := by
        calc
          _ ≤ q * (L * (m + 1)) := by
            apply mul_le_mul_of_nonneg_left _ hq₀
            nlinarith
          _ ≤ (1 / L ^ 2) * (L * (m + 1)) :=
            mul_le_mul_of_nonneg_right hq₂ (by positivity)
          _ = (m + 1) / L := by field_simp
          _ ≤ κ / 2 := by
            rw [div_le_iff₀ hL₀]
            have := (div_le_iff₀ hκ).mp hLκ.le
            nlinarith
      have hmom := extend_moments w.moments L q hq₀ hq₁
        (by dsimp [q]; field_simp)
      have hcommon : w.no.expect w.value = m := by
        simpa [m] using (w.moments 1 (by omega)).symm
      have hmean :
          (extendYes w.yes w.no q hq₀ hq₁).expect (liftedValue w.value L) =
            m + q * (1 + (L - 1) * m) := by
        rw [show (liftedValue w.value L) = (fun z => (fun a : ℝ => a) (liftedValue w.value L z))
          from rfl, expect_extend_yes w.yes w.no w.value L q hq₀ hq₁ (fun a => a)]
        simp only [Law.expect_add, Law.expect_const]
        simp_rw [mul_comm L, Law.expect_mul_const]
        rw [hcommon]
        dsimp [m]
        ring
      refine ⟨
        { Carrier := w.Carrier ⊕ w.Carrier
          yes := extendYes w.yes w.no q hq₀ hq₁
          no := extendNo w.yes w.no q hq₀ hq₁
          value := liftedValue w.value L
          nonneg := ?_
          moments := hmom
          yes_support := ?_
          mean_lower := ?_
          mean_upper := ?_
          no_positive := ?_ }⟩
      · intro z
        cases z with
        | inl a => exact w.nonneg a
        | inr a =>
            dsimp [liftedValue]
            have := w.nonneg a
            nlinarith
      · intro z hz
        cases z with
        | inl a =>
            have hmass :
                (extendYes w.yes w.no q hq₀ hq₁).mass (.inl a) =
                  (1 - q) * w.yes.mass a := by
              simp [extendYes, Law.mix]
            have hpos : 0 < w.yes.mass a := by
              rw [hmass] at hz
              by_contra h
              have := mul_nonpos_of_nonneg_of_nonpos
                (sub_nonneg.mpr hq₁) (le_of_not_gt h)
              linarith
            exact w.yes_support a hpos
        | inr a =>
            dsimp [liftedValue]
            have := w.nonneg a
            nlinarith
      · rw [hmean]
        have := w.mean_lower
        have := mul_nonneg hq₀ (show 0 ≤ 1 + (L - 1) * m by nlinarith)
        dsimp [m] at *
        linarith
      · rw [hmean]
        have := w.mean_upper
        dsimp [m] at *
        linarith
      · have hleft :
            (Sum.inl : w.Carrier → w.Carrier ⊕ w.Carrier) ⁻¹'
                {z | 0 < liftedValue w.value L z} = {a | 0 < w.value a} := rfl
        have hright :
            (Sum.inr : w.Carrier → w.Carrier ⊕ w.Carrier) ⁻¹'
                {z | 0 < liftedValue w.value L z} = Set.univ := by
          ext a
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, liftedValue,
            Sum.elim_inr, Set.mem_univ, iff_true]
          have := w.nonneg a
          nlinarith
        simp only [extendNo, Law.prob_mix, Law.prob_map, hleft, hright,
          Law.prob_univ, sub_sub_cancel, mul_one]
        have := w.no_positive
        have := mul_nonneg hq₀ (w.no.prob_nonneg {a | 0 < w.value a})
        nlinarith

structure WeightLaws (s : ℕ) (δ lower : ℝ) where
  Carrier : Type
  [finite : Fintype Carrier]
  yes : Law Carrier
  no : Law Carrier
  value : Carrier → ℝ
  bound : ℝ
  bounded : ∀ ω, 0 ≤ value ω ∧ value ω ≤ bound
  moments : Law.MatchingMoments yes no value value s
  mean_yes : yes.expect value = 1
  mean_no : no.expect value = 1
  yes_support : ∀ ω, 0 < yes.mass ω → lower ≤ value ω
  no_positive : no.prob {ω | 0 < value ω} ≤ δ

attribute [instance] WeightLaws.finite

theorem moment_matched_weights_lower (s : ℕ) (hs : 1 ≤ s) (δ κ : ℝ)
    (hδ : 0 < δ) (hκ : 0 < κ) :
    Nonempty (WeightLaws s δ (1 / (1 + κ))) := by
  obtain ⟨w⟩ := raw_weights_exist s hs δ κ hδ hκ
  let m := w.yes.expect w.value
  have hm₀ : 0 < m := lt_of_lt_of_le zero_lt_one w.mean_lower
  have hmκ : m ≤ 1 + κ := w.mean_upper
  let v : w.Carrier → ℝ := fun ω => w.value ω / m
  have hv₀ : ∀ ω, 0 ≤ v ω := fun ω => div_nonneg (w.nonneg ω) hm₀.le
  have hmean : w.yes.expect v = 1 := by
    simp only [v, div_eq_mul_inv, Law.expect_mul_const]
    exact mul_inv_cancel₀ hm₀.ne'
  refine ⟨
    { Carrier := w.Carrier
      yes := w.yes
      no := w.no
      value := v
      bound := ∑ ω, v ω
      bounded := ?_
      moments := w.moments.scale m
      mean_yes := hmean
      mean_no := ?_
      yes_support := ?_
      no_positive := ?_ }⟩
  · intro ω
    exact ⟨hv₀ ω, Finset.single_le_sum (fun a _ => hv₀ a) (Finset.mem_univ ω)⟩
  · have := (w.moments.scale m) 1 hs
    have heq : w.no.expect v = w.yes.expect v := by simpa [v] using this.symm
    exact heq.trans hmean
  · intro ω hω
    dsimp [v]
    rw [le_div_iff₀ hm₀]
    have := w.yes_support ω hω
    have hscale : (1 / (1 + κ)) * m ≤ 1 := by
      simpa [div_eq_mul_inv, mul_comm] using
        (div_le_one (by linarith : 0 < 1 + κ)).mpr hmκ
    linarith
  · have heq : {ω | 0 < v ω} = {ω | 0 < w.value ω} := by
      ext ω
      exact div_pos_iff_of_pos_right hm₀
    rw [heq]
    exact w.no_positive

theorem moment_matched_weights (s : ℕ) (hs : 1 ≤ s) (δ : ℝ) (hδ : 0 < δ) :
    Nonempty (WeightLaws s δ (1 / 2)) := by
  have htwo : (1 : ℝ) + 1 = 2 := by norm_num
  simpa only [htwo] using moment_matched_weights_lower s hs δ 1 hδ (by norm_num)

end WeightConstruction

end SteinerLowerBound
