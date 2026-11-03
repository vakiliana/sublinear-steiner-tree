module

public import SteinerLowerBound.MetricComparison.FillerBounds
public import SteinerLowerBound.MetricComparison.Bernoulli

@[expose] public section

namespace SteinerLowerBound.MetricComparison

open scoped BigOperators Classical
open HardDistribution

variable {S Ω : Type*} [Fintype S]

theorem small_of_R (k : Setup S Ω) (hR : 16 * scale k ≤ k.R) :
    anchorConstant k.d k.H0 k.M / k.R ≤ 1 := by
  apply (div_le_one k.R_pos).mpr
  have := scale_ge_one k
  linarith [anchor_le_scale k]

theorem starEvidence_le_total (k : Setup S Ω) (w : S → Ω) (h : History S) :
    starEvidence k w h ≤ starTotal k.d k.H0 k.R (fun u => k.value (w u)) := by
  apply Finset.sum_le_sum
  intro H _
  split_ifs
  · rfl
  · exact starMass_nonneg k.d k.H0_nonneg k.R_pos.le (fun u => (k.bounded (w u)).1) H

theorem static_evidence_nonempty (k : Setup S Ω) (w : S → Ω) (h : History S)
    (hp : 1 ≤ h.positive.card) :
    (History.staticObserver k w).evidence h =
      fillerEvidence (by have := k.d_ge_three; have := k.enough_special; omega) h +
        starEvidence k w h := by
  have hn : h.positive ≠ ∅ := by intro he; simp [he] at hp
  rw [static_evidence, if_neg hn, sub_zero]

theorem static_evidence_many (k : Setup S Ω) (w : S → Ω) (h : History S)
    (hp : 3 ≤ h.positive.card) :
    (History.staticObserver k w).evidence h = starEvidence k w h := by
  rw [static_evidence_nonempty k w h (by omega), filler_evidence_many _ h hp, zero_add]

theorem activationMass_nonneg (k : Setup S Ω) (w : S → Ω) (h : History S) :
    0 ≤ activationMass k w h := by
  apply Finset.sum_nonneg
  intro H _
  split_ifs
  · exact starMass_nonneg k.d k.H0_nonneg k.R_pos.le (fun u => (k.bounded (w u)).1) H
  · rfl

theorem activationMass_le (k : Setup S Ω) (w : S → Ω) (h : History S)
    (hv : h.Valid) (hp : 2 ≤ h.positive.card) :
    activationMass k w h ≤ beta S * scale k / k.R := by
  have he : h.anchors.card = 2 := by rw [hv.2.2.1, min_eq_right hp]
  apply le_trans _ (prescribed_pair k w h.anchors he)
  apply Finset.sum_le_sum
  intro H _
  change (if h.anchors ⊆ H.val ∧ Disjoint H.val h.blocked then
    starMass k.d k.H0 k.R (fun u => k.value (w u)) H else 0) ≤
      if h.anchors ⊆ H.val then starMass k.d k.H0 k.R (fun u => k.value (w u)) H else 0
  by_cases hh : h.anchors ⊆ H.val
  · simp only [hh, true_and, ↓reduceIte]
    split_ifs
    · rfl
    · exact starMass_nonneg k.d k.H0_nonneg k.R_pos.le (fun u => (k.bounded (w u)).1) H
  · simp only [hh, false_and, ↓reduceIte, le_refl]

theorem starEvidence_le_activation (k : Setup S Ω) (w : S → Ω) (h : History S)
    (hv : h.Valid) :
    starEvidence k w h ≤ activationMass k w h := by
  apply Finset.sum_le_sum
  intro H _
  by_cases hh : h.compatible H.val
  · have hs : h.anchors ⊆ H.val ∧ Disjoint H.val h.blocked :=
      ⟨hv.2.1.trans hh.1, Finset.disjoint_of_subset_right hv.2.2.2.1 hh.2⟩
    simp [hh, hs]
  · simp only [hh, ↓reduceIte]
    split_ifs
    · exact starMass_nonneg k.d k.H0_nonneg k.R_pos.le (fun u => (k.bounded (w u)).1) H
    · rfl

theorem gated_evidence_next_low (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (h : History S) (hv : h.Valid) (u : S) (hf : h.Fresh u)
    (hp : h.positive.card ≤ 1) :
    (gatedObserver k w hsmall).evidence (h.update u true) =
      fillerEvidence (by have := k.d_ge_three; have := k.enough_special; omega)
        (h.update u true) := by
  classical
  have hv' := h.update_valid u true hv hf
  have hcard : (h.update u true).positive.card = h.positive.card + 1 := by
    simp only [History.update, ↓reduceIte, Finset.card_insert_of_notMem hf.1]
  by_cases hp₀ : h.positive.card = 0
  · exact gated_evidence_low k w hsmall _ (by omega)
  · have hp₁ : h.positive.card = 1 := by omega
    have he : activationMass k w (h.update u true) = starEvidence k w (h.update u true) := by
      unfold activationMass starEvidence
      simp only [History.update, ↓reduceIte, hp₁, show (1 : ℕ) < 2 by omega,
        show (1 : ℕ) = 1 by rfl, History.compatible]
      have ha := h.anchors_eq hv (by omega)
      simp only [ha]
    rw [gated_evidence_two k w hsmall _ hv' (by omega), he,
      filler_evidence_two _ _ hv' (by omega)]
    ring

theorem low_evidence_perturbation (k : Setup S Ω) (w : S → Ω)
    (hR : 16 * scale k ≤ k.R)
    (h : History S) (hv : h.Valid) (u : S) (hf : h.Fresh u)
    (hp : h.positive.card ≤ 1) :
    let hm : 2 ≤ Fintype.card S := by have := k.d_ge_three; have := k.enough_special; omega
    let F := fillerEvidence hm h
    let N₀ := fillerEvidence hm (h.update u true)
    let Z := (History.staticObserver k w).evidence h
    let N := (History.staticObserver k w).evidence (h.update u true)
    F / 2 ≤ Z ∧ |Z - F| ≤ 4 * scale k * F / k.R ∧
      |N - N₀| ≤ 4 * scale k * F / (k.R * Fintype.card S) := by
  classical
  dsimp only
  let hm : 2 ≤ Fintype.card S := by have := k.d_ge_three; have := k.enough_special; omega
  let F := fillerEvidence hm h
  have hF : 0 < F := filler_evidence_pos hm h hv (by omega)
  have hm₀ : (0 : ℝ) < Fintype.card S := by exact_mod_cast (show 0 < Fintype.card S by omega)
  have hL : 0 ≤ scale k := (scale_pos k).le
  have hRp : 0 < k.R := k.R_pos
  have hv' := h.update_valid u true hv hf
  have hc' : (h.update u true).positive.card = h.positive.card + 1 := by
    simp only [History.update, ↓reduceIte, Finset.card_insert_of_notMem hf.1]
  have hN := static_evidence_nonempty k w (h.update u true) (by omega)
  have hnum :
      |(History.staticObserver k w).evidence (h.update u true) -
        fillerEvidence hm (h.update u true)| ≤
          4 * scale k * F / (k.R * Fintype.card S) := by
    rw [hN]
    have hne := starEvidence_nonneg k w (h.update u true)
    rw [add_sub_cancel_left, abs_of_nonneg hne]
    apply (starEvidence_le_prescribed k w (h.update u true)).trans
    by_cases hp₀ : h.positive.card = 0
    · apply (prescribed_one k w _ (by omega)).trans
      have hFl : 1 / 4 ≤ F := by
        have hh := filler_evidence_zero_lower hm h hp₀
        dsimp only [F]
        linarith
      have hh := mul_le_mul_of_nonneg_left hFl
        (show 0 ≤ 4 * scale k / (k.R * Fintype.card S) by positivity)
      convert hh using 1 <;> ring
    · have hp₁ : h.positive.card = 1 := by omega
      apply (prescribed_pair k w _ (by omega)).trans
      have hb := (beta_bounds (S := S) hm).2
      have hFl := (filler_evidence_one_bounds hm h hv hp₁).1
      calc
        _ ≤ (1 / (Fintype.card S : ℝ) ^ 2) * scale k / k.R :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hL) k.R_pos.le
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_left hFl
            (show 0 ≤ 4 * scale k / (k.R * Fintype.card S) by positivity)
          convert hh using 1 <;> field_simp <;> ring
  have hden :
      |(History.staticObserver k w).evidence h - F| ≤ 4 * scale k * F / k.R := by
    by_cases hp₀ : h.positive.card = 0
    · have he : h.positive = ∅ := Finset.card_eq_zero.mp hp₀
      rw [static_evidence, if_pos he]
      change |F + starEvidence k w h -
        starTotal k.d k.H0 k.R (fun u => k.value (w u)) - F| ≤ _
      have hs := starEvidence_le_total k w h
      have hsn := starEvidence_nonneg k w h
      have habs : |F + starEvidence k w h -
          starTotal k.d k.H0 k.R (fun u => k.value (w u)) - F| ≤
            starTotal k.d k.H0 k.R (fun u => k.value (w u)) := by
        rw [abs_le]
        constructor <;> linarith
      apply habs.trans ((starTotal_le_scale k w).trans _)
      have hFl : 1 / 4 ≤ F := by
        have hh := filler_evidence_zero_lower hm h hp₀
        dsimp only [F]
        linarith
      have hh := mul_le_mul_of_nonneg_left hFl (show 0 ≤ 4 * scale k / k.R by positivity)
      convert hh using 1 <;> ring
    · have hp₁ : h.positive.card = 1 := by omega
      rw [static_evidence_nonempty k w h (by omega)]
      change |F + starEvidence k w h - F| ≤ _
      rw [add_sub_cancel_left, abs_of_nonneg (starEvidence_nonneg k w h)]
      apply (starEvidence_le_prescribed k w h).trans ((prescribed_one k w h.positive hp₁).trans _)
      have hFl := (filler_evidence_one_bounds hm h hv hp₁).1
      have hh := mul_le_mul_of_nonneg_left hFl (show 0 ≤ 4 * scale k / k.R by positivity)
      convert hh using 1 <;> field_simp <;> ring
  have hz : F / 2 ≤ (History.staticObserver k w).evidence h := by
    have hmul := mul_le_mul_of_nonneg_right hR hF.le
    have hup : 4 * scale k * F / k.R ≤ F / 2 := by
      apply (div_le_iff₀ k.R_pos).mpr
      nlinarith
    have hh := (abs_le.mp (hden.trans hup)).1
    linarith
  exact ⟨hz, hden, hnum⟩

theorem low_kernel_affinity (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S)
    (h : History S) (hv : h.Valid) (u : S) (hf : h.Fresh u)
    (hp : h.positive.card ≤ 1) :
    1 - Law.affinity ((History.staticObserver k w).kernel h u)
      ((gatedObserver k w hsmall).kernel h u) ≤
        16384 * scale k ^ 2 / ((Fintype.card S : ℝ) * k.R ^ 2) := by
  classical
  let hm₂ : 2 ≤ Fintype.card S := by omega
  let F := fillerEvidence hm₂ h
  let N₀ := fillerEvidence hm₂ (h.update u true)
  let Z := (History.staticObserver k w).evidence h
  let N := (History.staticObserver k w).evidence (h.update u true)
  have hF : 0 < F := filler_evidence_pos hm₂ h hv (by omega)
  obtain ⟨hZ, hden, hnum⟩ := low_evidence_perturbation k w hR h hv u hf hp
  have hZ₀ : 0 < Z := by dsimp only [Z]; linarith
  have hrate := filler_rate_bounds hm₂ h hv u hf hp
  have hm₀ : (0 : ℝ) < Fintype.card S := by exact_mod_cast (show 0 < Fintype.card S by omega)
  have hdiff : |N / Z - N₀ / F| ≤ 40 * scale k / (k.R * Fintype.card S) := by
    have hh := ratio_difference_bound N N₀ Z F (Fintype.card S) k.R (4 * scale k)
      hF hZ hm₀ k.R_pos (by have := scale_pos k; positivity)
      (filler_evidence_nonneg hm₂ _) hrate.2 hden hnum
    convert hh using 1 <;> ring
  have hse : (History.staticObserver k w).positiveRate h u = N / Z := by
    simp only [Observer.positiveRate, hv, hf, hZ₀, and_self, ↓reduceIte, N, Z]
  have hge : (gatedObserver k w hsmall).positiveRate h u = N₀ / F := by
    simp only [Observer.positiveRate, gated_evidence_low k w hsmall h hp,
      gated_evidence_next_low k w hsmall h hv u hf hp, hv, hf, hF,
      and_self, ↓reduceIte, F, N₀]
  have hx₀ : 0 ≤ N / Z := by rw [← hse]; exact Observer.positiveRate_nonneg _ _ _
  have hx₁ : N / Z ≤ 1 := by rw [← hse]; exact Observer.positiveRate_le_one _ _ _
  have hy₀ : 0 ≤ N₀ / F := by rw [← hge]; exact Observer.positiveRate_nonneg _ _ _
  have hy₁ : N₀ / F ≤ 1 := by rw [← hge]; exact Observer.positiveRate_le_one _ _ _
  have hym : N₀ / F ≤ 1 / 2 := by
    apply hrate.2.trans
    apply (div_le_iff₀ hm₀).mpr
    have hh : (16 : ℝ) ≤ Fintype.card S := by exact_mod_cast hm
    linarith
  have hh := bernoulli_additive_bound (N / Z) (N₀ / F) (Fintype.card S) k.R (40 * scale k)
    hx₀ hx₁ hy₀ hy₁ (by exact_mod_cast (show 1 ≤ Fintype.card S by omega))
    k.R_pos (by have := scale_pos k; positivity) hrate.1 hym hdiff
  simp only [Observer.kernel, hse, hge]
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [sq_nonneg (scale k)]

end SteinerLowerBound.MetricComparison
