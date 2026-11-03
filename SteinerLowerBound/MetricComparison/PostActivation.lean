module

public import SteinerLowerBound.MetricComparison.LocalComparison

@[expose] public section

namespace SteinerLowerBound.MetricComparison

open scoped BigOperators Classical
open HardDistribution

variable {S Ω : Type*} [Fintype S]

theorem two_kernel_affinity (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S)
    (h : History S) (hv : h.Valid) (u : S) (hf : h.Fresh u)
    (hp : h.positive.card = 2) :
    1 - Law.affinity ((History.staticObserver k w).kernel h u)
      ((gatedObserver k w hsmall).kernel h u) ≤
        16384 * scale k ^ 2 / ((Fintype.card S : ℝ) * k.R ^ 2) := by
  classical
  let A := starEvidence k w h
  let B := activationMass k w h
  let N := starEvidence k w (h.update u true)
  let Z := beta S + A
  let G := beta S + A - B
  have hL : 0 < scale k := scale_pos k
  have hRp : 0 < k.R := k.R_pos
  have hβ : 0 < beta S := beta_pos (by omega)
  have hm' : (16 : ℝ) ≤ Fintype.card S := by exact_mod_cast hm
  have hm₀ : (0 : ℝ) < Fintype.card S := by linarith
  have hA : 0 ≤ A := starEvidence_nonneg k w h
  have hB : 0 ≤ B := activationMass_nonneg k w h
  have hN : 0 ≤ N := starEvidence_nonneg k w (h.update u true)
  have hAB : A ≤ B := starEvidence_le_activation k w h hv
  have hBu : B ≤ beta S * scale k / k.R := activationMass_le k w h hv (by omega)
  have hBhalf : B ≤ beta S / 2 := by
    apply hBu.trans
    apply (div_le_iff₀ hRp).mpr
    have hh := mul_le_mul_of_nonneg_left hR hβ.le
    nlinarith
  have hZ : 0 < Z := by dsimp only [Z]; linarith
  have hGhalf : beta S / 2 ≤ G := by dsimp only [G]; linarith
  have hG : 0 < G := by linarith
  have hv' := h.update_valid u true hv hf
  have hc' : (h.update u true).positive.card = 3 := by
    simp only [History.update, ↓reduceIte, Finset.card_insert_of_notMem hf.1, hp]
  have hNu : N ≤ beta S * scale k / (k.R * Fintype.card S) :=
    (starEvidence_le_prescribed k w (h.update u true)).trans
      (prescribed_three k w (by omega) _ hc')
  have hse : (History.staticObserver k w).evidence h = Z := by
    rw [static_evidence_nonempty k w h (by omega), filler_evidence_two _ h hv hp]
  have hge : (gatedObserver k w hsmall).evidence h = G :=
    gated_evidence_two k w hsmall h hv hp
  have hsn : (History.staticObserver k w).evidence (h.update u true) = N :=
    static_evidence_many k w _ (by omega)
  have hgn : (gatedObserver k w hsmall).evidence (h.update u true) = N :=
    gated_evidence_many k w hsmall _ hv' (by omega)
  have hsr : (History.staticObserver k w).positiveRate h u = N / Z := by
    simp only [Observer.positiveRate, hse, hsn, hv, hf, hZ, and_self, ↓reduceIte]
  have hgr : (gatedObserver k w hsmall).positiveRate h u = N / G := by
    simp only [Observer.positiveRate, hge, hgn, hv, hf, hG, and_self, ↓reduceIte]
  have hx₀ : 0 ≤ N / Z := div_nonneg hN hZ.le
  have hy₀ : 0 ≤ N / G := div_nonneg hN hG.le
  have hx₁ : N / Z ≤ 1 := by rw [← hsr]; exact Observer.positiveRate_le_one _ _ _
  have hy₁ : N / G ≤ 1 := by rw [← hgr]; exact Observer.positiveRate_le_one _ _ _
  have hybound : N / G ≤ 2 * scale k / (k.R * Fintype.card S) := by
    apply (div_le_iff₀ hG).mpr
    have hh := mul_le_mul_of_nonneg_left hGhalf
      (show 0 ≤ 2 * scale k / (k.R * Fintype.card S) by positivity)
    apply hNu.trans
    convert hh using 1 <;> ring
  have hyhalf : N / G ≤ 1 / 2 := by
    apply hybound.trans
    apply (div_le_iff₀ (mul_pos hRp hm₀)).mpr
    have hh := mul_nonneg hRp.le (show 0 ≤ (Fintype.card S : ℝ) - 1 by linarith)
    nlinarith
  have hr : 0 ≤ scale k / k.R := by positivity
  have hratio : B / Z ≤ scale k / k.R := by
    apply (div_le_iff₀ hZ).mpr
    have hZβ : beta S ≤ Z := by dsimp only [Z]; linarith
    have hh := mul_le_mul_of_nonneg_left hZβ hr
    apply hBu.trans
    convert hh using 1 <;> ring
  have hdiff : |N / Z - N / G| ≤ (scale k / k.R) * (N / G) := by
    have hid : N / Z - N / G = -(B / Z) * (N / G) := by
      field_simp [hZ.ne', hG.ne']
      dsimp only [Z, G]
      ring
    rw [hid, abs_mul, abs_neg, abs_of_nonneg (div_nonneg hB hZ.le),
      abs_of_nonneg hy₀]
    exact mul_le_mul_of_nonneg_right hratio hy₀
  have hh := bernoulli_relative_bound (N / Z) (N / G) (scale k / k.R)
    hx₀ hx₁ hy₀ hy₁ hr hyhalf hdiff
  simp only [Observer.kernel, hsr, hgr]
  apply hh.trans
  calc
    _ ≤ (scale k / k.R) ^ 2 *
        (2 * scale k / (k.R * Fintype.card S)) :=
      mul_le_mul_of_nonneg_left hybound (sq_nonneg _)
    _ = (2 * scale k ^ 2 / ((Fintype.card S : ℝ) * k.R ^ 2)) *
        (scale k / k.R) := by ring
    _ ≤ (2 * scale k ^ 2 / ((Fintype.card S : ℝ) * k.R ^ 2)) * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (div_le_one hRp).mpr
      linarith
    _ ≤ _ := by
      rw [mul_one]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (scale k)]

theorem many_kernel_equal (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (h : History S) (hv : h.Valid) (u : S) (hf : h.Fresh u)
    (hp : 3 ≤ h.positive.card) :
    (History.staticObserver k w).kernel h u = (gatedObserver k w hsmall).kernel h u := by
  have hv' := h.update_valid u true hv hf
  have hp' : 3 ≤ (h.update u true).positive.card := by
    simp only [History.update, ↓reduceIte, Finset.card_insert_of_notMem hf.1]
    omega
  have he : (History.staticObserver k w).positiveRate h u =
      (gatedObserver k w hsmall).positiveRate h u := by
    simp only [Observer.positiveRate, static_evidence_many k w h hp,
      static_evidence_many k w (h.update u true) hp',
      gated_evidence_many k w hsmall h hv hp,
      gated_evidence_many k w hsmall (h.update u true) hv' hp']
  simp only [Observer.kernel, he]

theorem local_kernel_affinity (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S)
    (h : History S) (hv : h.Valid) (u : S) (hf : h.Fresh u) :
    1 - Law.affinity ((History.staticObserver k w).kernel h u)
      ((gatedObserver k w hsmall).kernel h u) ≤
        16384 * scale k ^ 2 / ((Fintype.card S : ℝ) * k.R ^ 2) := by
  by_cases hp : h.positive.card ≤ 1
  · exact low_kernel_affinity k w hsmall hR hm h hv u hf hp
  by_cases hp₂ : h.positive.card = 2
  · exact two_kernel_affinity k w hsmall hR hm h hv u hf hp₂
  · rw [many_kernel_equal k w hsmall h hv u hf (by omega), Law.affinity_self]
    simp only [sub_self]
    positivity

end SteinerLowerBound.MetricComparison
