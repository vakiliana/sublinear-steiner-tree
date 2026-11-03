module

public import SteinerUpperBound.Covers.Sampling

@[expose] public section

namespace SteinerUpperBound.Covers.Rejection

open SteinerLowerBound
open scoped Classical BigOperators
open FiniteSampling

variable {U : Type*} [Fintype U] [Nonempty U]

noncomputable def lowerEstimate (k s t : ℕ) (ξ : ℝ) : ℝ :=
  (1 - ξ / 2) * k * s / t

noncomputable def upperEstimate (k s t : ℕ) (ξ : ℝ) : ℝ :=
  (1 + ξ / 2) * k * s / t

def Calibrated (b : U → Bool) (C s : ℕ) (ξ : ℝ)
    (rows : Fin s → Fin C → U) : Prop :=
  (1 - ξ) * (retained b).card ≤
      lowerEstimate (Fintype.card U) s (proposals b C s rows) ξ ∧
    lowerEstimate (Fintype.card U) s (proposals b C s rows) ξ ≤ (retained b).card ∧
    ((retained b).card : ℝ) ≤
      upperEstimate (Fintype.card U) s (proposals b C s rows) ξ ∧
    upperEstimate (Fintype.card U) s (proposals b C s rows) ξ ≤
      (1 + ξ) * (retained b).card

theorem ratio_calibration (p s t ξ : ℝ) (hp : 0 < p) (hs : 0 < s)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (h :
      |p * t - s| ≤ (ξ / 4) * s) :
    0 < t ∧
      (1 - ξ) * p ≤ (1 - ξ / 2) * s / t ∧
      (1 - ξ / 2) * s / t ≤ p ∧
      p ≤ (1 + ξ / 2) * s / t ∧
      (1 + ξ / 2) * s / t ≤ (1 + ξ) * p := by
  have hlo : (1 - ξ / 4) * s ≤ p * t := by linarith [(abs_le.mp h).1]
  have hhi : p * t ≤ (1 + ξ / 4) * s := by linarith [(abs_le.mp h).2]
  have hpt : 0 < p * t := by nlinarith
  have ht : 0 < t := ((mul_pos_iff.mp hpt).resolve_right (by intro h; linarith)).2
  refine ⟨ht, ?_, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ ht).mpr
    have hc : (1 - ξ) * (1 + ξ / 4) ≤ 1 - ξ / 2 := by nlinarith [sq_nonneg ξ]
    have ha := mul_le_mul_of_nonneg_left hhi (sub_nonneg.mpr hξ1)
    have hb := mul_le_mul_of_nonneg_right hc hs.le
    nlinarith
  · apply (div_le_iff₀ ht).mpr
    nlinarith
  · apply (le_div_iff₀ ht).mpr
    nlinarith
  · apply (div_le_iff₀ ht).mpr
    have hc : 1 + ξ / 2 ≤ (1 + ξ) * (1 - ξ / 4) := by
      nlinarith [mul_nonneg hξ.le (sub_nonneg.mpr hξ1)]
    have ha := mul_le_mul_of_nonneg_left hlo (by linarith : 0 ≤ 1 + ξ)
    have hb := mul_le_mul_of_nonneg_right hc hs.le
    nlinarith

theorem calibrated_of_deviation (b : U → Bool) (hb : (retained b).Nonempty)
    (C s : ℕ) (hs : 0 < s) (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (rows : Fin s → Fin C → U)
    (h : |hitRate b * proposals b C s rows - s| ≤ (ξ / 4) * s) :
    Calibrated b C s ξ rows := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  obtain ⟨ht, h₁, h₂, h₃, h₄⟩ := ratio_calibration
    (hitRate b) s (proposals b C s rows) ξ (hitRate_pos b hb) hsR hξ hξ1 h
  have hk : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have he : (Fintype.card U : ℝ) * hitRate b = (retained b).card := by
    unfold hitRate
    field_simp
  have ha := mul_le_mul_of_nonneg_left h₁ hk.le
  have hb' := mul_le_mul_of_nonneg_left h₂ hk.le
  have hc := mul_le_mul_of_nonneg_left h₃ hk.le
  have hd := mul_le_mul_of_nonneg_left h₄ hk.le
  have he₁ : (Fintype.card U : ℝ) * ((1 - ξ) * hitRate b) =
      (1 - ξ) * (retained b).card := by rw [mul_left_comm, he]
  have he₄ : (Fintype.card U : ℝ) * ((1 + ξ) * hitRate b) =
      (1 + ξ) * (retained b).card := by rw [mul_left_comm, he]
  rw [he₁] at ha
  rw [he] at hb' hc
  rw [he₄] at hd
  simpa only [Calibrated, lowerEstimate, upperEstimate, mul_div_assoc, mul_assoc,
    mul_left_comm, mul_comm] using And.intro ha (And.intro hb' (And.intro hc hd))

theorem calibration_failure (b : U → Bool) (hb : (retained b).Nonempty)
    (C s : ℕ) (hs : 0 < s) (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hcap : (1 - hitRate b) ^ C ≤ ξ / 8) :
    (poolLaw C s).prob {rows | ¬ Calibrated b C s ξ rows} ≤
      8 / ((ξ / 4) ^ 2 * s) := by
  have hsub : {rows | ¬ Calibrated b C s ξ rows} ⊆
      {rows | (ξ / 4) * s < |hitRate b * proposals b C s rows - s|} := by
    intro rows hrows
    by_contra hn
    exact hrows (calibrated_of_deviation b hb C s hs ξ hξ hξ1 rows (le_of_not_gt hn))
  apply (Law.prob_mono _ hsub).trans
  exact calibration_concentration b hb C s hs (ξ / 4) (by positivity)
    (by convert hcap using 1 <;> ring)

noncomputable def calibrationSamples (β ξ : ℝ) : ℕ :=
  ⌈256 / (β * ξ ^ 2)⌉₊

noncomputable def proposalRowCap (k s : ℕ) (β ξ : ℝ) : ℕ :=
  ⌈(k : ℝ) * Real.log (16 * (s : ℝ) / (β * ξ))⌉₊

theorem calibrationSamples_pos (β ξ : ℝ) (hβ : 0 < β) (hξ : 0 < ξ) :
    0 < calibrationSamples β ξ := by
  have hpos : (0 : ℝ) < 256 / (β * ξ ^ 2) := by positivity
  have h := hpos.trans_le (Nat.le_ceil (256 / (β * ξ ^ 2)))
  exact_mod_cast h

theorem proposal_cap_survival (b : U → Bool) (hb : (retained b).Nonempty)
    (s : ℕ) (hs : 0 < s) (β ξ : ℝ) (hβ : 0 < β) (hξ : 0 < ξ) :
    (1 - hitRate b) ^ proposalRowCap (Fintype.card U) s β ξ ≤
      β * ξ / (16 * s) := by
  have hk : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hlog : 0 < 16 * (s : ℝ) / (β * ξ) := by positivity
  have hC := Nat.le_ceil
    ((Fintype.card U : ℝ) * Real.log (16 * (s : ℝ) / (β * ξ)))
  have he : Real.exp
      (-(proposalRowCap (Fintype.card U) s β ξ : ℝ) / Fintype.card U) ≤
        β * ξ / (16 * s) := by
    calc
      _ ≤ Real.exp (-Real.log (16 * (s : ℝ) / (β * ξ))) := by
        apply Real.exp_le_exp.mpr
        apply (div_le_iff₀ hk).mpr
        dsimp [proposalRowCap]
        nlinarith
      _ = _ := by rw [Real.exp_neg, Real.exp_log hlog]; field_simp
  rw [← first_failure b hb]
  exact (first_failure_exp b hb _).trans he

theorem sampler_and_calibration (b : U → Bool) (hb : (retained b).Nonempty)
    (β ξ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    let s := calibrationSamples β ξ
    let C := proposalRowCap (Fintype.card U) s β ξ
    (poolLaw C s).prob
      {rows | ¬ Successful b C s rows ∨ ¬ Calibrated b C s ξ rows} ≤ β := by
  classical
  dsimp only
  let s := calibrationSamples β ξ
  let C := proposalRowCap (Fintype.card U) s β ξ
  have hs : 0 < s := calibrationSamples_pos β ξ hβ hξ
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hq := proposal_cap_survival b hb s hs β ξ hβ hξ
  have hqscaled :
      (1 - hitRate b) ^ C * (16 * (s : ℝ)) ≤ β * ξ :=
    (le_div_iff₀ (by positivity)).mp hq
  have hqsmall : (1 - hitRate b) ^ C ≤ ξ / 8 := by
    have hβξ := mul_le_mul_of_nonneg_right hβ1 hξ.le
    have hq0 := pow_nonneg (sub_nonneg.mpr (hitRate_le_one b)) C
    nlinarith
  have hsample : 256 ≤ (s : ℝ) * (β * ξ ^ 2) :=
    (div_le_iff₀ (by positivity)).mp (Nat.le_ceil (256 / (β * ξ ^ 2)))
  have hcheb : 8 / ((ξ / 4) ^ 2 * (s : ℝ)) ≤ β / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hfail : (poolLaw C s).prob {rows | ¬ Successful b C s rows} ≤ β / 16 := by
    apply (pool_failure_le b hb C s).trans
    have hβξ := mul_le_mul_of_nonneg_left hξ1 hβ.le
    nlinarith
  have hcal := (calibration_failure b hb C s hs ξ hξ hξ1 hqsmall).trans hcheb
  exact (Law.prob_union_le _ _ _).trans ((add_le_add hfail hcal).trans (by linarith))

end SteinerUpperBound.Covers.Rejection
