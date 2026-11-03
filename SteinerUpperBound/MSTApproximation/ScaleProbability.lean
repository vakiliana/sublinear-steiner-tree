module

public import SteinerUpperBound.MSTApproximation.ScaleProgram

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry QueryProgram
open scoped Classical BigOperators
open Covers.Rejection
open Covers.FiniteSampling

variable {V U Q : Type*} [Fintype V] [Fintype U]

theorem pool_score_deviation [Nonempty U] (I : Instance V) (e : U → V)
    (he : Function.Injective e) (b : U → Bool) (hb : (retained b).Nonempty)
    (root : U) (a : ℝ) (B C samples : ℕ) (hn : 0 < samples) (xi beta : ℝ)
    (hxi : 0 < xi) (hbudget : 1 ≤ beta * ((samples : ℝ) * xi ^ 2)) :
    (poolLaw C samples).prob {rows | xi <
      |ScoreSampling.empirical (fun y => scoreOn I (selectedPoints e b) a B (e y))
        samples (labels b root C samples rows) - scoreMean I (selectedPoints e b) a B|} ≤
      beta + (samples : ℝ) * Real.exp (-(C : ℝ) / Fintype.card U) := by
  let E : Set (Fin samples → U) := {w | xi <
    |ScoreSampling.empirical (fun y => scoreOn I (selectedPoints e b) a B (e y))
      samples w - scoreMean I (selectedPoints e b) a B|}
  have hclose := pool_uniform_close b hb root C samples E
  have hdiff := (abs_le.mp hclose).2
  rw [Law.prob_map] at hdiff
  have hiid := retained_iid_score_deviation I e he b hb a B samples hn xi beta hxi hbudget
  have hfail := pool_failure_exp b hb C samples
  change (poolLaw C samples).prob ((labels b root C samples) ⁻¹' E) ≤ _
  change (tape (uniformRetained b hb) samples).prob E ≤ beta at hiid
  linarith

def ScaleGood (I : Instance V) (N : Finset V) (a : ℝ) (B : ℕ) (xi : ℝ)
    (r : ScaleAnswer Q) : Prop :=
  r.successful = true ∧ (1 - xi) * (N.card : ℝ) ≤ r.gminus ∧ r.gminus ≤ N.card ∧
    |r.empirical - scoreMean I N a B| ≤ xi

theorem scaleProgram_failure {k : ℕ} (I : Instance V) (b : Q → Bool)
    (e : Fin (k + 1) → V) (he : Function.Injective e) (key : V → Q)
    (a xi beta : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct b cache) (hroot : b (key (e root)) = true)
    (henum : Finset.univ.image e = l.toFinset)
    (hs : 0 < samples) (hx : 0 < xi) (hx1 : xi ≤ 1) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hbudget : 256 ≤ beta * ((samples : ℝ) * xi ^ 2))
    (hrow : Real.exp (-(C : ℝ) / (k + 1)) ≤ beta * xi / (16 * samples)) :
    Code.probability I.weight b (scaleProgram e key a xi B C samples l root cache)
      {o | ¬ ScaleGood I (ComponentExplore.retained b key l.toFinset) a B xi o.value} ≤ beta := by
  classical
  let b' := fun y => b (key (e y))
  have hret : (retained b').Nonempty := ⟨root, by simp [retained, CategoricalCoupling.selected, b', hroot]⟩
  have hcard : (ComponentExplore.retained b key l.toFinset).card = (retained b').card := by
    rw [← enumeration_selectedPoints e key b l henum, selectedPoints_card e he]
  have hsR : (1 : ℝ) ≤ samples := by exact_mod_cast hs
  have hfail := pool_failure_exp b' hret C samples
  have hcap : (1 - hitRate b') ^ C ≤ xi / 8 := by
    have hfirst := first_failure_exp b' hret C
    rw [first_failure b' hret C] at hfirst
    have heq : Fintype.card (Fin (k + 1)) = k + 1 := Fintype.card_fin _
    rw [heq] at hfirst
    simp only [Nat.cast_add, Nat.cast_one] at hfirst
    have hm := (le_div_iff₀ (show (0 : ℝ) < 16 * samples by positivity)).mp hrow
    have hbxi := mul_le_mul_of_nonneg_right hb1 hx.le
    have h0 := pow_nonneg (sub_nonneg.mpr (hitRate_le_one b')) C
    nlinarith
  have hcal := calibration_failure b' hret C samples hs xi hx hx1 hcap
  have hscore := pool_score_deviation I e he b' hret root a B C samples hs xi
    (beta / 256) hx (by nlinarith)
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hfail hscore
  have hfailSmall : (poolLaw C samples).prob {rows | ¬ Successful b' C samples rows} ≤ beta / 16 := by
    have h := mul_le_mul_of_nonneg_left hrow (show (0 : ℝ) ≤ samples by positivity)
    have hcancel : (samples : ℝ) * (beta * xi / (16 * samples)) = beta * xi / 16 := by
      field_simp
    rw [hcancel] at h
    have hbeta : beta * xi / 16 ≤ beta / 16 := by
      nlinarith [mul_le_mul_of_nonneg_left hx1 hb.le]
    exact hfail.trans (h.trans hbeta)
  have hcalSmall : (poolLaw C samples).prob {rows | ¬ Calibrated b' C samples xi rows} ≤ beta / 2 := by
    apply hcal.trans
    apply (div_le_iff₀ (by positivity : 0 < (xi / 4) ^ 2 * (samples : ℝ))).mpr
    nlinarith
  have hscoreSmall : (poolLaw C samples).prob {rows | xi <
      |ScoreSampling.empirical (fun y => scoreOn I (selectedPoints e b') a B (e y))
        samples (labels b' root C samples rows) - scoreMean I (selectedPoints e b') a B|} ≤
      beta / 256 + beta / 16 := by
    apply hscore.trans
    have h := mul_le_mul_of_nonneg_left hrow (show (0 : ℝ) ≤ samples by positivity)
    have hcancel : (samples : ℝ) * (beta * xi / (16 * samples)) = beta * xi / 16 := by
      field_simp
    rw [hcancel] at h
    linarith [mul_le_mul_of_nonneg_left hx1 hb.le]
  unfold Code.probability
  let F : ScaleAnswer Q → ℝ := fun r =>
    @ite ℝ (¬ ScaleGood I (ComponentExplore.retained b key l.toFinset) a B xi r)
      (Classical.propDecidable _) 1 0
  change (scaleProgram e key a xi B C samples l root cache).evaluate I.weight b
    (fun o => F o.value) ≤ beta
  rw [scaleProgram_law I.weight b e key a xi B C samples l root cache hc F]
  have hprob : (poolLaw C samples).expect (fun rows =>
      F (scaleTrace I.weight b e key a xi B C samples l root cache rows)) =
      (poolLaw C samples).prob {rows | ¬ ScaleGood I (ComponentExplore.retained b key l.toFinset) a B xi
        (scaleTrace I.weight b e key a xi B C samples l root cache rows)} := by
    rw [Law.prob_eq_expect]
    apply congrArg (poolLaw C samples).expect
    funext rows
    by_cases h : ScaleGood I (ComponentExplore.retained b key l.toFinset) a B xi
        (scaleTrace I.weight b e key a xi B C samples l root cache rows) <;> simp [F, h]
  rw [hprob]
  have hsub : {rows | ¬ ScaleGood I (ComponentExplore.retained b key l.toFinset) a B xi
      (scaleTrace I.weight b e key a xi B C samples l root cache rows)} ⊆
      {rows | ¬ Successful b' C samples rows} ∪ {rows | ¬ Calibrated b' C samples xi rows} ∪
        {rows | xi <
          |ScoreSampling.empirical (fun y => scoreOn I (selectedPoints e b') a B (e y))
            samples (labels b' root C samples rows) - scoreMean I (selectedPoints e b') a B|} := by
    intro rows hbad
    by_contra hnone
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hnone hbad
    have hsuc : Successful b' C samples rows := by tauto
    have hcalib : Calibrated b' C samples xi rows := by tauto
    have hmean : |ScoreSampling.empirical (fun y => scoreOn I (selectedPoints e b') a B (e y))
        samples (labels b' root C samples rows) - scoreMean I (selectedPoints e b') a B| ≤ xi := by
      exact le_of_not_gt (by tauto)
    obtain ⟨hg, hm, hsuc', _⟩ := scaleTrace_fields I b e key a xi B C samples l root cache hc hroot henum rows
    apply hbad
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [hsuc', decide_eq_true_eq] using hsuc
    · rw [hg, hcard]
      simpa only [Fintype.card_fin] using hcalib.1
    · rw [hg, hcard]
      simpa only [Fintype.card_fin] using hcalib.2.1
    · rw [hm, ← enumeration_selectedPoints e key b l henum]
      exact hmean
  apply ((poolLaw C samples).prob_mono hsub).trans
  have hUnion := (poolLaw C samples).prob_union_le
    ({rows | ¬ Successful b' C samples rows} ∪ {rows | ¬ Calibrated b' C samples xi rows})
    {rows | xi <
      |ScoreSampling.empirical (fun y => scoreOn I (selectedPoints e b') a B (e y))
        samples (labels b' root C samples rows) - scoreMean I (selectedPoints e b') a B|}
  have hUnion' := (poolLaw C samples).prob_union_le
    {rows | ¬ Successful b' C samples rows} {rows | ¬ Calibrated b' C samples xi rows}
  linarith

end SteinerUpperBound.MSTApproximation
