module

public import SteinerUpperBound.ReusableSample.Conditioning

@[expose] public section

namespace SteinerUpperBound.ReusableSample

open SteinerLowerBound
open scoped BigOperators Classical

variable {U : Type*} [Fintype U] [Nonempty U]

noncomputable local instance dataFintype (Ns : ℕ) : Fintype (Fin Ns → U) :=
  @Pi.instFintype (Fin Ns) (fun _ => U) (Classical.decEq _) inferInstance
    (fun _ => inferInstance)

local instance transcriptFintype (n : ℕ) : Fintype (Fin n → Bool) :=
  @Pi.instFintype (Fin n) (fun _ => Bool) inferInstance inferInstance
    (fun _ => inferInstance)

/-- Uniform records are sampled once, and only the acceptance transcript is
returned. In particular, the row vector is outside both random choices. -/
noncomputable def run (b : ℝ) (Ns t : ℕ) {n : ℕ} (R : Fin n → Finset U) :
    Law (Fin n → Bool) :=
  ((Law.uniform U).iid (Fin Ns)).bind (mechanism b Ns t R)

theorem run_support (b : ℝ) (Ns t : ℕ) {n : ℕ} (R : Fin n → Finset U)
    (T : Fin n → Bool) (hT : 0 < (run b Ns t R).mass T) : acceptances T ≤ t := by
  have hex : ∃ X : Fin Ns → U, 0 < (mechanism b Ns t R X).mass T := by
    by_contra hn
    push Not at hn
    have hh : (run b Ns t R).mass T ≤ 0 := by
      change (∑ X, ((Law.uniform U).iid (Fin Ns)).mass X *
        (mechanism b Ns t R X).mass T) ≤ 0
      apply Finset.sum_nonpos
      intro X _
      exact mul_nonpos_of_nonneg_of_nonpos
        (((Law.uniform U).iid (Fin Ns)).nonneg X) (hn X)
    linarith
  obtain ⟨X, hX⟩ := hex
  rw [mechanism_as_pool] at hX
  exact poolTree_support b (2 * Ns / t) (fun i => some (X i)) R t ∅ T hX

private theorem integrated_margins (b : ℝ) (hb : 0 < b) (Ns t : ℕ)
    {n : ℕ} (R : Fin n → Finset U) :
    (Probability.experiment ((Law.uniform U).iid (Fin Ns)) (mechanism b Ns t R)).prob
      {z | ¬ Margins (fun i => some (z.1 i)) R t ∅
        (2 * Ns / t - Ns / (4 * t)) (2 * Ns / t + Ns / (4 * t)) z.2} ≤
      2 * n * Real.exp (-(Ns / (4 * t)) / b) := by
  rw [Probability.experiment, Law.prob_bind]
  simp only [Law.prob_map]
  exact (((Law.uniform U).iid (Fin Ns)).expect_mono
    (fun X => by
      rw [mechanism_as_pool]
      exact pool_margins b hb (2 * Ns / t) (Ns / (4 * t))
        (fun i => some (X i)) R t ∅)).trans_eq
    (((Law.uniform U).iid (Fin Ns)).expect_const _)

private theorem good_transcript {b : ℝ} {Ns t n : ℕ} [Nonempty (Fin Ns)]
    (R : Fin n → Finset U)
    (hNs : 0 < Ns) (ht : 0 < t) (T : Fin n → Bool)
    (hT : 0 < (run b Ns t R).mass T)
    (htransfer : Probability.Transferred
      (Probability.averageJoint (Law.uniform U) (mechanism b Ns t R))
      (run b Ns t R) (Law.uniform U) (4 / 3) (1 / (16 * t)) T)
    (hbad : Probability.conditionalBad
      (Probability.experiment ((Law.uniform U).iid (Fin Ns)) (mechanism b Ns t R))
      (run b Ns t R)
      (fun X T => ¬ Margins (fun i => some (X i)) R t ∅
        (2 * Ns / t - Ns / (4 * t)) (2 * Ns / t + Ns / (4 * t)) T) T ≤ 1 / (16 * t)) :
    Specification R t T := by
  let ν := Law.uniform U
  let K := mechanism b Ns t R
  let π := run b Ns t R
  let D := Probability.experiment (ν.iid (Fin Ns)) K
  let P := Probability.posterior D π (Probability.experiment_marginal _ _) T hT
  let G : (Fin Ns → U) → Prop := fun X =>
    Margins (fun i => some (X i)) R t ∅
      (2 * Ns / t - Ns / (4 * t)) (2 * Ns / t + Ns / (4 * t)) T
  let ρ : ℝ := 1 / t
  let ζ : ℝ := 1 / (16 * t)
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  have hNs' : 0 < (Ns : ℝ) := by exact_mod_cast hNs
  have hρ : 0 < ρ := one_div_pos.mpr ht'
  have hρ₁ : ρ ≤ 1 := (div_le_one ht').mpr (by exact_mod_cast ht)
  have hζ : ζ = ρ / 16 := by dsimp [ζ, ρ]; ring
  have hζ' : (1 / (16 * (t : ℝ))) = ρ / 16 := hζ
  have hsq : ρ * ρ ≤ ρ := by nlinarith
  have hg : 0 < (Fintype.card U : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc := run_support b Ns t R T hT
  have hb : P.prob {X | ¬ G X} ≤ ζ := by
    change Probability.conditionalBad D π (fun X _ => ¬ G X) T ≤ ζ at hbad
    rw [Probability.conditionalBad_eq D π (Probability.experiment_marginal _ _) T hT] at hbad
    exact hbad
  have hmean (A : Finset U) :
      P.expect (fun X => Probability.sampleMean X (indicator A)) =
        Probability.posteriorMean (Probability.averageJoint ν K) π T (indicator A) :=
    Probability.posterior_sampleMean ν K T hT (indicator A)
  have hlo : (7 * ρ / 4) * Ns = 2 * Ns / t - Ns / (4 * t) := by
    dsimp [ρ]
    ring
  have hhi : (9 * ρ / 4) * Ns = 2 * Ns / t + Ns / (4 * t) := by
    dsimp [ρ]
    ring
  apply specification_of_decisions R T t ht hc
  · intro j hj
    let A := fresh R T ∅ j
    let f := fun X : Fin Ns → U => Probability.sampleMean X (indicator A)
    have hgood : ∀ X, G X → 7 * ρ / 4 ≤ f X := by
      intro X hX
      have hh := hX j (accepted_tested T t hc j hj)
      simp only [hj, ↓reduceIte] at hh
      dsimp [f]
      rw [sampleMean_indicator, le_div_iff₀ hNs', hlo]
      exact hh
    have hexp := Probability.expect_lower_good P f G (7 * ρ / 4)
      (fun X => Probability.sampleMean_nonneg X _ (indicator_nonneg A)) hgood
    have htfr := (htransfer hT (indicator A) (indicator_nonneg A) (indicator_le_one A)).1
    rw [← hmean A, uniform_indicator] at htfr
    have hfrac : ρ ≤ (A.card : ℝ) / Fintype.card U := by
      dsimp [f] at hexp
      rw [hζ] at hb
      rw [hζ'] at htfr
      nlinarith
    have hcard := (le_div_iff₀ hg).mp hfrac
    simpa [ρ, A, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hcard
  · intro j hj hjb
    let A := fresh R T ∅ j
    let f := fun X : Fin Ns → U => Probability.sampleMean X (indicator A)
    have hgood : ∀ X, G X → f X ≤ 9 * ρ / 4 := by
      intro X hX
      have hh := hX j hj
      simp only [hjb, Bool.false_eq_true, ↓reduceIte] at hh
      dsimp [f]
      rw [sampleMean_indicator, div_le_iff₀ hNs', hhi]
      exact hh
    have hexp := Probability.expect_upper_good P f G (9 * ρ / 4) (by positivity)
      (fun X => Probability.sampleMean_le_one X _ (indicator_le_one A)) hgood
    have htfr := (htransfer hT (indicator A) (indicator_nonneg A) (indicator_le_one A)).2
    rw [← hmean A, uniform_indicator] at htfr
    have hfrac : (A.card : ℝ) / Fintype.card U ≤ 4 * ρ := by
      dsimp [f] at hexp
      rw [hζ] at hb
      rw [hζ'] at htfr
      nlinarith
    have hcard := (div_le_iff₀ hg).mp hfrac
    simpa [ρ, A, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hcard

/-- Correctness from numerical inequalities on the explicit bandwidth and sample
size. Stability itself is proved for `mechanism`, not supplied as a premise. -/
theorem correctness (b : ℝ) (hb : 0 < b) (Ns t : ℕ) (hNs : 0 < Ns) (ht : 0 < t)
    {n : ℕ} (R : Fin n → Finset U) (β : ℝ) (hβ : 0 < β) (L : ℝ) (hL : 0 ≤ L)
    (ha : (1 + increment b) * Real.exp (increment b * L) ≤ 4 / 3)
    (hd : (1 + increment b) * Real.exp (-L) ≤ β / (128 * t))
    (hm : 2 * n * Real.exp (-(Ns / (4 * t)) / b) ≤ β / (64 * t)) :
    1 - β / 2 ≤ (run b Ns t R).prob {T | Specification R t T} := by
  let : Nonempty (Fin Ns) := ⟨⟨0, hNs⟩⟩
  let ν := Law.uniform U
  let K := mechanism b Ns t R
  let π := run b Ns t R
  let J := Probability.averageJoint ν K
  let D := Probability.experiment (ν.iid (Fin Ns)) K
  let δ : ℝ := β / (128 * t)
  let ζ : ℝ := 1 / (16 * t)
  let G : (Fin Ns → U) → (Fin n → Bool) → Prop := fun X T =>
    ¬ Margins (fun i => some (X i)) R t ∅
      (2 * Ns / t - Ns / (4 * t)) (2 * Ns / t + Ns / (4 * t)) T
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hs : ∀ X i y, Probability.Dominated (K X)
      (K (@Function.update (Fin Ns) (fun _ => U) (Classical.decEq _) X i y)) (4 / 3) δ := by
    intro X i y E
    have hh := mechanism_stable b hb Ns t R L hL X i y E
    have hm' := mul_le_mul_of_nonneg_right ha
      ((mechanism b Ns t R
        (@Function.update (Fin Ns) (fun _ => U) (Classical.decEq _) X i y)).prob_nonneg E)
    dsimp [K, δ]
    linarith
  have hsJ := Probability.averageJoint_stable ν K (4 / 3) δ hs
  have htfr := Probability.posterior_transfer J π ν (4 / 3) δ ζ hζ hsJ.1 hsJ.2
  have hmargin : D.prob {z | G z.1 z.2} ≤ β / (64 * t) :=
    (integrated_margins b hb Ns t R).trans hm
  have hcond := Probability.conditionalBad_markov D π G (β / (64 * t)) ζ hζ hmargin
  have hfail : π.prob {T | ¬ Specification R t T} ≤ β / 2 := by
    calc
      _ ≤ π.prob ({T | ¬ Probability.Transferred J π ν (4 / 3) ζ T} ∪
          {T | ζ < Probability.conditionalBad D π G T}) := by
        apply π.prob_mono_support
        intro T hT hbad
        by_cases htr : Probability.Transferred J π ν (4 / 3) ζ T
        · by_cases hb' : ζ < Probability.conditionalBad D π G T
          · exact Or.inr hb'
          · exact (hbad (good_transcript R hNs ht T hT htr (le_of_not_gt hb'))).elim
        · exact Or.inl htr
      _ ≤ π.prob {T | ¬ Probability.Transferred J π ν (4 / 3) ζ T} +
          π.prob {T | ζ < Probability.conditionalBad D π G T} := π.prob_union_le _ _
      _ ≤ 2 * δ / ζ + (β / (64 * t)) / ζ := add_le_add htfr hcond
      _ = β / 2 := by dsimp [δ, ζ]; field_simp; ring
  have hc := π.prob_compl {T | Specification R t T}
  change π.prob {T | ¬ Specification R t T} = 1 - π.prob {T | Specification R t T} at hc
  change 1 - β / 2 ≤ π.prob _
  linarith

end SteinerUpperBound.ReusableSample
