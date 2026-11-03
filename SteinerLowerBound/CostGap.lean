module

public import SteinerLowerBound.Sampling
public import SteinerLowerBound.Testing
public import SteinerLowerBound.WeightLaws

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace HardDistribution.Setup

variable {S Ω G I C : Type*}
variable [Fintype S] [Fintype Ω] [Fintype G] [Fintype I] [Fintype C]
variable [Nonempty G] [Nonempty I]

noncomputable def instanceOpt (k : Setup S Ω) (ell : ℝ) (σ : C → State S k.d) : ℝ :=
  Steiner.optimum (G := G) (I := I) ell (fun c => neighbors k.d (σ c))

omit [Fintype Ω] in
theorem yes_cost_deterministic (k : Setup S Ω) {ell : ℝ} (hEll : ell ≤ 2)
    (σ : C → State S k.d) :
    k.instanceOpt (G := G) (I := I) ell σ ≤
      ell * Fintype.card G * ((Fintype.card I : ℝ) - 1) +
        2 * Fintype.card G + Fintype.card S - 2 +
          (uncovered σ).card + 2 * (stars σ).card := by
  have h := Steiner.optimum_upper (G := G) (I := I) hEll
    (fun c => neighbors k.d (σ c)) (stars σ)
  have hc : ((covered σ).card : ℝ) + (uncovered σ).card = Fintype.card S := by
    exact_mod_cast covered_add_uncovered σ
  change k.instanceOpt (G := G) (I := I) ell σ ≤ _ at h
  change k.instanceOpt (G := G) (I := I) ell σ ≤ _
  dsimp [covered] at hc
  linarith

theorem yes_cost_probability (k : Setup S Ω) (μ : Law Ω) {ell : ℝ} (hEll : ell ≤ 2)
    (hmean : μ.expect k.value = 1) (a : ℝ) (ha : 0 ≤ a)
    (hfloor : ∀ ω, 0 < μ.mass ω → a ≤ k.value ω)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * k.R)
    (u z : ℝ) (hu : 0 < u) (hz : 0 < z) :
    (k.law (C := C) μ).prob {σ |
        ell * Fintype.card G * ((Fintype.card I : ℝ) - 1) +
          2 * Fintype.card G + Fintype.card S - 2 + u + 2 * z <
            k.instanceOpt (G := G) (I := I) ell σ} ≤
      (Fintype.card S / (1 + k.H0 * a ^ k.d)) / u +
        ((Fintype.card C : ℝ) * k.H0 / ((k.d : ℝ) * k.R)) / z := by
  let law := k.law (C := C) μ
  have hs : {σ : C → State S k.d |
        ell * Fintype.card G * ((Fintype.card I : ℝ) - 1) +
          2 * Fintype.card G + Fintype.card S - 2 + u + 2 * z <
            k.instanceOpt (G := G) (I := I) ell σ} ⊆
      {σ | u < ((uncovered σ).card : ℝ)} ∪ {σ | z < ((stars σ).card : ℝ)} := by
    intro σ hσ
    by_cases h₁ : u < ((uncovered σ).card : ℝ)
    · exact Or.inl h₁
    · right
      have h := k.yes_cost_deterministic (G := G) (I := I) hEll σ
      dsimp [instanceOpt] at *
      linarith [le_of_not_gt h₁]
  have hunc := (law.markov_gt (fun σ => Nat.cast_nonneg (uncovered σ).card) hu).trans
    (div_le_div_of_nonneg_right (k.mean_uncovered (C := C) μ a ha hfloor hC) hu.le)
  have hstars := law.markov_gt (fun σ => Nat.cast_nonneg (stars σ).card) hz
  rw [k.mean_stars (C := C) μ hmean] at hstars
  exact ((law.prob_mono hs).trans (law.prob_union_le _ _)).trans (add_le_add hunc hstars)

theorem no_cost_probability (k : Setup S Ω) (μ : Law Ω) {ell : ℝ} (hEll : ell ≤ 2)
    (b : ℝ) (hb : 0 < b) :
    (k.law (C := C) μ).prob {σ | k.instanceOpt (G := G) (I := I) ell σ <
      ell * Fintype.card G * Fintype.card I + 2 * Fintype.card S - 2 - b} ≤
        ((Fintype.card S : ℝ) * μ.prob {ω | 0 < k.value ω}) / b := by
  classical
  let positive (w : S → Ω) := Finset.univ.filter (fun u => 0 < k.value (w u))
  have hcond (w : S → Ω) :
      (k.centersLaw (C := C) w).prob {σ | k.instanceOpt (G := G) (I := I) ell σ <
        ell * Fintype.card G * Fintype.card I + 2 * Fintype.card S - 2 - b} ≤
          if b < ((positive w).card : ℝ) then 1 else 0 := by
    by_cases hlarge : b < ((positive w).card : ℝ)
    · simpa only [hlarge, ↓reduceIte] using (k.centersLaw (C := C) w).prob_le_one _
    · simp only [hlarge, ↓reduceIte]
      apply le_trans ((k.centersLaw (C := C) w).prob_mono_support
        (F := ∅) (fun σ hσ hbad => ?_)) (by simp)
      have hlower := Steiner.optimum_lower (G := G) (I := I) hEll
        (fun c => neighbors k.d (σ c)) (stars σ) (positive w)
        (k.conditional_star_support w σ hσ) (fillers_small σ)
      dsimp [instanceOpt] at hbad
      linarith [le_of_not_gt hlarge]
  rw [law, Law.prob_bind]
  calc
    _ ≤ (μ.iid S).expect (fun w => if b < ((positive w).card : ℝ) then 1 else 0) :=
      Law.expect_mono _ hcond
    _ = (μ.iid S).prob {w | b < ((positive w).card : ℝ)} := by
      symm
      exact Law.prob_eq_expect _ _
    _ ≤ (μ.iid S).expect (fun w => ((positive w).card : ℝ)) / b :=
      Law.markov_gt _ (fun w => Nat.cast_nonneg _) hb
    _ = _ := by rw [mean_positive_weights]

theorem floor_power (d : ℕ) (hd : 1 ≤ d) :
    1 / 2 ≤ (1 / (1 + 1 / (2 * (d : ℝ)))) ^ d := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  let κ := 1 / (2 * (d : ℝ))
  have hκ₀ : 0 < κ := by dsimp [κ]; positivity
  have hκ₁ : κ ≤ 1 := by
    dsimp [κ]
    rw [div_le_one (by positivity : 0 < 2 * (d : ℝ))]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hfloor : 1 - κ ≤ 1 / (1 + κ) := by
    rw [le_div_iff₀ (by linarith : 0 < 1 + κ)]
    nlinarith [sq_nonneg κ]
  have hBern := one_add_mul_le_pow (a := -κ) (by linarith : (-2 : ℝ) ≤ -κ) d
  have hκd : (d : ℝ) * κ = 1 / 2 := by dsimp [κ]; field_simp
  have hhalf : 1 / 2 ≤ (1 - κ) ^ d := by
    simp only [mul_neg, ← sub_eq_add_neg, hκd] at hBern
    linarith
  exact hhalf.trans (pow_le_pow_left₀ (sub_nonneg.mpr hκ₁) hfloor d)

end HardDistribution.Setup

end SteinerLowerBound
