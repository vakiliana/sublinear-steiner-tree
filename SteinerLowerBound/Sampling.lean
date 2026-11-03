module

public import SteinerLowerBound.Distributions
public import SteinerLowerBound.ProductProbability
public import SteinerLowerBound.SteinerOptimum

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace HardDistribution

variable {S Ω C : Type*} [Fintype S] [Fintype Ω] [Fintype C]

def isStar {d : ℕ} : State S d → Bool
  | .inr (.inr (.inr _)) => true
  | _ => false

def starSupport {d : ℕ} : State S d → Finset S
  | .inr (.inr (.inr H)) => H.val
  | _ => ∅

noncomputable def stars {d : ℕ} (σ : C → State S d) : Finset C :=
  Finset.univ.filter (fun c => isStar (σ c) = true)

noncomputable def covered {d : ℕ} (σ : C → State S d) : Finset S :=
  (stars σ).biUnion (fun c => neighbors d (σ c))

noncomputable def uncovered {d : ℕ} (σ : C → State S d) : Finset S :=
  Finset.univ.filter (fun u => ∀ c, u ∉ starSupport (σ c))

omit [Fintype S] in
@[simp]
theorem mem_starSupport {d : ℕ} (s : State S d) (u : S) :
    u ∈ starSupport s ↔ isStar s = true ∧ u ∈ neighbors d s := by
  rcases s with (_ | v | e | H) <;> simp [isStar, starSupport, neighbors]

theorem uncovered_eq {d : ℕ} (σ : C → State S d) :
    uncovered σ = Finset.univ \ covered σ := by
  classical
  ext u
  simp [uncovered, covered, stars, Finset.mem_biUnion, mem_starSupport]

theorem covered_add_uncovered {d : ℕ} (σ : C → State S d) :
    (covered σ).card + (uncovered σ).card = Fintype.card S := by
  rw [uncovered_eq, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  exact Nat.add_sub_of_le (Finset.card_le_univ _)

omit [Fintype S] in
theorem fillers_small {d : ℕ} (σ : C → State S d) (c : C) (hc : c ∉ stars σ) :
    (neighbors d (σ c)).card ≤ 2 := by
  have hs : isStar (σ c) ≠ true := by simpa [stars] using hc
  rcases h : σ c with (_ | u | e | H)
  · simp [neighbors]
  · simp [neighbors]
  · simp [neighbors, e.property]
  · simp [h, isStar] at hs

structure Setup (S Ω : Type*) [Fintype S] where
  d : ℕ
  H0 : ℝ
  R : ℝ
  M : ℝ
  value : Ω → ℝ
  d_ge_three : 3 ≤ d
  enough_special : d ≤ Fintype.card S
  H0_nonneg : 0 ≤ H0
  R_pos : 0 < R
  bounded : ∀ ω, 0 ≤ value ω ∧ value ω ≤ M
  valid : H0 * M ^ d / ((d : ℝ) * R) ≤ 1 / 2

namespace Setup

noncomputable def centerLaw (k : Setup S Ω) (w : S → Ω) : Law (State S k.d) :=
  staticLaw k.d k.H0 k.R (fun u => k.value (w u))
    (by have := k.d_ge_three; have := k.enough_special; omega)
    k.H0_nonneg k.R_pos.le (fun u => (k.bounded (w u)).1)
    ((starTotal_le k.d k.enough_special k.H0_nonneg k.R_pos
      (fun u => (k.bounded (w u)).1) (fun u => (k.bounded (w u)).2)).trans k.valid)

noncomputable def centersLaw (k : Setup S Ω) (w : S → Ω) : Law (C → State S k.d) :=
  Law.pi (fun _ : C => k.centerLaw w)

noncomputable def law (k : Setup S Ω) (μ : Law Ω) : Law (C → State S k.d) :=
  (μ.iid S).bind (fun w => k.centersLaw w)

omit [Fintype Ω] in
theorem prob_star (k : Setup S Ω) (w : S → Ω) :
    (k.centerLaw w).prob {s | isStar s = true} =
      starTotal k.d k.H0 k.R (fun u => k.value (w u)) := by
  simp [Law.prob, centerLaw, staticLaw, isStar, starTotal, Fintype.sum_sum_type]

omit [Fintype Ω] in
theorem prob_hit (k : Setup S Ω) (w : S → Ω) (u : S) :
    (k.centerLaw w).prob {s | u ∈ starSupport s} =
      ∑ H : Subsets S k.d, if u ∈ H.val then
        starMass k.d k.H0 k.R (fun v => k.value (w v)) H else 0 := by
  simp [Law.prob, centerLaw, staticLaw, starSupport, Fintype.sum_sum_type]

theorem mean_starTotal (k : Setup S Ω) (μ : Law Ω) (hmean : μ.expect k.value = 1) :
    (μ.iid S).expect (fun w => starTotal k.d k.H0 k.R (fun u => k.value (w u))) =
      k.H0 / ((k.d : ℝ) * k.R) := by
  have hp (H : Subsets S k.d) :
      (μ.iid S).expect (fun w => ∏ u ∈ H.val, k.value (w u)) = 1 := by
    rw [Law.expect_iid_finset_product, hmean, one_pow]
  simp only [starTotal, Law.expect_sum, starMass, Law.expect_const_mul, hp, mul_one,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_finset_len]
  have hc : ((Fintype.card S).choose k.d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos k.enough_special).ne'
  field_simp

omit [Fintype Ω] in
theorem mean_stars_conditional (k : Setup S Ω) (w : S → Ω) :
    (k.centersLaw (C := C) w).expect (fun σ => ((stars σ).card : ℝ)) =
      (Fintype.card C : ℝ) * starTotal k.d k.H0 k.R (fun u => k.value (w u)) := by
  rw [Law.expect_card_finset (k.centersLaw w) stars]
  have h (c : C) :
      (k.centersLaw w).prob {σ | c ∈ stars σ} =
        starTotal k.d k.H0 k.R (fun u => k.value (w u)) := by
    have he : {σ : C → State S k.d | c ∈ stars σ} =
        {σ | isStar (σ c) = true} := by ext σ; simp [stars]
    rw [he, centersLaw]
    simpa only [Set.mem_ofPred_eq, k.prob_star w] using
      Law.prob_pi_coordinate (fun _ : C => k.centerLaw w) {s | isStar s = true} c
  simp_rw [h]
  simp

theorem mean_stars (k : Setup S Ω) (μ : Law Ω) (hmean : μ.expect k.value = 1) :
    (k.law (C := C) μ).expect (fun σ => ((stars σ).card : ℝ)) =
      (Fintype.card C : ℝ) * k.H0 / ((k.d : ℝ) * k.R) := by
  rw [law, Law.expect_bind]
  simp_rw [mean_stars_conditional, Law.expect_const_mul, mean_starTotal k μ hmean]
  ring

omit [Fintype Ω] in
theorem positive_star_support (k : Setup S Ω) (w : S → Ω) (s : State S k.d)
    (hs : 0 < (k.centerLaw w).mass s) (hstar : isStar s = true) :
    neighbors k.d s ⊆ Finset.univ.filter (fun u => 0 < k.value (w u)) := by
  classical
  rcases s with (_ | v | e | H)
  · simp [isStar] at hstar
  · simp [isStar] at hstar
  · simp [isStar] at hstar
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra h
    have hz : k.value (w u) = 0 :=
      le_antisymm (le_of_not_gt h) (k.bounded (w u)).1
    have hp : (∏ v ∈ H.val, k.value (w v)) = 0 :=
      Finset.prod_eq_zero hu hz
    simp [centerLaw, staticLaw, starMass, hp] at hs

omit [Fintype Ω] in
theorem conditional_star_support (k : Setup S Ω) (w : S → Ω) (σ : C → State S k.d)
    (hσ : 0 < (k.centersLaw w).mass σ) :
    ∀ c ∈ stars σ, neighbors k.d (σ c) ⊆
      Finset.univ.filter (fun u => 0 < k.value (w u)) := by
  intro c hc
  apply k.positive_star_support w (σ c)
    (Law.pi_mass_positive (fun _ => k.centerLaw w) σ hσ c)
  exact (Finset.mem_filter.mp hc).2

theorem mean_positive_weights (k : Setup S Ω) (μ : Law Ω) :
    (μ.iid S).expect
        (fun w => ((Finset.univ.filter fun u => 0 < k.value (w u)).card : ℝ)) =
      (Fintype.card S : ℝ) * μ.prob {ω | 0 < k.value ω} := by
  rw [Law.expect_filter_card]
  have h (u : S) : (μ.iid S).prob {w | 0 < k.value (w u)} =
      μ.prob {ω | 0 < k.value ω} :=
    Law.prob_iid_coordinate μ {ω | 0 < k.value ω} u
  simp_rw [h]
  simp

omit [Fintype Ω] in
theorem hit_probability_lower (k : Setup S Ω) (w : S → Ω) (a : ℝ)
    (ha : 0 ≤ a) (hw : ∀ u, a ≤ k.value (w u)) (u : S) :
    k.H0 * a ^ k.d / ((Fintype.card S : ℝ) * k.R) ≤
      (k.centerLaw w).prob {s | u ∈ starSupport s} := by
  classical
  let c := k.H0 / ((k.d : ℝ) * k.R * (Fintype.card S).choose k.d)
  have hR₀ : k.R ≠ 0 := k.R_pos.ne'
  have hc₀ : 0 ≤ c := by
    apply div_nonneg k.H0_nonneg
    have := k.R_pos.le
    positivity
  have hprod (H : Subsets S k.d) : c * a ^ k.d ≤
      starMass k.d k.H0 k.R (fun v => k.value (w v)) H := by
    apply mul_le_mul_of_nonneg_left _ hc₀
    calc
      a ^ k.d = ∏ _v ∈ H.val, a := by simp [H.property]
      _ ≤ ∏ v ∈ H.val, k.value (w v) :=
        Finset.prod_le_prod₀ (fun _ _ => ha) (fun v _ => hw v)
  have hcount :
      (Finset.univ.filter (fun H : Subsets S k.d => u ∈ H.val)).card =
        (Fintype.card S - 1).choose (k.d - 1) := by
    simpa using prescribed_count k.d {u} (by have := k.d_ge_three; simp; omega)
  have hid :
      ((Fintype.card S).choose k.d : ℝ) * (k.d : ℝ) =
        (Fintype.card S : ℝ) * ((Fintype.card S - 1).choose (k.d - 1) : ℝ) := by
    have h := Nat.choose_mul (n := Fintype.card S) (k := k.d) (s := 1)
      (by have := k.d_ge_three; omega)
    simpa using congrArg (fun n : ℕ => (n : ℝ)) h
  have hm₀ : (Fintype.card S : ℝ) ≠ 0 := by
    have hd := k.d_ge_three
    have hm := k.enough_special
    exact_mod_cast (show Fintype.card S ≠ 0 by omega)
  have hd₀ : (k.d : ℝ) ≠ 0 := by
    have hd := k.d_ge_three
    exact_mod_cast (show k.d ≠ 0 by omega)
  have hchoose : ((Fintype.card S).choose k.d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos k.enough_special).ne'
  rw [prob_hit]
  calc
    _ = ((Fintype.card S - 1).choose (k.d - 1) : ℝ) * (c * a ^ k.d) := by
      dsimp [c]
      field_simp
      nlinarith [congrArg (fun z : ℝ => k.H0 * a ^ k.d * z) hid]
    _ = ∑ H : Subsets S k.d, if u ∈ H.val then c * a ^ k.d else 0 := by
      rw [← Finset.sum_filter]
      simp [hcount]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro H _
      split_ifs
      · exact hprod H
      · rfl

omit [Fintype Ω] in
theorem uncovered_probability (k : Setup S Ω) (w : S → Ω) (u : S) :
    (k.centersLaw (C := C) w).prob {σ | u ∈ uncovered σ} =
      (1 - (k.centerLaw w).prob {s | u ∈ starSupport s}) ^ Fintype.card C := by
  classical
  have he : {σ : C → State S k.d | u ∈ uncovered σ} =
      {σ | ∀ c, u ∉ starSupport (σ c)} := by ext σ; simp [uncovered]
  rw [he, centersLaw, Law.prob_pi_all (fun _ : C => k.centerLaw w)
    (fun _ s => u ∉ starSupport s)]
  have hc : {s : State S k.d | u ∉ starSupport s} = {s | u ∈ starSupport s}ᶜ := rfl
  simp_rw [hc, Law.prob_compl]
  simp

omit [Fintype Ω] in
theorem mean_uncovered_conditional (k : Setup S Ω) (w : S → Ω)
    (a : ℝ) (ha : 0 ≤ a) (hw : ∀ u, a ≤ k.value (w u))
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * k.R) :
    (k.centersLaw (C := C) w).expect (fun σ => ((uncovered σ).card : ℝ)) ≤
      Fintype.card S / (1 + k.H0 * a ^ k.d) := by
  classical
  have hR₀ : k.R ≠ 0 := k.R_pos.ne'
  have hden : 0 < 1 + k.H0 * a ^ k.d := by
    have := k.H0_nonneg
    positivity
  have hm₀ : (Fintype.card S : ℝ) ≠ 0 := by
    have hd := k.d_ge_three
    have hm := k.enough_special
    exact_mod_cast (show Fintype.card S ≠ 0 by omega)
  have hpoint (u : S) :
      (k.centersLaw (C := C) w).prob {σ | u ∈ uncovered σ} ≤
        1 / (1 + k.H0 * a ^ k.d) := by
    rw [uncovered_probability]
    have hh := k.hit_probability_lower w a ha hw u
    have hmult := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ Fintype.card C by positivity)
    have hid : (Fintype.card C : ℝ) *
        (k.H0 * a ^ k.d / ((Fintype.card S : ℝ) * k.R)) = k.H0 * a ^ k.d := by
      rw [hC]
      field_simp
    rw [hid] at hmult
    exact (survival_le ((k.centerLaw w).prob_nonneg _) ((k.centerLaw w).prob_le_one _) _).trans
      (one_div_le_one_div_of_le hden (by linarith))
  rw [Law.expect_card_finset (k.centersLaw w) uncovered]
  calc
    _ ≤ ∑ _u : S, 1 / (1 + k.H0 * a ^ k.d) :=
      Finset.sum_le_sum (fun u _ => hpoint u)
    _ = _ := by simp [div_eq_mul_inv]

theorem mean_uncovered (k : Setup S Ω) (μ : Law Ω)
    (a : ℝ) (ha : 0 ≤ a) (hfloor : ∀ ω, 0 < μ.mass ω → a ≤ k.value ω)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * k.R) :
    (k.law (C := C) μ).expect (fun σ => ((uncovered σ).card : ℝ)) ≤
      Fintype.card S / (1 + k.H0 * a ^ k.d) := by
  rw [law, Law.expect_bind]
  calc
    _ ≤ (μ.iid S).expect (fun _ => (Fintype.card S : ℝ) / (1 + k.H0 * a ^ k.d)) := by
      apply Law.expect_mono_support
      intro w hw
      exact k.mean_uncovered_conditional w a ha
        (fun u => hfloor (w u) (Law.iid_mass_positive μ w hw u)) hC
    _ = _ := Law.expect_const _ _

end Setup

end HardDistribution

end SteinerLowerBound
