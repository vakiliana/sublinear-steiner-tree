module

public import SteinerLowerBound.MomentMatching

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Law

variable {Ω U : Type*} [Fintype Ω] [Fintype U]

theorem expect_pi_product (μ : U → Law Ω) (f : U → Ω → ℝ) :
    (pi μ).expect (fun w => ∏ u, f u (w u)) = ∏ u, (μ u).expect (f u) := by
  classical
  simp only [expect, pi]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun u ω => (μ u).mass ω * f u ω).symm

theorem expect_pi_coordinate (μ : U → Law Ω) (f : Ω → ℝ) (u : U) :
    (pi μ).expect (fun w => f (w u)) = (μ u).expect f := by
  classical
  have h := expect_pi_product μ (fun v ω => if v = u then f ω else 1)
  have hf (v : U) : (μ v).expect (fun ω => if v = u then f ω else 1) =
      if v = u then (μ u).expect f else 1 := by
    by_cases hv : v = u <;> simp [hv, expect_const]
  simpa [hf] using h

theorem prob_eq_expect (μ : Law Ω) (E : Set Ω) :
    μ.prob E = μ.expect (fun ω => if ω ∈ E then 1 else 0) := by
  classical
  simp only [prob, expect]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ω ∈ E <;> simp [h]

theorem prob_pi_coordinate (μ : U → Law Ω) (E : Set Ω) (u : U) :
    (pi μ).prob {w | w u ∈ E} = (μ u).prob E := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  simpa only [Set.mem_ofPred_eq] using
    expect_pi_coordinate μ (fun ω => if ω ∈ E then 1 else 0) u

theorem prob_iid_coordinate (μ : Law Ω) (E : Set Ω) (u : U) :
    (μ.iid U).prob {w | w u ∈ E} = μ.prob E := by
  change (pi (fun _ : U => μ)).prob {w | w u ∈ E} = μ.prob E
  exact prob_pi_coordinate _ E u

theorem prob_pi_all (μ : U → Law Ω) (P : U → Ω → Prop) :
    (pi μ).prob {w | ∀ u, P u (w u)} = ∏ u, (μ u).prob {ω | P u ω} := by
  classical
  have hi (w : U → Ω) :
      (@ite ℝ (∀ u, P u (w u)) (Classical.propDecidable _) 1 0) =
        ∏ u, if P u (w u) then 1 else 0 := by
    by_cases h : ∀ u, P u (w u)
    · simp [h]
    · push Not at h
      obtain ⟨u, hu⟩ := h
      have hzero :
          (∏ v, if P v (w v) then (1 : ℝ) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ u) (by simp [hu])
      simp [show ¬∀ u, P u (w u) by intro h; exact hu (h u), hzero]
  rw [prob_eq_expect]
  simp only [Set.mem_ofPred_eq]
  simp_rw [hi]
  rw [expect_pi_product μ (fun u ω => if P u ω then 1 else 0)]
  apply Finset.prod_congr rfl
  intro u _
  exact (prob_eq_expect _ _).symm

theorem expect_iid_finset_product (μ : Law Ω) (x : Ω → ℝ) (H : Finset U) :
    (μ.iid U).expect (fun w => ∏ u ∈ H, x (w u)) = (μ.expect x) ^ H.card := by
  classical
  have h := expect_iid_product μ (fun u ω => if u ∈ H then x ω else 1)
  have hf (u : U) : μ.expect (fun ω => if u ∈ H then x ω else 1) =
      if u ∈ H then μ.expect x else 1 := by
    by_cases hu : u ∈ H <;> simp [hu, expect_const]
  simpa [hf, Finset.prod_ite_mem] using h

theorem expect_filter_card {Γ : Type*} [Fintype Γ] (μ : Law Ω) (P : Γ → Ω → Prop) :
    μ.expect (fun ω => ((Finset.univ.filter fun γ => P γ ω).card : ℝ)) =
      ∑ γ, μ.prob {ω | P γ ω} := by
  classical
  have h (ω : Ω) :
      ((Finset.univ.filter fun γ => P γ ω).card : ℝ) =
        ∑ γ, if P γ ω then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp
  simp_rw [h, expect_sum]
  exact Finset.sum_congr rfl fun γ _ => (prob_eq_expect μ {ω | P γ ω}).symm

theorem expect_card_finset {Γ : Type*} [Fintype Γ] (μ : Law Ω) (F : Ω → Finset Γ) :
    μ.expect (fun ω => ((F ω).card : ℝ)) = ∑ γ, μ.prob {ω | γ ∈ F ω} := by
  classical
  have h (ω : Ω) : ((F ω).card : ℝ) = ∑ γ, if γ ∈ F ω then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun γ => γ ∈ F ω) = F ω := by ext γ; simp
    rw [he]
    simp
  simp_rw [h, expect_sum]
  apply Finset.sum_congr rfl
  intro γ _
  unfold expect prob
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hγ : γ ∈ F ω <;> simp [hγ]

theorem iid_mass_positive (μ : Law Ω) (w : U → Ω) (h : 0 < (μ.iid U).mass w) (u : U) :
    0 < μ.mass (w u) := by
  by_contra h'
  have hz : μ.mass (w u) = 0 := le_antisymm (le_of_not_gt h') (μ.nonneg _)
  have hzero : (μ.iid U).mass w = 0 := Finset.prod_eq_zero (Finset.mem_univ u) hz
  linarith

theorem pi_mass_positive (μ : U → Law Ω) (w : U → Ω) (h : 0 < (pi μ).mass w) (u : U) :
    0 < (μ u).mass (w u) := by
  by_contra h'
  have hz : (μ u).mass (w u) = 0 := le_antisymm (le_of_not_gt h') ((μ u).nonneg _)
  have hzero : (pi μ).mass w = 0 := Finset.prod_eq_zero (Finset.mem_univ u) hz
  linarith

end Law

theorem survival_mul {p : ℝ} (_hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (n : ℕ) :
    (1 + (n : ℝ) * p) * (1 - p) ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hfac : (1 + ((n + 1 : ℕ) : ℝ) * p) * (1 - p) ≤ 1 + (n : ℝ) * p := by
        push_cast
        nlinarith [sq_nonneg p, show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      calc
        _ = ((1 + ((n + 1 : ℕ) : ℝ) * p) * (1 - p)) * (1 - p) ^ n := by
          rw [pow_succ]
          ring
        _ ≤ (1 + (n : ℝ) * p) * (1 - p) ^ n :=
          mul_le_mul_of_nonneg_right hfac (pow_nonneg (sub_nonneg.mpr hp₁) n)
        _ ≤ 1 := ih

theorem survival_le {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n ≤ 1 / (1 + (n : ℝ) * p) := by
  have hden : 0 < 1 + (n : ℝ) * p := by positivity
  rw [le_div_iff₀ hden]
  simpa [mul_comm] using survival_mul hp₀ hp₁ n

end SteinerLowerBound
