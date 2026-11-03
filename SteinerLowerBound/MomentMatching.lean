module

public import SteinerLowerBound.FiniteProbability

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Law

variable {Ω Γ U J : Type*} [Fintype Ω] [Fintype Γ] [Fintype U]

def MatchingMoments (μ : Law Ω) (ν : Law Γ) (x : Ω → ℝ) (y : Γ → ℝ)
    (s : ℕ) : Prop :=
  ∀ j ≤ s, μ.expect (fun ω => x ω ^ j) = ν.expect (fun γ => y γ ^ j)

theorem MatchingMoments.scale {μ : Law Ω} {ν : Law Γ}
    {x : Ω → ℝ} {y : Γ → ℝ} {s : ℕ}
    (h : MatchingMoments μ ν x y s) (M : ℝ) :
    MatchingMoments μ ν (fun ω => x ω / M) (fun γ => y γ / M) s := by
  intro j hj
  simp_rw [div_pow, div_eq_mul_inv, expect_mul_const]
  rw [h j hj]

theorem MatchingMoments.monomial {μ : Law Ω} {ν : Law Γ}
    {x : Ω → ℝ} {y : Γ → ℝ} {s : ℕ}
    (h : MatchingMoments μ ν x y s) (e : U → ℕ) (he : ∀ u, e u ≤ s) :
    (μ.iid U).expect (fun w => ∏ u, x (w u) ^ e u) =
      (ν.iid U).expect (fun w => ∏ u, y (w u) ^ e u) := by
  rw [expect_iid_product μ (fun u ω => x ω ^ e u),
    expect_iid_product ν (fun u γ => y γ ^ e u)]
  exact Finset.prod_congr rfl fun u _ => h (e u) (he u)

theorem expect_sum (μ : Law Ω) {J : Type*} (I : Finset J) (f : J → Ω → ℝ) :
    μ.expect (fun ω => ∑ j ∈ I, f j ω) = ∑ j ∈ I, μ.expect (f j) := by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem MatchingMoments.polynomial {μ : Law Ω} {ν : Law Γ}
    {x : Ω → ℝ} {y : Γ → ℝ} {s : ℕ}
    (h : MatchingMoments μ ν x y s) (p : MvPolynomial U ℝ)
    (hp : ∀ u, p.degreeOf u ≤ s) :
    (μ.iid U).expect (fun w => MvPolynomial.eval (fun u => x (w u)) p) =
      (ν.iid U).expect (fun w => MvPolynomial.eval (fun u => y (w u)) p) := by
  classical
  have expand (w : U → Ω) :
      MvPolynomial.eval (fun u => x (w u)) p =
        ∑ e ∈ p.support, p.coeff e * ∏ u, x (w u) ^ e u := by
    rw [MvPolynomial.eval_eq]
    apply Finset.sum_congr rfl
    intro e _
    congr 1
    exact Finsupp.prod_fintype e (fun u n => x (w u) ^ n) (by simp)
  have expand' (w : U → Γ) :
      MvPolynomial.eval (fun u => y (w u)) p =
        ∑ e ∈ p.support, p.coeff e * ∏ u, y (w u) ^ e u := by
    rw [MvPolynomial.eval_eq]
    apply Finset.sum_congr rfl
    intro e _
    congr 1
    exact Finsupp.prod_fintype e (fun u n => y (w u) ^ n) (by simp)
  simp_rw [expand, expand', expect_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp_rw [mul_comm (p.coeff e), expect_mul_const]
  rw [h.monomial e (fun u => (MvPolynomial.le_degreeOf_of_mem_support u he).trans (hp u))]

end Law

namespace Proposals

variable {U J : Type*}

noncomputable def supportPolynomial (H : Finset U) : MvPolynomial U ℝ :=
  ∏ u ∈ H, MvPolynomial.X u

noncomputable def recordPolynomial (I : Finset J) (H : J → Finset U) (b : J → Bool) :
    MvPolynomial U ℝ :=
  ∏ j ∈ I, if b j then supportPolynomial (H j) else 1 - supportPolynomial (H j)

theorem degree_support (H : Finset U) (u : U) :
    (supportPolynomial H).degreeOf u ≤ if u ∈ H then 1 else 0 := by
  classical
  calc
    _ ≤ ∑ v ∈ H, (MvPolynomial.X v : MvPolynomial U ℝ).degreeOf u :=
      MvPolynomial.degreeOf_prod_le _ _ _
    _ = _ := by simp [MvPolynomial.degreeOf_X]

theorem degree_record (I : Finset J) (H : J → Finset U) (b : J → Bool) (u : U) :
    (recordPolynomial I H b).degreeOf u ≤ (I.filter fun j => u ∈ H j).card := by
  classical
  calc
    _ ≤ ∑ j ∈ I, (if b j then supportPolynomial (H j)
        else 1 - supportPolynomial (H j)).degreeOf u :=
      MvPolynomial.degreeOf_prod_le _ _ _
    _ ≤ ∑ j ∈ I, if u ∈ H j then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      cases hb : b j
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact (MvPolynomial.degreeOf_sub_le _ _ _).trans
          (max_le (by simp) (degree_support _ _))
      · simpa only [hb, ↓reduceIte] using degree_support (H j) u
    _ = _ := by simp

theorem eval_record (I : Finset J) (H : J → Finset U) (b : J → Bool) (w : U → ℝ) :
    MvPolynomial.eval w (recordPolynomial I H b) =
      ∏ j ∈ I, if b j then ∏ u ∈ H j, w u else 1 - ∏ u ∈ H j, w u := by
  classical
  simp [recordPolynomial, supportPolynomial, apply_ite]

theorem moment_identity {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [Fintype U]
    {μ : Law Ω} {ν : Law Γ} {x : Ω → ℝ} {y : Γ → ℝ} {s : ℕ}
    (h : Law.MatchingMoments μ ν x y s) (M : ℝ)
    (I : Finset J) (H : J → Finset U) (b : J → Bool)
    (hload : ∀ u, (I.filter fun j => u ∈ H j).card ≤ s) :
    (μ.iid U).expect (fun w =>
      ∏ j ∈ I, if b j then ∏ u ∈ H j, x (w u) / M
        else 1 - ∏ u ∈ H j, x (w u) / M) =
    (ν.iid U).expect (fun w =>
      ∏ j ∈ I, if b j then ∏ u ∈ H j, y (w u) / M
        else 1 - ∏ u ∈ H j, y (w u) / M) := by
  classical
  simpa only [eval_record] using
    (h.scale M).polynomial (recordPolynomial I H b)
      (fun u => (degree_record I H b u).trans (hload u))

end Proposals

end SteinerLowerBound
