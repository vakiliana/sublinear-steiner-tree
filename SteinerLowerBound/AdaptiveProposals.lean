module

public import SteinerLowerBound.MomentMatching

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

abbrev Rate := Set.Icc (0 : ℝ) 1

inductive ProposalTree (U R : Type*)
  | leaf : R → ProposalTree U R
  | coin : Rate → ProposalTree U R → ProposalTree U R → ProposalTree U R
  | inspect : Finset U → Rate → ProposalTree U R → ProposalTree U R →
      ProposalTree U R → ProposalTree U R

namespace ProposalTree

variable {U R : Type*}

noncomputable def retention (H : Finset U) (w : U → Rate) : Rate :=
  ⟨∏ u ∈ H, (w u : ℝ),
    Finset.prod_nonneg (fun u _ => (w u).property.1),
    Finset.prod_le_one₀ (fun u _ => (w u).property.1) (fun u _ => (w u).property.2)⟩

noncomputable def run [Fintype R] : ProposalTree U R → (U → Rate) → Law R
  | .leaf r, _ => Law.pure r
  | .coin p yes no, w =>
      Law.mix p p.property.1 p.property.2 (yes.run w) (no.run w)
  | .inspect H p no reject retain, w =>
      let a := retention H w
      Law.mix p p.property.1 p.property.2
        (Law.mix a a.property.1 a.property.2 (retain.run w) (reject.run w)) (no.run w)

noncomputable def polynomial (E : Set R) : ProposalTree U R → MvPolynomial U ℝ
  | .leaf r => if r ∈ E then 1 else 0
  | .coin p yes no =>
      MvPolynomial.C (p : ℝ) * yes.polynomial E +
        MvPolynomial.C (1 - (p : ℝ)) * no.polynomial E
  | .inspect H p no reject retain =>
      MvPolynomial.C (p : ℝ) *
        (Proposals.supportPolynomial H * retain.polynomial E +
          (1 - Proposals.supportPolynomial H) * reject.polynomial E) +
        MvPolynomial.C (1 - (p : ℝ)) * no.polynomial E

noncomputable def load (u : U) : ProposalTree U R → ℕ
  | .leaf _ => 0
  | .coin _ yes no => max (yes.load u) (no.load u)
  | .inspect H _ no reject retain =>
      max (no.load u) (max (reject.load u + if u ∈ H then 1 else 0)
        (retain.load u + if u ∈ H then 1 else 0))

theorem prob_run [Fintype R] (t : ProposalTree U R) (w : U → Rate) (E : Set R) :
    (t.run w).prob E = MvPolynomial.eval (fun u => (w u : ℝ)) (t.polynomial E) := by
  induction t with
  | leaf r => simp [run, polynomial, Law.prob_pure]
  | coin p yes no hy hn =>
      simp [run, Law.prob_mix, polynomial, hy, hn]
  | inspect H p no reject retain hn hr ht =>
      simp [run, Law.prob_mix, polynomial, hn, hr, ht,
        retention, Proposals.supportPolynomial]

theorem degree_polynomial [Fintype U] (t : ProposalTree U R) (E : Set R) (u : U) :
    (t.polynomial E).degreeOf u ≤ t.load u := by
  classical
  induction t with
  | leaf r => by_cases hr : r ∈ E <;> simp [polynomial, load, hr]
  | coin p yes no hy hn =>
      apply (MvPolynomial.degreeOf_add_le _ _ _).trans
      simp only [load] at *
      exact max_le_max
        ((MvPolynomial.degreeOf_C_mul_le _ _ _).trans hy)
        ((MvPolynomial.degreeOf_C_mul_le _ _ _).trans hn)
  | inspect H p no reject retain hn hr ht =>
      simp only [polynomial, load]
      apply (MvPolynomial.degreeOf_add_le _ _ _).trans
      apply max_le
      · apply (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
        apply (MvPolynomial.degreeOf_add_le _ _ _).trans
        apply max_le
        · exact ((MvPolynomial.degreeOf_mul_le _ _ _).trans
            (add_le_add (Proposals.degree_support H u) ht)).trans
            (by omega)
        · have hs : (1 - Proposals.supportPolynomial H : MvPolynomial U ℝ).degreeOf u ≤
              if u ∈ H then 1 else 0 :=
            (MvPolynomial.degreeOf_sub_le _ _ _).trans
              (max_le (by simp) (Proposals.degree_support H u))
          exact ((MvPolynomial.degreeOf_mul_le _ _ _).trans (add_le_add hs hr)).trans
            (by omega)
      · exact ((MvPolynomial.degreeOf_C_mul_le _ _ _).trans hn).trans (le_max_left _ _)

noncomputable def marginal {Ω : Type*} [Fintype Ω] [Fintype U] [Fintype R]
    (t : ProposalTree U R) (μ : Law Ω) (w : Ω → Rate) : Law R :=
  (μ.iid U).bind (fun a => t.run (fun u => w (a u)))

theorem matching_marginal {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    [Fintype U] [Fintype R] (t : ProposalTree U R)
    {μ : Law Ω} {ν : Law Γ} {x : Ω → Rate} {y : Γ → Rate} {s : ℕ}
    (h : Law.MatchingMoments μ ν (fun ω => (x ω : ℝ)) (fun γ => (y γ : ℝ)) s)
    (hload : ∀ u, t.load u ≤ s) :
    Law.Close (t.marginal μ x) (t.marginal ν y) 0 := by
  intro E
  simp only [marginal, Law.prob_bind, prob_run]
  have heq := h.polynomial (t.polynomial E)
    (fun u => (t.degree_polynomial E u).trans (hload u))
  rw [heq]
  simp

noncomputable def increment (k : U → ℕ) (H : Finset U) (u : U) : ℕ :=
  k u + if u ∈ H then 1 else 0

noncomputable def stop (s : ℕ) (k : U → ℕ) : ProposalTree U R → ProposalTree U (Option R)
  | .leaf r => .leaf (some r)
  | .coin p yes no => .coin p (yes.stop s k) (no.stop s k)
  | .inspect H p no reject retain =>
      if ∀ u ∈ H, k u < s then
        .inspect H p (no.stop s k)
          (reject.stop s (increment k H)) (retain.stop s (increment k H))
      else .coin p (.leaf none) (no.stop s k)

theorem load_stop (t : ProposalTree U R) (s : ℕ) (k : U → ℕ) (hk : ∀ u, k u ≤ s)
    (u : U) : (t.stop s k).load u ≤ s - k u := by
  induction t generalizing k with
  | leaf r => simp [stop, load]
  | coin p yes no hy hn =>
      simp only [stop, load, max_le_iff]
      exact ⟨hy k hk, hn k hk⟩
  | inspect H p no reject retain hn hr ht =>
      simp only [stop]
      split_ifs with h
      · have hk' : ∀ v, increment k H v ≤ s := by
          intro v
          by_cases hv : v ∈ H
          · simp only [increment, hv, ↓reduceIte]
            exact h v hv
          · simpa [increment, hv] using hk v
        have hr' := hr (increment k H) hk'
        have ht' := ht (increment k H) hk'
        simp only [load, max_le_iff]
        refine ⟨hn k hk, ?_, ?_⟩
        · by_cases hu : u ∈ H
          · have hu_lt := h u hu
            simp only [increment, hu, ↓reduceIte] at hr' ⊢
            omega
          · simpa [increment, hu] using hr'
        · by_cases hu : u ∈ H
          · have hu_lt := h u hu
            simp only [increment, hu, ↓reduceIte] at ht' ⊢
            omega
          · simpa [increment, hu] using ht'
      · simp only [load, max_le_iff]
        exact ⟨Nat.zero_le _, hn k hk⟩

theorem stopped_records_match {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    [Fintype U] [Fintype R] (t : ProposalTree U R)
    {μ : Law Ω} {ν : Law Γ} {x : Ω → Rate} {y : Γ → Rate} {s : ℕ}
    (h : Law.MatchingMoments μ ν (fun ω => (x ω : ℝ)) (fun γ => (y γ : ℝ)) s) :
    Law.Close ((t.stop s (fun _ => 0)).marginal μ x)
      ((t.stop s (fun _ => 0)).marginal ν y) 0 := by
  apply matching_marginal _ h
  intro u
  simpa only [Nat.sub_zero] using load_stop t s (fun _ => 0) (fun _ => Nat.zero_le s) u

end ProposalTree

end SteinerLowerBound
