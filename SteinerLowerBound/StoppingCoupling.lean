module

public import SteinerLowerBound.AdaptiveMoments

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace ProposalTree

variable {U R : Type*}

theorem abs_mix_sub (p : Rate) (a b c d : ℝ) :
    |(p : ℝ) * a + (1 - (p : ℝ)) * b - ((p : ℝ) * c + (1 - (p : ℝ)) * d)| ≤
      (p : ℝ) * |a - c| + (1 - (p : ℝ)) * |b - d| := by
  calc
    _ = |(p : ℝ) * (a - c) + (1 - (p : ℝ)) * (b - d)| := by congr 1; ring
    _ ≤ |(p : ℝ) * (a - c)| + |(1 - (p : ℝ)) * (b - d)| := abs_add_le _ _
    _ = _ := by
      rw [abs_mul, abs_mul, abs_of_nonneg p.property.1,
        abs_of_nonneg (sub_nonneg.mpr p.property.2)]

theorem stopping_error [Fintype R] (t : ProposalTree U R) (w : U → Rate)
    (s : ℕ) (k : U → ℕ) (fallback : R) (E : Set R) :
    |(t.run w).prob E -
        ((t.stop s k).run w).prob ((fun r : Option R => r.getD fallback) ⁻¹' E)| ≤
      ((t.stop s k).run w).prob {none} := by
  classical
  induction t generalizing k with
  | leaf r => simp [stop, run, Law.prob_pure]
  | coin p yes no hy hn =>
      simp only [stop, run, Law.prob_mix]
      exact (abs_mix_sub p _ _ _ _).trans
        (add_le_add (mul_le_mul_of_nonneg_left (hy k) p.property.1)
          (mul_le_mul_of_nonneg_left (hn k) (sub_nonneg.mpr p.property.2)))
  | inspect H p no reject retain hn hr ht =>
      simp only [stop]
      split_ifs with h
      · simp only [run, Law.prob_mix]
        apply (abs_mix_sub p _ _ _ _).trans
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ p.property.1
          exact (abs_mix_sub (retention H w) _ _ _ _).trans
            (add_le_add
              (mul_le_mul_of_nonneg_left (ht _) (retention H w).property.1)
              (mul_le_mul_of_nonneg_left (hr _)
                (sub_nonneg.mpr (retention H w).property.2)))
        · exact mul_le_mul_of_nonneg_left (hn _) (sub_nonneg.mpr p.property.2)
      · have hlead :
            |((retention H w : ℝ) * (retain.run w).prob E +
                (1 - (retention H w : ℝ)) * (reject.run w).prob E) -
              (Law.pure (none : Option R)).prob
                ((fun r : Option R => r.getD fallback) ⁻¹' E)| ≤ 1 := by
          simpa only [Law.prob_mix, Law.prob_pure, Option.getD_none,
            Set.mem_preimage] using
            Law.close_one
              (Law.mix (retention H w) (retention H w).property.1
                (retention H w).property.2 (retain.run w) (reject.run w))
              (Law.pure fallback) E
        simp only [run, Law.prob_mix]
        apply (abs_mix_sub p _ _ _ _).trans
        have hno := hn k
        have hfirst := mul_le_mul_of_nonneg_left hlead p.property.1
        have hsecond := mul_le_mul_of_nonneg_left hno (sub_nonneg.mpr p.property.2)
        simpa [Law.prob_pure] using add_le_add hfirst hsecond

theorem execute_overflow_one (t : ProposalTree U R) (w : U → Rate)
    (s : ℕ) (k : U → ℕ) (h : ∃ u, s < k u) :
    t.execute w k (overflowPayoff s) = 1 := by
  classical
  induction t generalizing k with
  | leaf r => simp [execute, overflowPayoff, h]
  | coin p yes no hy hn => simp only [execute, hy k h, hn k h]; ring
  | inspect H p no reject retain hn hr ht =>
      have h' : ∃ u, s < increment k H u := by
        obtain ⟨u, hu⟩ := h
        refine ⟨u, ?_⟩
        dsimp [increment]
        split_ifs <;> omega
      simp only [execute, hn k h, hr _ h', ht _ h']
      ring

theorem stopped_overflow_le [Fintype R] (t : ProposalTree U R) (w : U → Rate)
    (s : ℕ) (k : U → ℕ) :
    ((t.stop s k).run w).prob {none} ≤
      t.execute w k (overflowPayoff s) := by
  classical
  induction t generalizing k with
  | leaf r =>
      simp only [stop, run, Law.prob_pure, Set.mem_singleton_iff, Option.some_ne_none, ↓reduceIte,
        execute, overflowPayoff]
      split_ifs <;> norm_num
  | coin p yes no hy hn =>
      simp only [stop, run, Law.prob_mix, execute]
      exact add_le_add (mul_le_mul_of_nonneg_left (hy k) p.property.1)
        (mul_le_mul_of_nonneg_left (hn k) (sub_nonneg.mpr p.property.2))
  | inspect H p no reject retain hn hr ht =>
      simp only [stop]
      split_ifs with h
      · simp only [run, Law.prob_mix, execute]
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ p.property.1
          exact add_le_add
            (mul_le_mul_of_nonneg_left (ht _) (retention H w).property.1)
            (mul_le_mul_of_nonneg_left (hr _)
              (sub_nonneg.mpr (retention H w).property.2))
        · exact mul_le_mul_of_nonneg_left (hn k) (sub_nonneg.mpr p.property.2)
      · have h' : ∃ u, s < increment k H u := by
          push Not at h
          obtain ⟨u, hu, hku⟩ := h
          exact ⟨u, by simp only [increment, hu, ↓reduceIte]; omega⟩
        simp only [run, Law.prob_mix, execute,
          execute_overflow_one _ w s _ h']
        have hno := mul_le_mul_of_nonneg_left (hn k) (sub_nonneg.mpr p.property.2)
        simpa [Law.prob_pure] using hno

theorem marginal_stopping_error {Ω : Type*} [Fintype Ω] [Fintype U] [Fintype R]
    (t : ProposalTree U R) (μ : Law Ω) (x : Ω → Rate)
    (s : ℕ) (fallback : R) :
    Law.Close (t.marginal μ x)
      (((t.stop s (fun _ => 0)).marginal μ x).map (fun r => r.getD fallback))
      (((t.stop s (fun _ => 0)).marginal μ x).prob {none}) := by
  intro E
  simp only [marginal, Law.prob_map, Law.prob_bind]
  rw [← Law.expect_sub]
  exact ((μ.iid U).abs_expect_le _).trans
    ((μ.iid U).expect_mono fun a => t.stopping_error (fun u => x (a u)) s
      (fun _ => 0) fallback E)

theorem marginal_overflow_bound {Ω : Type*} [Fintype Ω] [Fintype U] [Fintype R]
    (t : ProposalTree U R) (μ : Law Ω) (x : Ω → Rate) (s : ℕ)
    (G : ℝ) (hG₀ : 0 ≤ G) (hG : ∀ u, t.budget u ≤ G) :
    ((t.stop s (fun _ => 0)).marginal μ x).prob {none} ≤
      Fintype.card U * G ^ (s + 1) := by
  classical
  rw [marginal, Law.prob_bind]
  calc
    _ ≤ (μ.iid U).expect (fun _ => (Fintype.card U : ℝ) * G ^ (s + 1)) := by
      apply Law.expect_mono
      intro a
      exact (t.stopped_overflow_le (fun u => x (a u)) s (fun _ => 0)).trans
        (t.overflow_bound (fun u => x (a u)) G hG₀ hG s)
    _ = _ := Law.expect_const _ _

theorem adaptive_proposals_close {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    [Fintype U] [Fintype R] (t : ProposalTree U R) (fallback : R)
    {μ : Law Ω} {ν : Law Γ} {x : Ω → Rate} {y : Γ → Rate} {s : ℕ}
    (h : Law.MatchingMoments μ ν (fun ω => (x ω : ℝ)) (fun γ => (y γ : ℝ)) s)
    (G : ℝ) (hG₀ : 0 ≤ G) (hG : ∀ u, t.budget u ≤ G) :
    Law.Close (t.marginal μ x) (t.marginal ν y)
      (2 * Fintype.card U * G ^ (s + 1)) := by
  have h₁ := (t.marginal_stopping_error μ x s fallback).mono
    (t.marginal_overflow_bound μ x s G hG₀ hG)
  have h₂ := (t.stopped_records_match h).map (fun r => r.getD fallback)
  have h₃ := ((t.marginal_stopping_error ν y s fallback).mono
    (t.marginal_overflow_bound ν y s G hG₀ hG)).symm
  have hfull := (h₁.trans h₂).trans h₃
  convert hfull using 1
  ring

end ProposalTree

end SteinerLowerBound
