module

public import SteinerUpperBound.Matching.Uniform

@[expose] public section

/-!
# Degree reduction under a uniform copy order

The proof uses averaging over rank transpositions, rather than a conditional
independence claim about the residual graph.
-/

namespace SteinerUpperBound.Matching

open SteinerLowerBound FiniteAveraging
open scoped Classical BigOperators

variable {V E : Type*} [Fintype E]

namespace Graph

variable (G : Graph V E)

def HighResidual (e : E) (D k : ℕ) (ρ : Rank E) : Prop :=
  e ∈ G.residual ρ k ∧ D ≤ (G.residualNeighbors ρ k e).card

theorem highResidual_mono (e : E) (D : ℕ) {i j : ℕ} (hij : i ≤ j) (ρ : Rank E)
    (h : G.HighResidual e D j ρ) : G.HighResidual e D i ρ :=
  ⟨G.residual_antitone ρ hij h.1,
    h.2.trans (Finset.card_le_card (G.residualNeighbors_antitone ρ e hij))⟩

theorem highResidual_swap (e : E) (D k : ℕ) (ρ : Rank E)
    (i j : Fin (Fintype.card E)) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    G.HighResidual e D k (ρ.swapRanks i j) ↔ G.HighResidual e D k ρ := by
  simp only [HighResidual, G.residual_swap ρ k i j hi hj,
    G.residualNeighbors_swap ρ k i j hi hj]

theorem highResidual_choices (e : E) (D k : ℕ) (hk : k < Fintype.card E)
    (ρ : Rank E) :
    ((Rank.suffix E k).filter fun j =>
      G.HighResidual e D (k + 1) (ρ.swapRanks ⟨k, hk⟩ j)).card ≤
      if G.HighResidual e D k ρ then Fintype.card E - k - D else 0 := by
  classical
  let S := Rank.suffix E k
  let A := (G.residualNeighbors ρ k e).image ρ
  have hAS : A ⊆ S := by
    intro j hj
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hj
    exact (Rank.mem_suffix k _).mpr
      (G.residual_rank ρ k ((G.mem_residualNeighbors ρ k e f).mp hf).1)
  have hcard : A.card = (G.residualNeighbors ρ k e).card :=
    Finset.card_image_of_injective _ ρ.injective
  have hprev (j : Fin (Fintype.card E)) (hj : j ∈ S)
      (hn : G.HighResidual e D (k + 1) (ρ.swapRanks ⟨k, hk⟩ j)) :
      G.HighResidual e D k ρ :=
    (G.highResidual_swap e D k ρ _ j (by simp) ((Rank.mem_suffix k j).mp hj)).mp
      (G.highResidual_mono e D (Nat.le_succ k) _ hn)
  by_cases h : G.HighResidual e D k ρ
  · simp only [h, ↓reduceIte]
    have hsub :
        (S.filter fun j => G.HighResidual e D (k + 1) (ρ.swapRanks ⟨k, hk⟩ j)) ⊆ S \ A := by
      intro j hj
      obtain ⟨hjS, hjB⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_sdiff.mpr ⟨hjS, ?_⟩
      intro hjA
      obtain ⟨f, hf, hfj⟩ := Finset.mem_image.mp hjA
      have hfe : ρ.edge j = f := by
        rw [← hfj]
        exact ρ.symm_apply_apply f
      have hx : (ρ.swapRanks ⟨k, hk⟩ j).edge ⟨k, hk⟩ ∈
          G.residualNeighbors (ρ.swapRanks ⟨k, hk⟩ j) k e := by
        simpa [Rank.swapRanks_edge, hfe,
          G.residualNeighbors_swap ρ k ⟨k, hk⟩ j (by simp)
            ((Rank.mem_suffix k j).mp hjS) e] using hf
      exact G.residual_killed (ρ.swapRanks ⟨k, hk⟩ j) k hk e hx hjB.1
    calc
      _ ≤ (S \ A).card := Finset.card_le_card hsub
      _ = S.card - A.card := Finset.card_sdiff_of_subset hAS
      _ ≤ Fintype.card E - k - D := by
        rw [hcard, Rank.card_suffix]
        exact Nat.sub_le_sub_left h.2 _
  · simp only [h, ↓reduceIte]
    have heq : (S.filter fun j =>
        G.HighResidual e D (k + 1) (ρ.swapRanks ⟨k, hk⟩ j)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨hjS, hjB⟩ := Finset.mem_filter.mp hj
      exact h (hprev j hjS hjB)
    change (S.filter fun j =>
      G.HighResidual e D (k + 1) (ρ.swapRanks ⟨k, hk⟩ j)).card ≤ 0
    rw [heq]
    exact Nat.le_refl 0

noncomputable def highResidualProb (e : E) (D k : ℕ) : ℝ :=
  (Rank.uniform (E := E)).prob {ρ | G.HighResidual e D k ρ}

theorem highResidualProb_nonneg (e : E) (D k : ℕ) :
    0 ≤ G.highResidualProb e D k :=
  Law.prob_nonneg _ _

theorem highResidualProb_step (e : E) (D k : ℕ)
    (hk : k < Fintype.card E) :
    G.highResidualProb e D (k + 1) ≤
      (1 - (D : ℝ) / Fintype.card E) * G.highResidualProb e D k := by
  classical
  let S := Rank.suffix E k
  let μ := Rank.uniform (E := E)
  have hpoint (ρ : Rank E) :
      (((S.filter fun j => G.HighResidual e D (k + 1)
        (ρ.swapRanks ⟨k, hk⟩ j)).card : ℕ) : ℝ) ≤
        ((Fintype.card E - k - D : ℕ) : ℝ) * indicator (G.HighResidual e D k) ρ := by
    have h := G.highResidual_choices e D k hk ρ
    by_cases hB : G.HighResidual e D k ρ
    · simpa [S, indicator, hB] using (Nat.cast_le (α := ℝ)).mpr h
    · simpa [S, indicator, hB] using (Nat.cast_le (α := ℝ)).mpr h
  have havg :
      μ.expect (fun ρ => ((S.filter fun j => G.HighResidual e D (k + 1)
        (ρ.swapRanks ⟨k, hk⟩ j)).card : ℝ)) =
        (S.card : ℝ) * G.highResidualProb e D (k + 1) := by
    simp only [card_filter_indicator]
    rw [expect_sum]
    change (∑ j ∈ S, μ.expect (fun ρ =>
      indicator (G.HighResidual e D (k + 1)) (ρ.swapRanks ⟨k, hk⟩ j))) =
        (S.card : ℝ) * G.highResidualProb e D (k + 1)
    have heq (j : Fin (Fintype.card E)) :
        μ.expect (fun ρ => indicator (G.HighResidual e D (k + 1))
          (ρ.swapRanks ⟨k, hk⟩ j)) = G.highResidualProb e D (k + 1) := by
      rw [show (fun ρ => indicator (G.HighResidual e D (k + 1))
          (ρ.swapRanks ⟨k, hk⟩ j)) =
          (fun ρ => indicator (G.HighResidual e D (k + 1))
            (Rank.swapEquiv ⟨k, hk⟩ j ρ)) from rfl]
      change (Law.uniform (Rank E)).expect (fun ρ =>
        indicator (G.HighResidual e D (k + 1)) (Rank.swapEquiv ⟨k, hk⟩ j ρ)) = _
      rw [uniform_expect_equiv]
      exact expect_indicator _ _
    simp_rw [heq]
    simp
  have hineq := μ.expect_mono hpoint
  rw [havg, Law.expect_const_mul, expect_indicator] at hineq
  change (S.card : ℝ) * G.highResidualProb e D (k + 1) ≤
    ((Fintype.card E - k - D : ℕ) : ℝ) * G.highResidualProb e D k at hineq
  have hpk : k ≤ Fintype.card E := Nat.le_of_lt hk
  have hp : (0 : ℝ) < Fintype.card E := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hs : (0 : ℝ) < S.card := by
    rw [Rank.card_suffix]
    exact_mod_cast Nat.sub_pos_of_lt hk
  have hnow := G.highResidualProb_nonneg e D k
  by_cases hDs : D ≤ Fintype.card E - k
  · have hsle : (S.card : ℝ) ≤ Fintype.card E := by
      rw [Rank.card_suffix]
      exact_mod_cast Nat.sub_le (Fintype.card E) k
    have hcast : ((Fintype.card E - k - D : ℕ) : ℝ) = (S.card : ℝ) - D := by
      rw [Nat.cast_sub hDs, Rank.card_suffix]
    rw [hcast] at hineq
    have hratio : (S.card : ℝ) - D ≤
        (S.card : ℝ) * (1 - (D : ℝ) / Fintype.card E) := by
      rw [mul_sub, mul_one]
      have hd : (0 : ℝ) ≤ D := Nat.cast_nonneg D
      have hdiv : (S.card : ℝ) * ((D : ℝ) / Fintype.card E) ≤ D := by
        have hm := mul_le_mul_of_nonneg_right hsle (div_nonneg hd hp.le)
        simpa [mul_div_cancel₀ _ (ne_of_gt hp), mul_div_assoc, mul_comm] using hm
      linarith
    have hm := mul_le_mul_of_nonneg_right hratio hnow
    nlinarith
  · have hzero : G.highResidualProb e D k = 0 := by
      apply le_antisymm _ hnow
      unfold highResidualProb
      have heq : {ρ : Rank E | G.HighResidual e D k ρ} = ∅ := by
        ext ρ
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hB
        exact hDs (hB.2.trans (G.residualNeighbors_card_le ρ k e))
      rw [heq, Law.prob_empty]
    rw [hzero, mul_zero] at hineq ⊢
    nlinarith

theorem highResidualProb_eq_zero (e : E) (D k : ℕ)
    (h : Fintype.card E ≤ k ∨ Fintype.card E < D) :
    G.highResidualProb e D k = 0 := by
  have heq : {ρ : Rank E | G.HighResidual e D k ρ} = ∅ := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hB
    rcases h with hk | hD
    · have hrank := G.residual_rank ρ k hB.1
      have hlt := ρ.index_lt e
      omega
    · have hc := hB.2.trans (G.residualNeighbors_card_le ρ k e)
      omega
  unfold highResidualProb
  rw [heq, Law.prob_empty]

theorem highResidualProb_le_pow (e : E) (D k : ℕ) (hD : D ≤ Fintype.card E) :
    G.highResidualProb e D k ≤ (1 - (D : ℝ) / Fintype.card E) ^ k := by
  have hp : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast Nat.zero_lt_of_lt ((Fintype.equivFin E e).isLt)
  have hq : (0 : ℝ) ≤ 1 - (D : ℝ) / Fintype.card E := by
    have hd : (D : ℝ) ≤ Fintype.card E := by exact_mod_cast hD
    exact sub_nonneg.mpr ((div_le_one hp).mpr hd)
  induction k with
  | zero =>
    simpa [highResidualProb] using
      (Rank.uniform (E := E)).prob_le_one {ρ | G.HighResidual e D 0 ρ}
  | succ k ih =>
    by_cases hk : k < Fintype.card E
    · calc
        _ ≤ (1 - (D : ℝ) / Fintype.card E) * G.highResidualProb e D k :=
          G.highResidualProb_step e D k hk
        _ ≤ (1 - (D : ℝ) / Fintype.card E) *
            (1 - (D : ℝ) / Fintype.card E) ^ k :=
          mul_le_mul_of_nonneg_left ih hq
        _ = _ := by rw [pow_succ']
    · rw [G.highResidualProb_eq_zero e D (k + 1) (Or.inl (by omega))]
      exact pow_nonneg hq _

/-- Exponential residual-degree tail, proved for labeled multigraphs. -/
theorem highResidualProb_le_exp (e : E) (D k : ℕ) :
    G.highResidualProb e D k ≤
      Real.exp (-(D : ℝ) * k / Fintype.card E) := by
  by_cases hD : D ≤ Fintype.card E
  · have hp : (0 : ℝ) < Fintype.card E := by
      exact_mod_cast Nat.zero_lt_of_lt ((Fintype.equivFin E e).isLt)
    have hq : (0 : ℝ) ≤ 1 - (D : ℝ) / Fintype.card E := by
      exact sub_nonneg.mpr ((div_le_one hp).mpr (by exact_mod_cast hD))
    calc
      _ ≤ (1 - (D : ℝ) / Fintype.card E) ^ k :=
        G.highResidualProb_le_pow e D k hD
      _ ≤ Real.exp (-(D : ℝ) / Fintype.card E) ^ k :=
        pow_le_pow_left₀ hq
          (by simpa only [neg_div] using
            (Real.one_sub_le_exp_neg ((D : ℝ) / Fintype.card E))) k
      _ = Real.exp (-(D : ℝ) * k / Fintype.card E) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  · rw [G.highResidualProb_eq_zero e D k (Or.inr (Nat.lt_of_not_ge hD))]
    exact (Real.exp_pos _).le

theorem maxResidualDegree_tail (D k : ℕ) :
    (Rank.uniform (E := E)).prob {ρ | ∃ e, G.HighResidual e D k ρ} ≤
      Fintype.card E * Real.exp (-(D : ℝ) * k / Fintype.card E) := by
  calc
    _ ≤ ∑ e, G.highResidualProb e D k := Law.finite_union_bound _ _
    _ ≤ ∑ _e : E, Real.exp (-(D : ℝ) * k / Fintype.card E) :=
      Finset.sum_le_sum fun e _ => G.highResidualProb_le_exp e D k
    _ = _ := by simp

end Graph

end SteinerUpperBound.Matching
