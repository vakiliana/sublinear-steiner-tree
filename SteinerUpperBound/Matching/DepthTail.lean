module

public import SteinerUpperBound.Matching.PathTail

@[expose] public section

/-!
# A fully proved polylogarithmic stack-depth tail

This replaces the external parallel-MIS depth theorem. A greedy prefix reduces
the residual line-graph degree; rank-swap averaging bounds monotone paths in
each dyadic window. The deliberately loose factorial estimate gives a cubic
logarithmic depth bound. No parallel-round/depth certificate is assumed.
-/

namespace SteinerUpperBound.Matching

open SteinerLowerBound
open scoped Classical BigOperators

variable {V E : Type*} [Fintype E]

namespace Graph

variable (G : Graph V E)

theorem validStack_length_le_copies (ρ : Rank E) {ds : List (Directed E)}
    (h : G.ValidStack ρ ds) : ds.length ≤ Fintype.card E := by
  have hl := (G.validStack_copies_nodup ρ h).length_le_card
  simpa only [List.length_map] using hl

/-- Uniform random ranks have cubic-logarithmic stack depth with an exponential tail. -/
theorem longStack_tail (h : ℕ) (hh : 0 < h) (hp : Fintype.card E < 2 ^ h) :
    (Rank.uniform (E := E)).prob {ρ | G.LongStack (Budget.depth h) ρ} ≤
      3 * h * Fintype.card E * Real.exp (-(8 : ℝ) * h) := by
  classical
  let p := Fintype.card E
  let L := Budget.windowLength h
  by_cases hlarge : 4 * L ≤ p
  · let S := Dyadic.stages p h
    let Bad : ℕ → Rank E → Prop := fun j ρ =>
      ¬ G.DegreeGood (2 ^ j) (Budget.degree p h (2 ^ j)) ρ ∨
        G.HasWindowPath (2 ^ j) (3 * 2 ^ j) (Budget.degree p h (2 ^ j)) L ρ
    have hbad (j : ↥S) :
        (Rank.uniform (E := E)).prob {ρ | Bad j.val ρ} ≤
          3 * p * Real.exp (-(8 : ℝ) * h) := by
      have ht : 2 * 2 ^ j.val ≤ p := (Finset.mem_filter.mp j.property).2
      have htpos : 0 < 2 ^ j.val := pow_pos (by decide) _
      have hgd := G.degreeGood_polylog_tail h (2 ^ j.val) htpos (by omega)
      have hpt := G.windowPath_polylog_tail h (2 ^ j.val) hh ht hlarge
      have heq : {ρ | Bad j.val ρ} =
          {ρ | ¬ G.DegreeGood (2 ^ j.val) (Budget.degree p h (2 ^ j.val)) ρ} ∪
            {ρ | G.HasWindowPath (2 ^ j.val) (3 * 2 ^ j.val)
              (Budget.degree p h (2 ^ j.val)) L ρ} := rfl
      rw [heq]
      have hu := (Rank.uniform (E := E)).prob_union_le
        {ρ | ¬ G.DegreeGood (2 ^ j.val) (Budget.degree p h (2 ^ j.val)) ρ}
        {ρ | G.HasWindowPath (2 ^ j.val) (3 * 2 ^ j.val)
          (Budget.degree p h (2 ^ j.val)) L ρ}
      nlinarith
    have hsub : {ρ | G.LongStack (Budget.depth h) ρ} ⊆
        {ρ | ∃ j : ↥S, Bad j.val ρ} := by
      intro ρ hlong
      by_contra hn
      have hgood : ∀ j ∈ S, G.DegreeGood (2 ^ j) (Budget.degree p h (2 ^ j)) ρ ∧
          ¬ G.HasWindowPath (2 ^ j) (3 * 2 ^ j) (Budget.degree p h (2 ^ j)) L ρ := by
        intro j hj
        have hnb : ¬ Bad j ρ := fun hb => hn ⟨⟨j, hj⟩, hb⟩
        exact ⟨by
          by_contra hg
          exact hnb (Or.inl hg), fun hpath => hnb (Or.inr hpath)⟩
      obtain ⟨d, parents, hs, hlen⟩ := hlong
      have hd := G.validStack_dyadic_length ρ h L hp
        (fun j => Budget.degree p h (2 ^ j)) hgood hs
      simp only [List.length_cons] at hd
      unfold Budget.depth at hlen
      change 4 * h * L + 1 ≤ parents.length at hlen
      nlinarith
    calc
      _ ≤ (Rank.uniform (E := E)).prob {ρ | ∃ j : ↥S, Bad j.val ρ} :=
        Law.prob_mono _ hsub
      _ ≤ ∑ j : ↥S, (Rank.uniform (E := E)).prob {ρ | Bad j.val ρ} :=
        Law.finite_union_bound _ _
      _ ≤ ∑ _j : ↥S, 3 * p * Real.exp (-(8 : ℝ) * h) :=
        Finset.sum_le_sum fun j _ => hbad j
      _ = (S.card : ℝ) * (3 * p * Real.exp (-(8 : ℝ) * h)) := by simp
      _ ≤ (h : ℝ) * (3 * p * Real.exp (-(8 : ℝ) * h)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Dyadic.card_stages_le p h) (by positivity)
      _ = _ := by ring
  · have heq : {ρ | G.LongStack (Budget.depth h) ρ} = ∅ := by
      ext ρ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨d, parents, hs, hlen⟩
      have hl := G.validStack_length_le_copies ρ hs
      simp only [List.length_cons] at hl
      unfold Budget.depth at hlen
      change 4 * h * L + 1 ≤ parents.length at hlen
      have hL : 0 < L := Budget.windowLength_pos hh
      nlinarith
    rw [heq, Law.prob_empty]
    positivity

end Graph

end SteinerUpperBound.Matching
