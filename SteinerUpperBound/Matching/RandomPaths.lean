module

public import SteinerUpperBound.Matching.DoubleCounting

@[expose] public section

/-!
# Paths in the unexposed suffix of a uniform order

All probability bounds below are obtained by finite rank-swap averaging.
In particular, the residual graph is not treated as an independent random graph.
-/

namespace SteinerUpperBound.Matching

open SteinerLowerBound FiniteAveraging
open scoped Classical BigOperators

variable {V E : Type*} [Fintype E]

namespace Graph

variable (G : Graph V E)

def DegreeGood (t Δ : ℕ) (ρ : Rank E) : Prop :=
  ∀ e ∈ G.residual ρ t, (G.residualNeighbors ρ t e).card ≤ Δ

theorem degreeGood_swap (t Δ : ℕ) (ρ : Rank E) (i j : Fin (Fintype.card E))
    (hi : t ≤ i.val) (hj : t ≤ j.val) :
    G.DegreeGood t Δ (ρ.swapRanks i j) ↔ G.DegreeGood t Δ ρ := by
  simp only [DegreeGood, G.residual_swap ρ t i j hi hj,
    G.residualNeighbors_swap ρ t i j hi hj]

def PositionPath (t Δ : ℕ) (xs : List (Fin (Fintype.card E))) (ρ : Rank E) : Prop :=
  G.DegreeGood t Δ ρ ∧
    (∀ i ∈ xs, ρ.edge i ∈ G.residual ρ t) ∧
    xs.IsChain (fun i j => G.Touch (ρ.edge i) (ρ.edge j))

theorem positionPath_swap (t Δ : ℕ) (xs : List (Fin (Fintype.card E)))
    (ρ : Rank E) (i j : Fin (Fintype.card E))
    (hi : t ≤ i.val) (hj : t ≤ j.val) (hin : i ∉ xs) (hjn : j ∉ xs) :
    G.PositionPath t Δ xs (ρ.swapRanks i j) ↔ G.PositionPath t Δ xs ρ := by
  have he (k : Fin (Fintype.card E)) (hk : k ∈ xs) :
      (ρ.swapRanks i j).edge k = ρ.edge k := by
    rw [Rank.swapRanks_edge, Equiv.swap_apply_of_ne_of_ne]
    · exact fun h => hin (h ▸ hk)
    · exact fun h => hjn (h ▸ hk)
  unfold PositionPath
  rw [G.degreeGood_swap t Δ ρ i j hi hj, G.residual_swap ρ t i j hi hj]
  have hall : (∀ k ∈ xs, (ρ.swapRanks i j).edge k ∈ G.residual ρ t) ↔
      ∀ k ∈ xs, ρ.edge k ∈ G.residual ρ t := by
    constructor <;> intro h k hk <;> simpa only [he k hk] using h k hk
  rw [hall]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply List.IsChain.iff_of_mem_imp
  intro a b ha hb
  simp only [he a ha, he b hb]

theorem positionPath_prefix (t Δ : ℕ) (xs ys : List (Fin (Fintype.card E)))
    (ρ : Rank E) (h : G.PositionPath t Δ (xs ++ ys) ρ) :
    G.PositionPath t Δ xs ρ :=
  ⟨h.1, fun i hi => h.2.1 i (List.mem_append_left _ hi), h.2.2.left_of_append⟩

theorem positionPath_last_neighbor (t Δ : ℕ) (xs : List (Fin (Fintype.card E)))
    (s : Fin (Fintype.card E)) (ρ : Rank E) (hne : xs ≠ [])
    (h : G.PositionPath t Δ (xs ++ [s]) ρ) :
    ρ.edge s ∈ G.residualNeighbors ρ t (ρ.edge (xs.getLast hne)) := by
  apply (G.mem_residualNeighbors ρ t _ _).mpr
  refine ⟨h.2.1 s (by simp), ?_⟩
  exact h.2.2.rel_getLast_head_of_append hne (by simp)

theorem positionPath_choices (t Δ : ℕ) (xs : List (Fin (Fintype.card E)))
    (s : Fin (Fintype.card E)) (ρ : Rank E)
    (hne : xs ≠ []) (hs : t ≤ s.val) (hsn : s ∉ xs) :
    (((Rank.suffix E t) \ xs.toFinset).filter fun j =>
      G.PositionPath t Δ (xs ++ [s]) (ρ.swapRanks s j)).card ≤
      if G.PositionPath t Δ xs ρ then Δ else 0 := by
  classical
  let S := (Rank.suffix E t) \ xs.toFinset
  have hprev (j : Fin (Fintype.card E)) (hj : j ∈ S)
      (h : G.PositionPath t Δ (xs ++ [s]) (ρ.swapRanks s j)) :
      G.PositionPath t Δ xs ρ := by
    obtain ⟨hjS, hjn⟩ := Finset.mem_sdiff.mp hj
    exact (G.positionPath_swap t Δ xs ρ s j hs ((Rank.mem_suffix t j).mp hjS)
      hsn (by simpa using hjn)).mp (G.positionPath_prefix t Δ xs [s] _ h)
  by_cases hbase : G.PositionPath t Δ xs ρ
  · simp only [hbase, ↓reduceIte]
    let e := ρ.edge (xs.getLast hne)
    let A := (G.residualNeighbors ρ t e).image ρ
    have hsub :
        (S.filter fun j => G.PositionPath t Δ (xs ++ [s]) (ρ.swapRanks s j)) ⊆ A := by
      intro j hj
      obtain ⟨hjS, hjP⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjS', hjn⟩ := Finset.mem_sdiff.mp hjS
      have hjt := (Rank.mem_suffix t j).mp hjS'
      have hlasts : xs.getLast hne ≠ s := fun heq =>
        hsn (heq ▸ List.getLast_mem hne)
      have hlastj : xs.getLast hne ≠ j := by
        intro heq
        exact hjn (List.mem_toFinset.mpr (heq ▸ List.getLast_mem hne))
      have hm := G.positionPath_last_neighbor t Δ xs s (ρ.swapRanks s j) hne hjP
      have hms : ρ.edge j ∈ G.residualNeighbors ρ t e := by
        simpa [e, Rank.swapRanks_edge, Equiv.swap_apply_of_ne_of_ne hlasts hlastj,
          G.residualNeighbors_swap ρ t s j hs hjt] using hm
      exact Finset.mem_image.mpr ⟨ρ.edge j, hms, ρ.apply_symm_apply j⟩
    calc
      _ ≤ A.card := Finset.card_le_card hsub
      _ = (G.residualNeighbors ρ t e).card :=
        Finset.card_image_of_injective _ ρ.injective
      _ ≤ Δ := hbase.1 e (hbase.2.1 _ (List.getLast_mem hne))
  · simp only [hbase, ↓reduceIte]
    have heq : (S.filter fun j =>
        G.PositionPath t Δ (xs ++ [s]) (ρ.swapRanks s j)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨hjS, hjP⟩ := Finset.mem_filter.mp hj
      exact hbase (hprev j hjS hjP)
    change (S.filter fun j =>
      G.PositionPath t Δ (xs ++ [s]) (ρ.swapRanks s j)).card ≤ 0
    rw [heq]
    exact Nat.le_refl 0

noncomputable def positionPathProb (t Δ : ℕ) (xs : List (Fin (Fintype.card E))) : ℝ :=
  (Rank.uniform (E := E)).prob {ρ | G.PositionPath t Δ xs ρ}

theorem positionPathProb_step (t Δ r : ℕ) (xs : List (Fin (Fintype.card E)))
    (s : Fin (Fintype.card E)) (hne : xs ≠ [])
    (hs : t ≤ s.val) (hsn : s ∉ xs)
    (hr : 0 < r) (hcard : r ≤ ((Rank.suffix E t) \ xs.toFinset).card) :
    G.positionPathProb t Δ (xs ++ [s]) ≤
      ((Δ : ℝ) / r) * G.positionPathProb t Δ xs := by
  classical
  let S := (Rank.suffix E t) \ xs.toFinset
  let μ := Rank.uniform (E := E)
  have hpoint (ρ : Rank E) :
      ((S.filter fun j => G.PositionPath t Δ (xs ++ [s]) (ρ.swapRanks s j)).card : ℝ) ≤
        (Δ : ℝ) * indicator (G.PositionPath t Δ xs) ρ := by
    have h := G.positionPath_choices t Δ xs s ρ hne hs hsn
    by_cases hB : G.PositionPath t Δ xs ρ <;>
      simpa [S, indicator, hB] using (Nat.cast_le (α := ℝ)).mpr h
  have havg :
      μ.expect (fun ρ => ((S.filter fun j =>
        G.PositionPath t Δ (xs ++ [s]) (ρ.swapRanks s j)).card : ℝ)) =
        (S.card : ℝ) * G.positionPathProb t Δ (xs ++ [s]) := by
    simp only [card_filter_indicator]
    rw [expect_sum]
    change (∑ j ∈ S, μ.expect (fun ρ =>
      indicator (G.PositionPath t Δ (xs ++ [s])) (ρ.swapRanks s j))) = _
    have heq (j : Fin (Fintype.card E)) :
        μ.expect (fun ρ => indicator (G.PositionPath t Δ (xs ++ [s]))
          (ρ.swapRanks s j)) = G.positionPathProb t Δ (xs ++ [s]) := by
      change (Law.uniform (Rank E)).expect (fun ρ =>
        indicator (G.PositionPath t Δ (xs ++ [s])) (Rank.swapEquiv s j ρ)) = _
      rw [uniform_expect_equiv]
      exact expect_indicator _ _
    simp_rw [heq]
    simp
  have hav := μ.expect_mono hpoint
  rw [havg, Law.expect_const_mul, expect_indicator] at hav
  have hnn : 0 ≤ G.positionPathProb t Δ (xs ++ [s]) := Law.prob_nonneg _ _
  have hcr : (r : ℝ) ≤ S.card := by exact_mod_cast hcard
  have hrough : (r : ℝ) * G.positionPathProb t Δ (xs ++ [s]) ≤
      (Δ : ℝ) * G.positionPathProb t Δ xs := by
    exact (mul_le_mul_of_nonneg_right hcr hnn).trans hav
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [div_mul_eq_mul_div, le_div_iff₀ hr']
  simpa [mul_comm] using hrough

theorem positionPathProb_le_pow (t Δ r : ℕ) (xs : List (Fin (Fintype.card E)))
    (hn : xs.Nodup) (hpos : ∀ i ∈ xs, t ≤ i.val)
    (hr : 0 < r) (hreserve : r + t + xs.length ≤ Fintype.card E) :
    G.positionPathProb t Δ xs ≤ ((Δ : ℝ) / r) ^ (xs.length - 1) := by
  classical
  induction xs using List.reverseRecOn with
  | nil =>
    simpa [positionPathProb] using
      (Rank.uniform (E := E)).prob_le_one {ρ | G.PositionPath t Δ [] ρ}
  | append_singleton xs s ih =>
    by_cases he : xs = []
    · subst xs
      simpa [positionPathProb] using
        (Rank.uniform (E := E)).prob_le_one {ρ | G.PositionPath t Δ [s] ρ}
    · have hnx : xs.Nodup := (List.nodup_append.mp hn).1
      have hsn : s ∉ xs := by
        intro h
        exact (List.nodup_append.mp hn).2.2 s h s (by simp) rfl
      have hpx : ∀ i ∈ xs, t ≤ i.val := fun i hi => hpos i (by simp [hi])
      have hs : t ≤ s.val := hpos s (by simp)
      have hsub : xs.toFinset ⊆ Rank.suffix E t := by
        intro i hi
        exact (Rank.mem_suffix t i).mpr (hpx i (List.mem_toFinset.mp hi))
      have hc : r ≤ ((Rank.suffix E t) \ xs.toFinset).card := by
        rw [Finset.card_sdiff_of_subset hsub, Rank.card_suffix,
          List.toFinset_card_of_nodup hnx]
        simp only [List.length_append, List.length_singleton] at hreserve
        omega
      have hres : r + t + xs.length ≤ Fintype.card E := by
        simp only [List.length_append, List.length_singleton] at hreserve
        omega
      have hi := ih hnx hpx hres
      have hq : (0 : ℝ) ≤ (Δ : ℝ) / r := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      calc
        _ ≤ ((Δ : ℝ) / r) * G.positionPathProb t Δ xs :=
          G.positionPathProb_step t Δ r xs s he hs hsn hr hc
        _ ≤ ((Δ : ℝ) / r) * ((Δ : ℝ) / r) ^ (xs.length - 1) :=
          mul_le_mul_of_nonneg_left hi hq
        _ = ((Δ : ℝ) / r) ^ ((xs ++ [s]).length - 1) := by
          rw [← pow_succ']
          congr 1
          have hl := List.length_pos_iff.mpr he
          simp only [List.length_append, List.length_singleton]
          omega

end Graph

end SteinerUpperBound.Matching
