module

public import SteinerUpperBound.Matching.RandomPaths

@[expose] public section

namespace SteinerUpperBound.Matching

open SteinerLowerBound FiniteAveraging
open scoped Classical BigOperators

variable {V E : Type*} [Fintype E]

namespace Rank

noncomputable def window (E : Type*) [Fintype E] (t b : ℕ) :
    Finset (Fin (Fintype.card E)) :=
  Finset.univ.filter fun i => t ≤ i.val ∧ i.val < t + b

@[simp] theorem mem_window (t b : ℕ) (i : Fin (Fintype.card E)) :
    i ∈ window E t b ↔ t ≤ i.val ∧ i.val < t + b := by simp [window]

theorem card_window_le (t b : ℕ) : (window E t b).card ≤ b := by
  classical
  have hsub : (window E t b).image Fin.val ⊆ Finset.Ico t (t + b) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_Ico.mpr ((mem_window t b j).mp hj)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Ico] at hc
  simpa using hc

end Rank

namespace Graph

variable (G : Graph V E)

def HasWindowPath (t b Δ L : ℕ) (ρ : Rank E) : Prop :=
  ∃ s ∈ (Rank.window E t b).powersetCard L,
    G.PositionPath t Δ (s.sort (· ≤ ·)) ρ

theorem hasWindowPath_tail (t b Δ L r : ℕ)
    (hr : 0 < r) (hreserve : r + t + L ≤ Fintype.card E) :
    (Rank.uniform (E := E)).prob {ρ | G.HasWindowPath t b Δ L ρ} ≤
      ((b.choose L : ℕ) : ℝ) * ((Δ : ℝ) / r) ^ (L - 1) := by
  classical
  let J := (Rank.window E t b).powersetCard L
  let μ := Rank.uniform (E := E)
  have heq : {ρ | G.HasWindowPath t b Δ L ρ} =
      {ρ | ∃ s : ↥J, G.PositionPath t Δ (s.val.sort (· ≤ ·)) ρ} := by
    ext ρ
    constructor
    · rintro ⟨s, hs, hp⟩
      exact ⟨⟨s, hs⟩, hp⟩
    · rintro ⟨s, hp⟩
      exact ⟨s.val, s.property, hp⟩
  have hbound (s : ↥J) :
      μ.prob {ρ | G.PositionPath t Δ (s.val.sort (· ≤ ·)) ρ} ≤
        ((Δ : ℝ) / r) ^ (L - 1) := by
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp s.property
    have hlen : (s.val.sort (· ≤ ·)).length = L := by
      rw [Finset.length_sort, hcard]
    have hpos : ∀ i ∈ s.val.sort (· ≤ ·), t ≤ i.val := by
      intro i hi
      have hi' : i ∈ s.val := by simpa using hi
      exact ((Rank.mem_window t b i).mp (hsub hi')).1
    have hh := G.positionPathProb_le_pow t Δ r (s.val.sort (· ≤ ·))
      (Finset.sort_nodup _ _) hpos hr (by simpa only [hlen] using hreserve)
    simpa only [positionPathProb, hlen] using hh
  have hcount : (J.card : ℝ) ≤ b.choose L := by
    rw [Finset.card_powersetCard]
    exact_mod_cast Nat.choose_le_choose L (Rank.card_window_le (E := E) t b)
  rw [heq]
  calc
    _ ≤ ∑ s : ↥J, μ.prob {ρ | G.PositionPath t Δ (s.val.sort (· ≤ ·)) ρ} :=
      Law.finite_union_bound _ _
    _ ≤ ∑ _s : ↥J, ((Δ : ℝ) / r) ^ (L - 1) :=
      Finset.sum_le_sum fun s _ => hbound s
    _ = (J.card : ℝ) * ((Δ : ℝ) / r) ^ (L - 1) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (pow_nonneg
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)

theorem hasWindowPath_factorial_tail (t b Δ L r : ℕ)
    (hL : 0 < L) (hr : 0 < r) (hreserve : r + t + L ≤ Fintype.card E) :
    (Rank.uniform (E := E)).prob {ρ | G.HasWindowPath t b Δ L ρ} ≤
      (b : ℝ) * ((b : ℝ) * ((Δ : ℝ) / r)) ^ (L - 1) / L.factorial := by
  have hq : (0 : ℝ) ≤ ((Δ : ℝ) / r) ^ (L - 1) :=
    pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
  calc
    _ ≤ ((b.choose L : ℕ) : ℝ) * ((Δ : ℝ) / r) ^ (L - 1) :=
      G.hasWindowPath_tail t b Δ L r hr hreserve
    _ ≤ ((b : ℝ) ^ L / L.factorial) * ((Δ : ℝ) / r) ^ (L - 1) :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div L b) hq
    _ = _ := by
      have hb : (b : ℝ) ^ L = (b : ℝ) * (b : ℝ) ^ (L - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hb, mul_pow]
      ring

theorem degreeGood_failure (t Δ : ℕ) :
    (Rank.uniform (E := E)).prob {ρ | ¬ G.DegreeGood t Δ ρ} ≤
      Fintype.card E * Real.exp (-((Δ + 1 : ℕ) : ℝ) * t / Fintype.card E) := by
  have heq : {ρ | ¬ G.DegreeGood t Δ ρ} =
      {ρ | ∃ e, G.HighResidual e (Δ + 1) t ρ} := by
    ext ρ
    simp only [DegreeGood, HighResidual, Set.mem_ofPred_eq]
    push Not
    constructor
    · rintro ⟨e, he, hc⟩
      exact ⟨e, he, by omega⟩
    · rintro ⟨e, he, hc⟩
      exact ⟨e, he, by omega⟩
  rw [heq]
  exact G.maxResidualDegree_tail (Δ + 1) t

end Graph

end SteinerUpperBound.Matching
