module

public import SteinerLowerBound.Screening.StarKernel

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {B A C S G I : Type*}
  [Fintype B] [Fintype A] [Fintype C] [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

theorem lucky_candidate_prefix_bound
    (μ : Law B) (k : B → C → Law (Option A))
    (F : B → C → Finset (Terminal S G I)) (support : A → Finset (Terminal S G I))
    (hF : ∀ b, Supported (F b))
    (hH : ∀ a u, u ∈ support a → specialPosition u)
    (hcard : ∀ b c, (F b c).card ≤ 2)
    (p₀ p₁ : ℝ) (hp₀ : 0 ≤ p₀) (hp₁ : 0 ≤ p₁)
    (ha : ∀ b c, 1 / 2 ≤ (k b c).mass none)
    (hmark : ∀ b c, (k b c).prob {a | a ≠ none} ≤ p₀)
    (hvertex : ∀ b c u, u ∉ F b c →
      (k b c).prob {a | u ∈ a.elim ∅ support} ≤ p₁)
    (r : Record (Query (Terminal S G I) C) Reply)
    (c : C) (u : Terminal S G I) (L : ℝ)
    (hsize : 0 ≤ (Fintype.card G * Fintype.card I : ℝ) - L)
    (E : Set ((B × (C → Option A)) × Equiv.Perm (Terminal S G I)))
    (hE : ∀ ω ∈ E,
      Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r ∧
      Screenable ω.2 (F ω.1.1) (starSupports support ω.1.2) (questions r) u L ∧
      (TwoAnchor.positives (relabel ω.2 (F ω.1.1))
        (relabel ω.2 (starSupports support ω.1.2)) (centerHistory (questions r)) c).card ≤ 2 ∧
      ω.2 u ∈ starSupports support ω.1.2 c) :
    ((Fintype.card G * Fintype.card I : ℝ) - L) *
        (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).prob E ≤
      (4 * p₀ + 2 * Fintype.card S * p₁) *
        (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).prob
          {ω | Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r} := by
  classical
  let ν := shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)
  let μ₀ := (Law.conditionalProduct μ k).map (eraseData c)
  let ν₀ := shuffledLaw (T := Terminal S G I) μ₀
  let P := {ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I) |
    Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r}
  let E₀ := {ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I) |
    ω ∈ P ∧ Screenable ω.2 (F ω.1.1) (starSupports support ω.1.2) (questions r) u L}
  let E₀F := {ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I) |
    ω ∈ E₀ ∧ ω.2 u ∈ F ω.1.1 c}
  let EF := {ω ∈ E | ω.2 u ∈ F ω.1.1 c}
  let EN := {ω ∈ E | ω.2 u ∉ F ω.1.1 c}
  have deleted (ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I)) (hω : ω ∈ E) :
      (eraseData c ω.1, ω.2) ∈ E₀ := by
    have hs := hE ω hω
    change Compatible (queryAnswer ω.2 (F ω.1.1)
      (starSupports support (Function.update ω.1.2 c none))) r ∧
      Screenable ω.2 (F ω.1.1) (starSupports support (Function.update ω.1.2 c none))
        (questions r) u L
    rw [starSupports_erase]
    exact ⟨erase_compatible _ _ _ r c hs.2.2.1 hs.1,
      erase_screenable _ _ _ _ u L c hs.2.1⟩
  have hEF : ν.prob EF ≤ p₀ * ν₀.prob E₀F := by
    apply shuffled_erasure_mark μ k c (fun _ _ => {a | a ≠ none}) p₀ hp₀
      (fun b _ => hmark b c) EF E₀F
    intro ω hω
    refine ⟨?_, deleted ω hω.1, hω.2⟩
    intro hz
    have huH := (hE ω hω.1).2.2.2
    simp only [starSupports, hz, Option.elim_none, Finset.notMem_empty] at huH
  have hEN : ν.prob EN ≤ p₁ * ν₀.prob E₀ := by
    let M := fun b (π : Equiv.Perm (Terminal S G I)) =>
      if π u ∈ F b c then ∅ else {a : Option A | π u ∈ a.elim ∅ support}
    apply shuffled_erasure_mark μ k c M p₁ hp₁
    · intro b π
      by_cases hu : π u ∈ F b c
      · simpa only [M, hu, ↓reduceIte, Law.prob_empty] using hp₁
      · exact by simpa only [M, hu, ↓reduceIte] using hvertex b c (π u) hu
    · intro ω hω
      refine ⟨?_, deleted ω hω.1⟩
      simpa only [M, hω.2, ↓reduceIte, Set.mem_ofPred_eq, starSupports] using
        (hE ω hω.1).2.2.2
  have supportF : ∀ x : B × (C → Option A), Supported (F x.1) := fun x => hF x.1
  have supportH : ∀ x : B × (C → Option A), Supported (starSupports support x.2) := by
    intro x c' v hv
    cases he : x.2 c' with
    | none => simp [starSupports, he] at hv
    | some a => exact hH a v (by simpa only [starSupports, he, Option.elim_some] using hv)
  have hFbound :
      ((Fintype.card G * Fintype.card I : ℝ) - L) * ν₀.prob E₀F ≤ 2 * ν₀.prob P := by
    have hh := anchor_prefix_bound μ₀ (fun x => F x.1) (fun x => starSupports support x.2)
      supportF supportH (fun x c => hcard x.1 c) (questions r)
      (fun i => (r[i.val]'(by simpa [questions] using i.isLt)).2) u c L
    have heq : E₀F = {ω | Compatible
        (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r ∧
      Screenable ω.2 (F ω.1.1) (starSupports support ω.1.2) (questions r) u L ∧
        ω.2 u ∈ F ω.1.1 c} := by
      ext ω
      simp only [E₀F, E₀, P, Set.mem_ofPred_eq, and_assoc]
    rw [heq]
    simpa only [← compatible_iff_observations, ν₀, P] using hh
  have hSbound :
      ((Fintype.card G * Fintype.card I : ℝ) - L) * ν₀.prob E₀ ≤
        Fintype.card S * ν₀.prob P := by
    have hh := special_prefix_bound μ₀ (fun x => F x.1) (fun x => starSupports support x.2)
      supportF supportH (questions r)
      (fun i => (r[i.val]'(by simpa [questions] using i.isLt)).2) u L
    simpa only [← compatible_iff_observations, ν₀, E₀, P, Set.mem_ofPred_eq] using hh
  have hdom : ν₀.prob P ≤ 2 * ν.prob P := by
    have hh := shuffled_erasure_domination μ k c (1 / 2) (by norm_num)
      (fun b => ha b c) P
    dsimp only [ν₀, μ₀, ν] at *
    linarith
  have hsplit : ν.prob E ≤ ν.prob EF + ν.prob EN := by
    have heq : E = EF ∪ EN := by
      ext ω
      simp only [EF, EN, Set.mem_ofPred_eq, Set.mem_union]
      tauto
    rw [heq]
    exact ν.prob_union_le _ _
  calc
    _ ≤ ((Fintype.card G * Fintype.card I : ℝ) - L) *
        (ν.prob EF + ν.prob EN) := mul_le_mul_of_nonneg_left hsplit hsize
    _ ≤ ((Fintype.card G * Fintype.card I : ℝ) - L) *
        (p₀ * ν₀.prob E₀F + p₁ * ν₀.prob E₀) :=
      mul_le_mul_of_nonneg_left (add_le_add hEF hEN) hsize
    _ = p₀ * (((Fintype.card G * Fintype.card I : ℝ) - L) * ν₀.prob E₀F) +
        p₁ * (((Fintype.card G * Fintype.card I : ℝ) - L) * ν₀.prob E₀) := by ring
    _ ≤ p₀ * (2 * ν₀.prob P) + p₁ * (Fintype.card S * ν₀.prob P) :=
      add_le_add (mul_le_mul_of_nonneg_left hFbound hp₀)
        (mul_le_mul_of_nonneg_left hSbound hp₁)
    _ = (2 * p₀ + Fintype.card S * p₁) * ν₀.prob P := by ring
    _ ≤ (2 * p₀ + Fintype.card S * p₁) * (2 * ν.prob P) :=
      mul_le_mul_of_nonneg_left hdom (by positivity)
    _ = _ := by dsimp only [ν, P]; ring

end Screening

end SteinerLowerBound
