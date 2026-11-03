module

public import SteinerLowerBound.Screening.LuckyStop
public import SteinerLowerBound.Screening.Rates

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

theorem cluster_stop_marks (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C))
    (hs : (analyze π F H D t R h).stop = some .cluster) :
    t ≤ (marked π h).card := by
  classical
  induction h using List.reverseRecOn with
  | nil => simp [Book.initial] at hs
  | append_singleton h q ih =>
      rw [analyze_append] at hs
      let s := analyze π F H D t R h
      change (advance π F H D t R h s q).stop = some .cluster at hs
      by_cases hn : s.stop = none
      · by_contra hm
        simp only [advance, hn, ne_eq, not_true_eq_false, hm, ↓reduceIte] at hs
        split_ifs at hs <;> cases hs
      · have he : advance π F H D t R h s q = s := by
          simp only [advance, hn, ne_eq, not_false_eq_true, ↓reduceIte]
        rw [he] at hs
        exact (ih hs).trans (Finset.card_le_card (marked_mono_append π h q))

theorem notice_stop_card (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C))
    (hs : (analyze π F H D t R h).stop = some .notices) :
    R < (analyze π F H D t R h).noticed.card := by
  classical
  induction h using List.reverseRecOn with
  | nil => simp [Book.initial] at hs
  | append_singleton h q ih =>
      rw [analyze_append] at hs ⊢
      let s := analyze π F H D t R h
      change (advance π F H D t R h s q).stop = some .notices at hs
      change R < (advance π F H D t R h s q).noticed.card
      by_cases hn : s.stop = none
      · by_cases hl : Lucky π H s.exposed q
        · simp only [advance, hn, ne_eq, not_true_eq_false, hl, ↓reduceIte] at hs
          cases hs
        · have hN : (advance π F H D t R h s q).noticed =
              (addNotices (relabel π F) (relabel π H) s
                (noticeOrder (noticeCandidates π F H D t h q s.exposed))).noticed := by
            simp only [advance, hn, ne_eq, not_true_eq_false, hl, ↓reduceIte]
          rw [hN]
          by_contra hnot
          simp only [advance, hn, ne_eq, not_true_eq_false, hl, hnot, ↓reduceIte] at hs
          split_ifs at hs <;> cases hs
      · have he : advance π F H D t R h s q = s := by
          simp only [advance, hn, ne_eq, not_false_eq_true, ↓reduceIte]
        rw [he] at hs ⊢
        exact ih hs

variable {B A : Type*} [Fintype B] [Fintype A] [Fintype C]

theorem screening_probability_explicit {Z : Type*}
    (μ : Law B) (k : B → C → Law (Option A))
    (F : B → C → Finset (Terminal S G I)) (support : A → Finset (Terminal S G I))
    (hF : ∀ b, Supported (F b)) (hH : ∀ a u, u ∈ support a → specialPosition u)
    (d : ℕ) (hcardF : ∀ b c, (F b c).card ≤ 2) (hcardH : ∀ a, (support a).card ≤ d)
    (hvalid : ∀ ω, 0 <
      (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).mass ω →
        ∀ c, (starSupports support ω.1.2 c).Nonempty → F ω.1.1 c ⊆ starSupports support ω.1.2 c)
    (p₀ p₁ : ℝ) (hp₀ : 0 ≤ p₀) (hp₁ : 0 ≤ p₁)
    (ha : ∀ b c, 1 / 2 ≤ (k b c).mass none)
    (hmark : ∀ b c, (k b c).prob {a | a ≠ none} ≤ p₀)
    (hvertex : ∀ b c u, u ∉ F b c →
      (k b c).prob {a | u ∈ a.elim ∅ support} ≤ p₁)
    (D t R q : ℕ) (hD : 0 < D) (ht : 0 < t) (hR : 0 < R)
    (hcluster : 0 < (Fintype.card G * Fintype.card I : ℝ) -
      (Fintype.card I + 2 * t + D * Fintype.card I))
    (hspecial : 0 < (Fintype.card G * Fintype.card I : ℝ) -
      (3 * t + D * Fintype.card I))
    (tree : SteinerLowerBound.DecisionTree (Query (Terminal S G I) C) Reply Z)
    (hquery : DecisionTree.Bounded tree q) :
    (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).prob {ω |
      let stop := (analyze ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R
        (questions (DecisionTree.run
          (fun ω => queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) ω [] tree))).stop
      stop ≠ none ∧ stop ≠ some .closure} ≤
      (2 * q / D + 2 * q * Fintype.card I / t +
        (2 * Fintype.card I /
          ((Fintype.card G * Fintype.card I : ℝ) -
            (Fintype.card I + 2 * t + D * Fintype.card I))) * q) / t +
      2 * d * p₀ * q / t +
      ((4 * p₀ + 2 * Fintype.card S * p₁) /
        ((Fintype.card G * Fintype.card I : ℝ) - (3 * t + D * Fintype.card I))) * q +
      ((2 * q + 2 * Fintype.card S * q / D) /
        ((Fintype.card G * Fintype.card I : ℝ) - (3 * t + D * Fintype.card I)) +
          2 * q / t) / R := by
  classical
  let ν := shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)
  let final := fun ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I) =>
    questions (DecisionTree.run (fun ω => queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) ω [] tree)
  let state := fun ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I) =>
    analyze ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R (final ω)
  let EC := {ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I) |
    t ≤ (marked ω.2 (final ω)).card}
  let EH := {ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I) |
    (state ω).stop = some .starCounter}
  let EL := {ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I) |
    (state ω).stop = some .lucky}
  let EN := {ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I) |
    R < (state ω).noticed.card}
  have supportH (x : B × (C → Option A)) : Supported (starSupports support x.2) := by
    intro c u hu
    cases he : x.2 c with
    | none => simp [starSupports, he] at hu
    | some a => exact hH a u (by simpa only [starSupports, he, Option.elim_some] using hu)
  have hC := cluster_stop_probability_explicit (Law.conditionalProduct μ k)
    (fun x => F x.1) (fun x => starSupports support x.2) (fun x => hF x.1) supportH
    D t q hD ht hcluster tree hquery
  have hHbound := star_counter_probability_explicit μ k F support hF hH d hcardF hcardH hvalid
    p₀ hp₀ ha hmark D t R q ht tree hquery
  have hL := lucky_stop_probability_explicit μ k F support hF hH hcardF hvalid
    p₀ p₁ hp₀ hp₁ ha hmark hvertex D t R q hD ht hspecial tree hquery
  have hN := notice_overflow_probability_explicit (Law.conditionalProduct μ k)
    (fun x => F x.1) (fun x => starSupports support x.2) (fun x => hF x.1) supportH
    (fun x c => hcardF x.1 c) D t R q hD ht hR hspecial tree hquery
  have hsub : {ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I) |
      (state ω).stop ≠ none ∧ (state ω).stop ≠ some .closure} ⊆ EC ∪ EH ∪ EL ∪ EN := by
    intro ω hω
    cases he : (state ω).stop with
    | none => exact False.elim (hω.1 he)
    | some kind =>
        cases kind with
        | closure => exact False.elim (hω.2 he)
        | cluster =>
            exact Or.inl (Or.inl (Or.inl
              (cluster_stop_marks ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R (final ω) he)))
        | starCounter => exact Or.inl (Or.inl (Or.inr he))
        | lucky => exact Or.inl (Or.inr he)
        | notices => exact Or.inr (notice_stop_card _ _ _ D t R (final ω) he)
  have hU1 := ν.prob_union_le (EC ∪ EH ∪ EL) EN
  have hU2 := ν.prob_union_le (EC ∪ EH) EL
  have hU3 := ν.prob_union_le EC EH
  have hmono := ν.prob_mono hsub
  change ν.prob _ ≤ _
  dsimp only [ν, EC, EH, EL, EN, state, final] at *
  linarith

end Screening

namespace Screening.Experiment

open HardDistribution

variable {S G I C W : Type*}
  [Fintype S] [Fintype G] [Fintype I] [Fintype C] [Fintype W]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

abbrev Configuration (k : Setup S W) :=
  (Base S C W × (C → Option (Subsets S k.d))) × Equiv.Perm (Terminal S G I)

noncomputable def gatedAnswer (k : Setup S W) (ω : Configuration (G := G) (I := I) (C := C) k) :
    List (Query (Terminal S G I) C) → Query (Terminal S G I) C → Reply :=
  queryAnswer ω.2 (fillers ω.1.1) (starSupports (starSupport k.d) ω.1.2)

def failure {Z : Type*} (k : Setup S W)
    (tree : SteinerLowerBound.DecisionTree (Query (Terminal S G I) C) Reply Z)
    (ω : Configuration (G := G) (I := I) (C := C) k) : Prop :=
  let stop := (analyze ω.2 (fillers ω.1.1) (starSupports (starSupport k.d) ω.1.2)
    (Fintype.card G / 16) ((Fintype.card G * Fintype.card I + 15) / 16) (Fintype.card I)
    (questions (DecisionTree.run (gatedAnswer k) ω [] tree))).stop
  stop ≠ none ∧ stop ≠ some .closure

theorem kernel_lifted_vertex_le (k : Setup S W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) (hm : 4 ≤ Fintype.card S)
    (hB₁ : 0 ≤ vertexConstant k.d k.H0 k.M)
    (b : Base S C W) (c : C) (u : Terminal S G I) (hu : u ∉ fillers b c) :
    (kernel k hsmall b c).prob {a | u ∈ a.elim ∅ (starSupport k.d)} ≤
      vertexConstant k.d k.H0 k.M / (k.R * Fintype.card S) := by
  classical
  cases u with
  | inl v =>
      have hv : v ∉ fillerNeighbors (b.2 c) := by
        simpa only [fillers, mem_liftSpecial] using hu
      have he : {a : Option (Subsets S k.d) | Sum.inl v ∈ a.elim ∅ (starSupport (G := G) (I := I) k.d)} =
          {a | v ∈ a.elim ∅ Subtype.val} := by
        ext a
        cases a <;> simp [starSupport, mem_liftSpecial]
      rw [he]
      exact kernel_vertex_le k hsmall hm b c v hv
  | inr p =>
      have he : {a : Option (Subsets S k.d) | Sum.inr p ∈ a.elim ∅ (starSupport (G := G) (I := I) k.d)} = ∅ := by
        ext a
        cases a <;> simp [starSupport]
      rw [he, Law.prob_empty]
      exact div_nonneg hB₁ (mul_nonneg k.R_pos.le (Nat.cast_nonneg _))

/-- Screening for the actual two-anchor experiment, with the paper's `1/16`
thresholds and all four non-closure first stops included. -/
theorem screening_two_anchor {Z : Type*}
    (k : Setup S W) (μ : Law W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (hhalf : anchorConstant k.d k.H0 k.M / k.R ≤ 1 / 2)
    (hm : Fintype.card S = k.d * Fintype.card G)
    (hA : 64 ≤ Fintype.card G) (hR : 0 < Fintype.card I)
    (hRsize : k.R = Fintype.card I)
    (q : ℕ) (tree : SteinerLowerBound.DecisionTree (Query (Terminal S G I) C) Reply Z)
    (hquery : DecisionTree.Bounded tree q) :
    (law k μ hsmall).prob (failure k tree) ≤
      screeningConstant k.d (anchorConstant k.d k.H0 k.M) (vertexConstant k.d k.H0 k.M) *
        ((q : ℝ) / (Fintype.card G * (Fintype.card G * Fintype.card I)) +
          (q : ℝ) / ((Fintype.card G * Fintype.card I) * Fintype.card I)) := by
  classical
  let A := Fintype.card G
  let R := Fintype.card I
  let K := A * R
  let D := A / 16
  let t := (K + 15) / 16
  let B₀ := anchorConstant k.d k.H0 k.M
  let B₁ := vertexConstant k.d k.H0 k.M
  let Fc : ℝ := (A : ℝ) * R - (R + 2 * t + D * R)
  let Fs : ℝ := (A : ℝ) * R - (3 * t + D * R)
  have hw : Nonempty W := by
    by_contra hn
    haveI : IsEmpty W := not_nonempty_iff.mp hn
    have ht := μ.total
    simp at ht
  obtain ⟨w₀⟩ := hw
  have hM : 0 ≤ k.M := (k.bounded w₀).1.trans (k.bounded w₀).2
  have hH₀ := k.H0_nonneg
  have hB₀ : 0 ≤ B₀ := by dsimp only [B₀, anchorConstant]; positivity
  have hB₁ : 0 ≤ B₁ := by dsimp only [B₁, vertexConstant]; positivity
  have hsizes := threshold_sizes A R hA hR
  have hD : 0 < D := hsizes.1
  have ht : 0 < t := hsizes.2.1
  have hA' : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hK' : (0 : ℝ) < (A : ℝ) * R := mul_pos hA' hR'
  have hm4 : 4 ≤ Fintype.card S := by
    rw [hm]
    have hd := k.d_ge_three
    change 64 ≤ A at hA
    nlinarith
  have hm' : (0 : ℝ) < Fintype.card S := by exact_mod_cast (by omega : 0 < Fintype.card S)
  have hFc : ((A : ℝ) * R) / 2 ≤ Fc := by
    have hh : (2 : ℝ) * (R + 2 * t + D * R) ≤ (A : ℝ) * R := by
      exact_mod_cast hsizes.2.2.2.2.1
    dsimp only [Fc]
    linarith
  have hFs : ((A : ℝ) * R) / 2 ≤ Fs := by
    have hh : (2 : ℝ) * (3 * t + D * R) ≤ (A : ℝ) * R := by
      exact_mod_cast hsizes.2.2.2.2.2
    dsimp only [Fs]
    linarith
  have hFcp : 0 < Fc := lt_of_lt_of_le (by positivity) hFc
  have hFsp : 0 < Fs := lt_of_lt_of_le (by positivity) hFs
  have hp₀ : 0 ≤ B₀ / k.R := div_nonneg hB₀ k.R_pos.le
  have hp₁ : 0 ≤ B₁ / (k.R * Fintype.card S) :=
    div_nonneg hB₁ (mul_nonneg k.R_pos.le (Nat.cast_nonneg _))
  have hscreen := screening_probability_explicit
    (baseLaw (C := C) k μ) (kernel k hsmall)
    (fillers (G := G) (I := I)) (starSupport (G := G) (I := I) k.d)
    (fun b => fillers_supported b) (stars_supported k.d) k.d
    (fun b c => fillers_card b c)
    (by intro a; simpa only [starSupport, card_liftSpecial, a.property] using Nat.le_refl k.d)
    (positive_configuration_anchor_support k μ hsmall)
    (B₀ / k.R) (B₁ / (k.R * Fintype.card S)) hp₀ hp₁
    (kernel_absent_ge_half k hsmall hhalf) (kernel_present_le k hsmall)
    (kernel_lifted_vertex_le k hsmall hm4 hB₁)
    D t R q hD ht hR hFcp hFsp tree hquery
  have hrate := screening_rate_bound
    (k.d : ℝ) (Fintype.card S : ℝ) (A : ℝ) (R : ℝ) ((A : ℝ) * R)
    (D : ℝ) (t : ℝ) Fc Fs (q : ℝ) B₀ B₁
    (Nat.cast_nonneg _) hm' hA' hR'
    (by exact_mod_cast hD) (by exact_mod_cast ht) (Nat.cast_nonneg _)
    hB₀ hB₁ rfl (by exact_mod_cast hm)
    (by exact_mod_cast hsizes.2.2.1) (by exact_mod_cast hsizes.2.2.2.1) hFc hFs
  rw [hRsize] at hscreen
  have hfinal := hscreen.trans hrate
  have horacle : gatedAnswer (G := G) (I := I) (C := C) k =
      (fun ω => queryAnswer ω.2 (fillers ω.1.1) (starSupports (starSupport k.d) ω.1.2)) := by
    funext ω
    rfl
  change (law k μ hsmall).prob {ω | failure k tree ω} ≤ _
  simp only [failure, horacle]
  simpa only [law, A, R, K, D, t, B₀, B₁, Fc, Fs] using hfinal

end Screening.Experiment

end SteinerLowerBound
