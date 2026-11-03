module

public import SteinerLowerBound.Screening.StarCounterProbability

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

def FirstLucky (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) : Prop :=
  (analyze π F H D t R h).stop = none ∧
    Lucky π H (analyze π F H D t R h).exposed q

theorem advance_lucky_cases (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (s : Book (Terminal S G I))
    (q : Query (Terminal S G I) C)
    (hs : (advance π F H D t R h s q).stop = some .lucky) :
    s.stop = some .lucky ∨ (s.stop = none ∧ Lucky π H s.exposed q) := by
  classical
  by_cases hn : s.stop = none
  · right
    refine ⟨hn, ?_⟩
    by_contra hl
    simp only [advance, hn, ne_eq, not_true_eq_false, hl, ↓reduceIte] at hs
    split_ifs at hs <;> cases hs
  · left
    simpa only [advance, hn, ne_eq, not_false_eq_true, ↓reduceIte] using hs

theorem lucky_stop_charging (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C))
    (hs : (analyze π F H D t R h).stop = some .lucky) :
    1 ≤ historyCharge (fun h q => if FirstLucky π F H D t R h q then 1 else 0) h := by
  classical
  induction h using List.reverseRecOn with
  | nil => simp [Book.initial] at hs
  | append_singleton h q ih =>
      rw [analyze_append] at hs
      rw [historyCharge_append]
      rcases advance_lucky_cases π F H D t R h _ q hs with hs | hs
      · have hh := ih hs
        have hc : (0 : ℝ) ≤ if FirstLucky π F H D t R h q then 1 else 0 := by split_ifs <;> norm_num
        linarith
      · have hc : FirstLucky π F H D t R h q := hs
        rw [if_pos hc]
        have hh := historyCharge_nonneg
          (fun h q => if FirstLucky π F H D t R h q then (1 : ℝ) else 0)
          (fun _ _ => by split_ifs <;> norm_num) h
        linarith

variable {B A : Type*} [Fintype B] [Fintype A] [Fintype C]

theorem firstLucky_expect_prefix
    (μ : Law B) (k : B → C → Law (Option A))
    (F : B → C → Finset (Terminal S G I)) (support : A → Finset (Terminal S G I))
    (hF : ∀ b, Supported (F b)) (hH : ∀ a u, u ∈ support a → specialPosition u)
    (hcard : ∀ b c, (F b c).card ≤ 2)
    (hvalid : ∀ ω, 0 <
      (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).mass ω →
        ∀ c, (starSupports support ω.1.2 c).Nonempty → F ω.1.1 c ⊆ starSupports support ω.1.2 c)
    (p₀ p₁ : ℝ) (hp₀ : 0 ≤ p₀) (hp₁ : 0 ≤ p₁)
    (ha : ∀ b c, 1 / 2 ≤ (k b c).mass none)
    (hmark : ∀ b c, (k b c).prob {a | a ≠ none} ≤ p₀)
    (hvertex : ∀ b c u, u ∉ F b c →
      (k b c).prob {a | u ∈ a.elim ∅ support} ≤ p₁)
    (D t R : ℕ) (hD : 0 < D) (ht : 0 < t)
    (hsize : 0 < (Fintype.card G * Fintype.card I : ℝ) - (3 * t + D * Fintype.card I))
    (r : Record (Query (Terminal S G I) C) Reply) (q : Query (Terminal S G I) C) :
    (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).expect (fun ω =>
      if Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r then
        (if FirstLucky ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R (questions r) q then 1 else 0)
      else 0) ≤
      ((4 * p₀ + 2 * Fintype.card S * p₁) /
        ((Fintype.card G * Fintype.card I : ℝ) - (3 * t + D * Fintype.card I))) *
      (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).prob
        {ω | Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r} := by
  classical
  let ν := shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)
  let E := {ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I) |
    Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r ∧
      FirstLucky ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R (questions r) q}
  have hExpect : ν.expect (fun ω =>
      if Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r then
        (if FirstLucky ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R (questions r) q then 1 else 0)
      else 0) = ν.prob E := by
    simp only [Law.expect, Law.prob, Set.mem_ofPred_eq]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h1 : Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r <;>
      by_cases h2 : FirstLucky ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R (questions r) q <;>
        simp only [E, Set.mem_ofPred_eq, h1, h2, and_self, false_and, and_false, ↓reduceIte, mul_one, mul_zero]
  rw [hExpect]
  let EG := {ω ∈ E | ∀ c, (starSupports support ω.1.2 c).Nonempty →
    F ω.1.1 c ⊆ starSupports support ω.1.2 c}
  have hmono : ν.prob E ≤ ν.prob EG := ν.prob_mono_support
    (fun ω hω hE => ⟨hE, hvalid ω hω⟩)
  have supportH (h : C → Option A) : Supported (starSupports support h) := by
    intro c u hu
    cases he : h c with
    | none => simp [starSupports, he] at hu
    | some a => exact hH a u (by simpa only [starSupports, he, Option.elim_some] using hu)
  have hbound :
      ((Fintype.card G * Fintype.card I : ℝ) - (3 * t + D * Fintype.card I)) * ν.prob EG ≤
        (4 * p₀ + 2 * Fintype.card S * p₁) * ν.prob
          {ω | Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r} := by
    cases q with
    | tt a b =>
        have he : EG = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro ω hω
          obtain ⟨c, u, hq, _⟩ := hω.1.2.2
          cases hq
        rw [he, Law.prob_empty, mul_zero]
        exact mul_nonneg (by positivity) (ν.prob_nonneg _)
    | cc c c' =>
        have he : EG = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro ω hω
          obtain ⟨c, u, hq, _⟩ := hω.1.2.2
          cases hq
        rw [he, Law.prob_empty, mul_zero]
        exact mul_nonneg (by positivity) (ν.prob_nonneg _)
    | ct c u =>
        apply lucky_candidate_prefix_bound μ k F support hF hH hcard p₀ p₁ hp₀ hp₁
          ha hmark hvertex r c u (3 * t + D * Fintype.card I) hsize.le EG
        intro ω hω
        obtain ⟨c', u', hq, hs, hout, huH⟩ := hω.1.2.2
        obtain ⟨hc, hu⟩ := Query.ct.inj hq
        subst c'
        subst u'
        have hn := hω.1.2.1
        refine ⟨hω.1.1, screenable_before_stop _ _ _ D t R hD ht
          (hF ω.1.1) (supportH ω.1.2) (questions r) hn u hs hout,
            low_positive_before_lucky _ _ _ D t R (hF ω.1.1) (supportH ω.1.2)
              (hcard ω.1.1) hω.2 (questions r) hn c u hout huH, huH⟩
  have hmul := mul_le_mul_of_nonneg_left hmono hsize.le
  have hh : ν.prob E ≤
      ((4 * p₀ + 2 * Fintype.card S * p₁) *
        ν.prob {ω | Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r}) /
      ((Fintype.card G * Fintype.card I : ℝ) - (3 * t + D * Fintype.card I)) := by
    apply (le_div_iff₀ hsize).mpr
    nlinarith [hbound, hmul]
  simpa only [div_mul_eq_mul_div] using hh

theorem lucky_stop_probability_explicit {Z : Type*}
    (μ : Law B) (k : B → C → Law (Option A))
    (F : B → C → Finset (Terminal S G I)) (support : A → Finset (Terminal S G I))
    (hF : ∀ b, Supported (F b)) (hH : ∀ a u, u ∈ support a → specialPosition u)
    (hcard : ∀ b c, (F b c).card ≤ 2)
    (hvalid : ∀ ω, 0 <
      (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).mass ω →
        ∀ c, (starSupports support ω.1.2 c).Nonempty → F ω.1.1 c ⊆ starSupports support ω.1.2 c)
    (p₀ p₁ : ℝ) (hp₀ : 0 ≤ p₀) (hp₁ : 0 ≤ p₁)
    (ha : ∀ b c, 1 / 2 ≤ (k b c).mass none)
    (hmark : ∀ b c, (k b c).prob {a | a ≠ none} ≤ p₀)
    (hvertex : ∀ b c u, u ∉ F b c →
      (k b c).prob {a | u ∈ a.elim ∅ support} ≤ p₁)
    (D t R q : ℕ) (hD : 0 < D) (ht : 0 < t)
    (hsize : 0 < (Fintype.card G * Fintype.card I : ℝ) - (3 * t + D * Fintype.card I))
    (tree : SteinerLowerBound.DecisionTree (Query (Terminal S G I) C) Reply Z)
    (hquery : DecisionTree.Bounded tree q) :
    (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).prob {ω |
      (analyze ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R
        (questions (DecisionTree.run
          (fun ω => queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) ω [] tree))).stop =
            some .lucky} ≤
      ((4 * p₀ + 2 * Fintype.card S * p₁) /
        ((Fintype.card G * Fintype.card I : ℝ) - (3 * t + D * Fintype.card I))) * q := by
  classical
  let ν := shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)
  let answer := fun ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I) =>
    queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)
  let cost := fun (ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I))
      (h : List (Query (Terminal S G I) C)) q =>
    if FirstLucky ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R h q then (1 : ℝ) else 0
  let V := (4 * p₀ + 2 * Fintype.card S * p₁) /
    ((Fintype.card G * Fintype.card I : ℝ) - (3 * t + D * Fintype.card I))
  let f := fun ω => historyCharge (cost ω) (questions (DecisionTree.run answer ω [] tree))
  have hcharge := DecisionTree.charging ν answer (fun ω r q => cost ω (questions r) q)
    (fun _ _ => 1) V (by
      intro r q
      simpa only [ν, answer, cost, V, mul_one] using
        (firstLucky_expect_prefix μ k F support hF hH hcard hvalid p₀ p₁ hp₀ hp₁
          ha hmark hvertex D t R hD ht hsize r q)) tree []
  simp only [compatible_nil, ↓reduceIte] at hcharge
  have hone : ν.expect (fun ω =>
      DecisionTree.accumulate answer (fun _ _ _ => 1) ω [] tree) ≤ q :=
    (ν.expect_mono (fun ω => DecisionTree.accumulate_one_le answer ω tree q hquery [])).trans_eq
      (ν.expect_const _)
  have hV : 0 ≤ V := div_nonneg (by positivity) hsize.le
  have hf : ν.expect f ≤ V * q := by
    have he (ω) : f ω =
        DecisionTree.accumulate answer (fun ω r q => cost ω (questions r) q) ω [] tree := by
      simpa only [questions, List.map_nil, historyCharge_nil, zero_add, f] using
        historyCharge_run answer cost ω [] tree
    rw [show f = (fun ω => DecisionTree.accumulate answer
      (fun ω r q => cost ω (questions r) q) ω [] tree) from funext he]
    exact hcharge.trans (mul_le_mul_of_nonneg_left hone hV)
  have hmono := ν.prob_mono
    (show {ω | (analyze ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R
        (questions (DecisionTree.run answer ω [] tree))).stop = some .lucky} ⊆
      {ω | 1 ≤ f ω} from by
        intro ω hω
        exact lucky_stop_charging ω.2 (F ω.1.1) (starSupports support ω.1.2)
          D t R (questions (DecisionTree.run answer ω [] tree)) hω)
  have hm := ν.markov (f := f) (fun ω => historyCharge_nonneg (cost ω)
    (fun _ _ => by dsimp only [cost]; split_ifs <;> norm_num) _) (by norm_num : (0 : ℝ) < 1)
  exact hmono.trans (by simpa only [div_one] using hm.trans (by simpa only [div_one] using hf))

end Screening

end SteinerLowerBound
