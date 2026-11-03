module

public import SteinerLowerBound.Screening.StarCounters

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {B A C S G I : Type*}
  [Fintype B] [Fintype A] [Fintype C] [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

theorem relevantIncrements_source (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C)
    (u : Terminal S G I) (hu : u ∈ relevantIncrements π F H D t R h q) :
    (analyze π F H D t R h).stop = none ∧
      u ∉ (analyze π F H D t R h).exposed ∧
        ∃ c x, q = .ct c x ∧ π u ∈ H c := by
  classical
  dsimp only [relevantIncrements] at hu
  split_ifs at hu with hg
  · have hs := (Finset.mem_filter.mp hu).2
    exact ⟨hg.1, hs.1, counter_increment_source π H h q u hs.2⟩
  · simp at hu

theorem relevantIncrements_ct_bound
    (π : Equiv.Perm (Terminal S G I))
    (F : C → Finset (Terminal S G I)) (support : A → Finset (Terminal S G I))
    (hstars : C → Option A) (d D t R : ℕ)
    (hF : Supported F) (hH : ∀ a u, u ∈ support a → specialPosition u)
    (hcardF : ∀ c, (F c).card ≤ 2) (hcardH : ∀ a, (support a).card ≤ d)
    (hFH : ∀ c, (starSupports support hstars c).Nonempty → F c ⊆ starSupports support hstars c)
    (h : List (Query (Terminal S G I) C)) (c : C) (x : Terminal S G I) :
    ((relevantIncrements π F (starSupports support hstars) D t R h (.ct c x)).card : ℝ) ≤
      if (TwoAnchor.positives (relabel π F) (relabel π (starSupports support hstars))
          (centerHistory h) c).card ≤ 2 ∧ hstars c ≠ none then (d : ℝ) else 0 := by
  classical
  let inc := relevantIncrements π F (starSupports support hstars) D t R h (.ct c x)
  have supportH : Supported (starSupports support hstars) := by
    intro c u hu
    cases he : hstars c with
    | none => simp [starSupports, he] at hu
    | some a => exact hH a u (by simpa only [starSupports, he, Option.elim_some] using hu)
  by_cases he : inc = ∅
  · change (inc.card : ℝ) ≤ _
    rw [he, Finset.card_empty, Nat.cast_zero]
    split_ifs <;> positivity
  · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr he
    obtain ⟨hn, hout, c', x', hq, huH⟩ := relevantIncrements_source _ _ _ _ _ _ _ _ _ hu
    obtain ⟨hc, _⟩ := Query.ct.inj hq
    subst c'
    have hp := low_positive_before_lucky π F (starSupports support hstars) D t R
      hF supportH hcardF hFH h hn c u hout huH
    have hsome : hstars c ≠ none := by
      intro hz
      simp only [starSupports, hz, Option.elim_none, Finset.notMem_empty] at huH
    rw [if_pos ⟨hp, hsome⟩]
    have hsub : inc ⊆ relabel π (starSupports support hstars) c := by
      intro v hv
      obtain ⟨_, _, c', x', hq, hvH⟩ := relevantIncrements_source _ _ _ _ _ _ _ _ _ hv
      obtain ⟨hc, _⟩ := Query.ct.inj hq
      subst c'
      exact (mem_relabel _ _ _ _).mpr hvH
    have hh : (starSupports support hstars c).card ≤ d := by
      cases hz : hstars c with
      | none => simp [starSupports, hz]
      | some a => simpa only [starSupports, hz, Option.elim_some] using hcardH a
    exact_mod_cast (Finset.card_le_card hsub).trans (by simpa only [card_relabel] using hh)

theorem relevantIncrements_expect_prefix
    (μ : Law B) (k : B → C → Law (Option A))
    (F : B → C → Finset (Terminal S G I)) (support : A → Finset (Terminal S G I))
    (hF : ∀ b, Supported (F b)) (hH : ∀ a u, u ∈ support a → specialPosition u)
    (d : ℕ) (hcardF : ∀ b c, (F b c).card ≤ 2) (hcardH : ∀ a, (support a).card ≤ d)
    (hvalid : ∀ ω, 0 <
      (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).mass ω →
        ∀ c, (starSupports support ω.1.2 c).Nonempty → F ω.1.1 c ⊆ starSupports support ω.1.2 c)
    (p : ℝ) (hp : 0 ≤ p) (ha : ∀ b c, 1 / 2 ≤ (k b c).mass none)
    (hmark : ∀ b c, (k b c).prob {a | a ≠ none} ≤ p)
    (D t R : ℕ) (r : Record (Query (Terminal S G I) C) Reply)
    (q : Query (Terminal S G I) C) :
    (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).expect (fun ω =>
      if Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r then
        ((relevantIncrements ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R (questions r) q).card : ℝ)
      else 0) ≤
      (2 * d * p) * (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).prob
        {ω | Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r} := by
  classical
  let ν := shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)
  cases q with
  | tt a b =>
      have he (ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I)) :
          relevantIncrements ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R (questions r) (.tt a b) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        obtain ⟨_, _, c, x, hc, _⟩ := relevantIncrements_source _ _ _ _ _ _ _ _ _ hu
        cases hc
      simp only [he, Finset.card_empty, Nat.cast_zero, ite_self, Law.expect_const]
      exact mul_nonneg (by positivity) (ν.prob_nonneg _)
  | cc c c' =>
      have he (ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I)) :
          relevantIncrements ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R (questions r) (.cc c c') = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        obtain ⟨_, _, c, x, hc, _⟩ := relevantIncrements_source _ _ _ _ _ _ _ _ _ hu
        cases hc
      simp only [he, Finset.card_empty, Nat.cast_zero, ite_self, Law.expect_const]
      exact mul_nonneg (by positivity) (ν.prob_nonneg _)
  | ct c x =>
      let E := {ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I) |
        Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r ∧
          (TwoAnchor.positives (relabel ω.2 (F ω.1.1)) (relabel ω.2 (starSupports support ω.1.2))
            (centerHistory (questions r)) c).card ≤ 2 ∧ ω.1.2 c ≠ none}
      have hcost : ν.expect (fun ω =>
          if Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r then
            ((relevantIncrements ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R
              (questions r) (.ct c x)).card : ℝ) else 0) ≤
          ν.expect (fun ω => if ω ∈ E then (d : ℝ) else 0) := by
        apply ν.expect_mono_support
        intro ω hω
        have hh := relevantIncrements_ct_bound ω.2 (F ω.1.1) support ω.1.2 d D t R
          (hF ω.1.1) hH (hcardF ω.1.1) hcardH (hvalid ω hω) (questions r) c x
        by_cases hr : Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r
        · simpa only [E, Set.mem_ofPred_eq, hr, true_and, ↓reduceIte] using hh
        · simp only [E, Set.mem_ofPred_eq, hr, false_and, ↓reduceIte, le_refl]
      have he : ν.expect (fun ω => if ω ∈ E then (d : ℝ) else 0) = d * ν.prob E := by
        simp only [Law.expect, Law.prob, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        by_cases hω : ω ∈ E <;> simp [hω, mul_comm]
      rw [he] at hcost
      have hb := unseen_center_prefix_bound μ k F support c p hp (fun b => ha b c)
        (fun b => hmark b c) r
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      have hm := mul_le_mul_of_nonneg_left hb hd
      exact hcost.trans (by simpa only [ν, E, mul_assoc, mul_comm, mul_left_comm] using hm)

theorem star_counter_probability_explicit {Z : Type*}
    (μ : Law B) (k : B → C → Law (Option A))
    (F : B → C → Finset (Terminal S G I)) (support : A → Finset (Terminal S G I))
    (hF : ∀ b, Supported (F b)) (hH : ∀ a u, u ∈ support a → specialPosition u)
    (d : ℕ) (hcardF : ∀ b c, (F b c).card ≤ 2) (hcardH : ∀ a, (support a).card ≤ d)
    (hvalid : ∀ ω, 0 <
      (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).mass ω →
        ∀ c, (starSupports support ω.1.2 c).Nonempty → F ω.1.1 c ⊆ starSupports support ω.1.2 c)
    (p : ℝ) (hp : 0 ≤ p) (ha : ∀ b c, 1 / 2 ≤ (k b c).mass none)
    (hmark : ∀ b c, (k b c).prob {a | a ≠ none} ≤ p)
    (D t R q : ℕ) (ht : 0 < t)
    (tree : SteinerLowerBound.DecisionTree (Query (Terminal S G I) C) Reply Z)
    (hquery : DecisionTree.Bounded tree q) :
    (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).prob {ω |
      (analyze ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R
        (questions (DecisionTree.run
          (fun ω => queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) ω [] tree))).stop =
            some .starCounter} ≤ 2 * d * p * q / t := by
  classical
  let ν := shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)
  let answer := fun ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I) =>
    queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)
  let cost := fun (ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I))
      (h : List (Query (Terminal S G I) C)) q =>
    ((relevantIncrements ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R h q).card : ℝ)
  let f := fun ω => historyCharge (cost ω) (questions (DecisionTree.run answer ω [] tree))
  have hcharge := DecisionTree.charging ν answer (fun ω r q => cost ω (questions r) q)
    (fun _ _ => 1) (2 * d * p)
    (by
      intro r q
      simpa only [mul_one, ν, answer, cost] using
        (relevantIncrements_expect_prefix μ k F support hF hH d hcardF hcardH hvalid
          p hp ha hmark D t R r q)) tree []
  simp only [compatible_nil, ↓reduceIte] at hcharge
  have hone : ν.expect (fun ω =>
      DecisionTree.accumulate answer (fun _ _ _ => 1) ω [] tree) ≤ q :=
    (ν.expect_mono (fun ω => DecisionTree.accumulate_one_le answer ω tree q hquery [])).trans_eq
      (ν.expect_const _)
  have hf : ν.expect f ≤ 2 * d * p * q := by
    have he (ω) : f ω =
        DecisionTree.accumulate answer (fun ω r q => cost ω (questions r) q) ω [] tree := by
      simpa only [questions, List.map_nil, historyCharge_nil, zero_add, f] using
        historyCharge_run answer cost ω [] tree
    rw [show f = (fun ω => DecisionTree.accumulate answer
      (fun ω r q => cost ω (questions r) q) ω [] tree) from funext he]
    exact hcharge.trans (mul_le_mul_of_nonneg_left hone (by positivity))
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hmono := ν.prob_mono
    (show {ω | (analyze ω.2 (F ω.1.1) (starSupports support ω.1.2) D t R
        (questions (DecisionTree.run answer ω [] tree))).stop = some .starCounter} ⊆
      {ω | (t : ℝ) ≤ f ω} from by
        intro ω hω
        exact (star_counter_charging ω.2 (F ω.1.1) (starSupports support ω.1.2)
          D t R (questions (DecisionTree.run answer ω [] tree))).2 hω)
  have hm := ν.markov (f := f) (fun ω => historyCharge_nonneg (cost ω)
    (fun _ _ => Nat.cast_nonneg _) _) ht'
  exact hmono.trans (hm.trans (div_le_div_of_nonneg_right hf ht'.le))

end Screening

end SteinerLowerBound
