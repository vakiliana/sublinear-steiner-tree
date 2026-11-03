module

public import SteinerLowerBound.Screening.ClusterCharging

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Law

theorem expect_mask_card {Ω T : Type*} [Fintype Ω] [Fintype T]
    (μ : Law Ω) (P : Ω → Prop) (F : Ω → Finset T) :
    μ.expect (fun ω => if P ω then ((F ω).card : ℝ) else 0) =
      ∑ u, μ.prob {ω | P ω ∧ u ∈ F ω} := by
  classical
  calc
    _ = μ.expect (fun ω => ((if P ω then F ω else ∅).card : ℝ)) := by
      apply congrArg (Law.expect μ)
      funext ω
      by_cases hp : P ω <;> simp [hp]
    _ = _ := μ.expect_card_finset _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      apply congrArg (Law.prob μ)
      ext ω
      by_cases hp : P ω <;> simp [hp]

end Law

namespace Screening

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

theorem lowMarkSet_subset_endpoints (π : Equiv.Perm (Terminal S G I)) (D t : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    lowMarkSet π D t h q ⊆ (queryEndpoints q).toFinset := by
  intro u hu
  have hu' := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu).1).1
  cases q with
  | tt a b =>
      change u ∈ (if a ≠ b ∧ SameCluster π a b then {a, b} else ∅) at hu'
      split_ifs at hu' with hp
      · simpa [queryEndpoints, hp.1] using hu'
      · simp at hu'
  | ct => simp [queryMarks] at hu'
  | cc => simp [queryMarks] at hu'

theorem lowMarkSet_source (π : Equiv.Perm (Terminal S G I)) (D t : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C)
    (u : Terminal S G I) (hu : u ∈ lowMarkSet π D t h q) :
    u ∉ marked π h ∧ ∃ v, u ≠ v ∧
      ∃ g, u ∈ clusterLabels π g ∧ v ∈ clusterLabels π g ∧
        (Fintype.card I : ℝ) + (marked π h).card + (externalLabels π h g).card +
          degree h u * Fintype.card I ≤ Fintype.card I + 2 * t + D * Fintype.card I := by
  classical
  obtain ⟨hu', hd, he, hm⟩ := Finset.mem_filter.mp hu
  obtain ⟨hmark, hnew⟩ := Finset.mem_sdiff.mp hu'
  obtain ⟨g, hg⟩ := queryMarks_cluster π q u hmark
  have hb : (externalLabels π h g).card < t := by
    simpa only [clusterExposure, (mem_clusterLabels _ _ _).mp hg] using he
  have hbudget : (Fintype.card I : ℝ) + (marked π h).card +
      (externalLabels π h g).card + degree h u * Fintype.card I ≤
        Fintype.card I + 2 * t + D * Fintype.card I := by
    have h1 : ((marked π h).card : ℝ) ≤ t := by exact_mod_cast hm.le
    have h2 : ((externalLabels π h g).card : ℝ) ≤ t := by exact_mod_cast hb.le
    have h3 : (degree h u : ℝ) ≤ D := by exact_mod_cast hd.le
    have hR : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
    nlinarith
  refine ⟨hnew, ?_⟩
  cases q with
  | ct => simp [queryMarks] at hmark
  | cc => simp [queryMarks] at hmark
  | tt a b =>
      change u ∈ (if a ≠ b ∧ SameCluster π a b then {a, b} else ∅) at hmark
      split_ifs at hmark with hp
      · rcases Finset.mem_insert.mp hmark with hua | hub
        · subst u
          obtain ⟨g', hga, hgb⟩ := hp.2
          have hgg : g' = g := by
            have hh := (mem_clusterLabels _ _ _).mp hg
            rw [hga] at hh
            exact Option.some.inj hh
          subst g'
          exact ⟨b, hp.1, g, hg, (mem_clusterLabels _ _ _).mpr hgb, hbudget⟩
        · have hub' := Finset.mem_singleton.mp hub
          subst u
          obtain ⟨g', hga, hgb⟩ := hp.2
          have hgg : g' = g := by
            have hh := (mem_clusterLabels _ _ _).mp hg
            rw [hgb] at hh
            exact Option.some.inj hh
          subst g'
          exact ⟨a, hp.1.symm, g, hg, (mem_clusterLabels _ _ _).mpr hga, hbudget⟩
      · simp at hmark

variable {Ξ : Type*} [Fintype Ξ]

theorem low_mark_prefix_bound (μ : Law Ξ)
    (F H : Ξ → C → Finset (Terminal S G I))
    (hF : ∀ ξ, Supported (F ξ)) (hH : ∀ ξ, Supported (H ξ))
    (D t : ℕ) (r : Record (Query (Terminal S G I) C) Reply)
    (q : Query (Terminal S G I) C) (u : Terminal S G I) :
    ((Fintype.card G * Fintype.card I : ℝ) -
        (Fintype.card I + 2 * t + D * Fintype.card I)) *
      (shuffledLaw (T := Terminal S G I) μ).prob
        {ω | Compatible (queryAnswer ω.2 (F ω.1) (H ω.1)) r ∧
          u ∈ lowMarkSet ω.2 D t (questions r) q} ≤
      Fintype.card I * (shuffledLaw (T := Terminal S G I) μ).prob
        {ω | Compatible (queryAnswer ω.2 (F ω.1) (H ω.1)) r} := by
  classical
  let E := {ω : Ξ × Equiv.Perm (Terminal S G I) |
    Compatible (queryAnswer ω.2 (F ω.1) (H ω.1)) r ∧
      u ∈ lowMarkSet ω.2 D t (questions r) q}
  -- The second endpoint may depend on the configuration.  There are only the
  -- two fixed endpoints of the next terminal--terminal query.
  cases q with
  | ct c v =>
      have he : E = ∅ := by
        ext ω
        simp only [E, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _
        simp [lowMarkSet, queryMarks]
      change _ * (shuffledLaw (T := Terminal S G I) μ).prob E ≤ _
      rw [he, Law.prob_empty, mul_zero]
      exact mul_nonneg (Nat.cast_nonneg _) ((shuffledLaw μ).prob_nonneg _)
  | cc c c' =>
      have he : E = ∅ := by
        ext ω
        simp only [E, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _
        simp [lowMarkSet, queryMarks]
      change _ * (shuffledLaw (T := Terminal S G I) μ).prob E ≤ _
      rw [he, Law.prob_empty, mul_zero]
      exact mul_nonneg (Nat.cast_nonneg _) ((shuffledLaw μ).prob_nonneg _)
  | tt a b =>
      by_cases hua : u = a
      · subst u
        have hb := cluster_prefix_bound μ F H hF hH (questions r)
          (fun i => (r[i.val]'(by simpa [questions] using i.isLt)).2) a b
          (Fintype.card I + 2 * t + D * Fintype.card I) E (by
            intro ω hω
            have hs := lowMarkSet_source ω.2 D t (questions r) (.tt a b) a hω.2
            have hqm := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hω.2).1).1
            have hpair : a ≠ b ∧ SameCluster ω.2 a b := by
              by_contra hn
              simp [queryMarks, hn] at hqm
            obtain ⟨g, hga, hgb⟩ := hpair.2
            have hext := (Finset.mem_filter.mp hω.2).2.2.1
            have hdeg := (Finset.mem_filter.mp hω.2).2.1
            have hmarked := (Finset.mem_filter.mp hω.2).2.2.2
            refine ⟨(compatible_iff_observations _ _ _ r).mp hω.1, hs.1,
              hpair.1, g, (mem_clusterLabels _ _ _).mpr hga,
                (mem_clusterLabels _ _ _).mpr hgb, ?_⟩
            have hb : ((externalLabels ω.2 (questions r) g).card : ℝ) ≤ t := by
              have hh : (externalLabels ω.2 (questions r) g).card < t := by
                simpa only [clusterExposure, hga] using hext
              exact_mod_cast hh.le
            have hd : (degree (questions r) a : ℝ) ≤ D := by exact_mod_cast hdeg.le
            have hm : ((marked ω.2 (questions r)).card : ℝ) ≤ t := by exact_mod_cast hmarked.le
            have hR : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
            nlinarith)
        simpa only [E, ← compatible_iff_observations] using hb
      · by_cases hub : u = b
        · subst u
          -- Use the symmetric query orientation, not a relabeling of queries.
          have hb := cluster_prefix_bound μ F H hF hH (questions r)
            (fun i => (r[i.val]'(by simpa [questions] using i.isLt)).2) b a
            (Fintype.card I + 2 * t + D * Fintype.card I) E (by
              intro ω hω
              have hqm := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hω.2).1).1
              have hpair : a ≠ b ∧ SameCluster ω.2 a b := by
                by_contra hn
                simp [queryMarks, hn] at hqm
              obtain ⟨g, hga, hgb⟩ := hpair.2
              have hext := (Finset.mem_filter.mp hω.2).2.2.1
              have hdeg := (Finset.mem_filter.mp hω.2).2.1
              have hmarked := (Finset.mem_filter.mp hω.2).2.2.2
              refine ⟨(compatible_iff_observations _ _ _ r).mp hω.1,
                (lowMarkSet_source _ _ _ _ _ _ hω.2).1, hpair.1.symm,
                  g, (mem_clusterLabels _ _ _).mpr hgb,
                    (mem_clusterLabels _ _ _).mpr hga, ?_⟩
              have hb : ((externalLabels ω.2 (questions r) g).card : ℝ) ≤ t := by
                have hh : (externalLabels ω.2 (questions r) g).card < t := by
                  simpa only [clusterExposure, hgb] using hext
                exact_mod_cast hh.le
              have hd : (degree (questions r) b : ℝ) ≤ D := by exact_mod_cast hdeg.le
              have hm : ((marked ω.2 (questions r)).card : ℝ) ≤ t := by exact_mod_cast hmarked.le
              have hR : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
              nlinarith)
          simpa only [E, ← compatible_iff_observations] using hb
        · have hzero : (shuffledLaw (T := Terminal S G I) μ).prob E = 0 := by
            have he : E = ∅ := by
              ext ω
              simp only [E, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
              intro hc hu
              have hh := lowMarkSet_subset_endpoints ω.2 D t (questions r) (.tt a b) hu
              by_cases hab : a = b <;> simpa [queryEndpoints, hab, hua, hub] using hh
            rw [he, Law.prob_empty]
          change _ * (shuffledLaw (T := Terminal S G I) μ).prob E ≤ _
          rw [hzero, mul_zero]
          exact mul_nonneg (Nat.cast_nonneg _) ((shuffledLaw μ).prob_nonneg _)

theorem low_mark_expect_prefix (μ : Law Ξ)
    (F H : Ξ → C → Finset (Terminal S G I))
    (hF : ∀ ξ, Supported (F ξ)) (hH : ∀ ξ, Supported (H ξ))
    (D t : ℕ) (r : Record (Query (Terminal S G I) C) Reply)
    (q : Query (Terminal S G I) C) :
    ((Fintype.card G * Fintype.card I : ℝ) -
        (Fintype.card I + 2 * t + D * Fintype.card I)) *
      (shuffledLaw (T := Terminal S G I) μ).expect
        (fun ω => if Compatible (queryAnswer ω.2 (F ω.1) (H ω.1)) r then
          ((lowMarkSet ω.2 D t (questions r) q).card : ℝ) else 0) ≤
      2 * Fintype.card I * (shuffledLaw (T := Terminal S G I) μ).prob
        {ω | Compatible (queryAnswer ω.2 (F ω.1) (H ω.1)) r} := by
  classical
  let ν := shuffledLaw (T := Terminal S G I) μ
  let P := fun ω : Ξ × Equiv.Perm (Terminal S G I) =>
    Compatible (queryAnswer ω.2 (F ω.1) (H ω.1)) r
  let e := (queryEndpoints q).toFinset
  have he : (e.card : ℝ) ≤ 2 := by
    have hc := List.toFinset_card_le (l := queryEndpoints q)
    have hl : (queryEndpoints q).length ≤ 2 := by
      cases q with
      | tt a b => dsimp only [queryEndpoints]; split_ifs <;> simp
      | ct c u => simp [queryEndpoints]
      | cc c c' => simp [queryEndpoints]
    exact_mod_cast hc.trans hl
  have hp := ν.prob_nonneg {ω | P ω}
  have hR : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  calc
    _ = ∑ u, (((Fintype.card G * Fintype.card I : ℝ) -
          (Fintype.card I + 2 * t + D * Fintype.card I)) *
        ν.prob {ω | P ω ∧ u ∈ lowMarkSet ω.2 D t (questions r) q}) := by
      rw [Law.expect_mask_card, Finset.mul_sum]
    _ ≤ ∑ u, if u ∈ e then Fintype.card I * ν.prob {ω | P ω} else 0 := by
      apply Finset.sum_le_sum
      intro u _
      by_cases hu : u ∈ e
      · simpa only [hu, ↓reduceIte, ν, P] using
          low_mark_prefix_bound μ F H hF hH D t r q u
      · have hz : {ω | P ω ∧ u ∈ lowMarkSet ω.2 D t (questions r) q} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro ω hω
          exact hu (lowMarkSet_subset_endpoints ω.2 D t (questions r) q hω.2)
        simp only [hz, Law.prob_empty, mul_zero, hu, ↓reduceIte, le_refl]
    _ = e.card * (Fintype.card I * ν.prob {ω | P ω}) := by
      rw [← Finset.sum_filter]
      have heq : Finset.univ.filter (fun u => u ∈ e) = e := by ext u; simp
      rw [heq, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right he (mul_nonneg hR hp)
      simpa only [ν, P, mul_assoc] using hh

theorem lowMarks_run_le {Z : Type*}
    (F H : Ξ → C → Finset (Terminal S G I)) (D t : ℕ)
    (ω : Ξ × Equiv.Perm (Terminal S G I))
    (tree : SteinerLowerBound.DecisionTree (Query (Terminal S G I) C) Reply Z)
    (r : Record (Query (Terminal S G I) C) Reply) :
    ((lowMarks ω.2 D t (questions (DecisionTree.run
      (fun ω => queryAnswer ω.2 (F ω.1) (H ω.1)) ω r tree))).card : ℝ) ≤
      (lowMarks ω.2 D t (questions r)).card +
        DecisionTree.accumulate (fun ω => queryAnswer ω.2 (F ω.1) (H ω.1))
          (fun ω r q => ((lowMarkSet ω.2 D t (questions r) q).card : ℝ)) ω r tree := by
  induction tree generalizing r with
  | leaf => simp [DecisionTree.run, DecisionTree.accumulate]
  | query q next ih =>
      let b := queryAnswer ω.2 (F ω.1) (H ω.1) (questions r) q
      have hh := ih b (r ++ [(q, b)])
      have hc := Finset.card_union_le
        (lowMarks ω.2 D t (questions r)) (lowMarkSet ω.2 D t (questions r) q)
      have hc' : ((lowMarks ω.2 D t (questions r) ∪
          lowMarkSet ω.2 D t (questions r) q).card : ℝ) ≤
        (lowMarks ω.2 D t (questions r)).card + (lowMarkSet ω.2 D t (questions r) q).card :=
        by exact_mod_cast hc
      simp only [questions, List.map_append, List.map_singleton] at hh
      rw [lowMarks_append] at hh
      simp only [DecisionTree.run, DecisionTree.accumulate]
      dsimp only [b] at *
      simp only [questions] at *
      linarith

theorem expected_lowMarks_le {Z : Type*}
    (μ : Law Ξ) (F H : Ξ → C → Finset (Terminal S G I))
    (hF : ∀ ξ, Supported (F ξ)) (hH : ∀ ξ, Supported (H ξ))
    (D t q : ℕ)
    (hsize : 0 < (Fintype.card G * Fintype.card I : ℝ) -
      (Fintype.card I + 2 * t + D * Fintype.card I))
    (tree : SteinerLowerBound.DecisionTree (Query (Terminal S G I) C) Reply Z)
    (hquery : DecisionTree.Bounded tree q) :
    (shuffledLaw (T := Terminal S G I) μ).expect (fun ω =>
      ((lowMarks ω.2 D t (questions (DecisionTree.run
        (fun ω => queryAnswer ω.2 (F ω.1) (H ω.1)) ω [] tree))).card : ℝ)) ≤
      (2 * Fintype.card I /
        ((Fintype.card G * Fintype.card I : ℝ) -
          (Fintype.card I + 2 * t + D * Fintype.card I))) * q := by
  classical
  let ν := shuffledLaw (T := Terminal S G I) μ
  let answer := fun ω : Ξ × Equiv.Perm (Terminal S G I) =>
    queryAnswer ω.2 (F ω.1) (H ω.1)
  let cost := fun (ω : Ξ × Equiv.Perm (Terminal S G I))
      (r : Record (Query (Terminal S G I) C) Reply) q =>
    ((lowMarkSet ω.2 D t (questions r) q).card : ℝ)
  let B := 2 * Fintype.card I /
    ((Fintype.card G * Fintype.card I : ℝ) -
      (Fintype.card I + 2 * t + D * Fintype.card I))
  have hB : 0 ≤ B := div_nonneg (by positivity) hsize.le
  have hlocal (r : Record (Query (Terminal S G I) C) Reply)
      (q : Query (Terminal S G I) C) :
      ν.expect (fun ω => if Compatible (answer ω) r then cost ω r q else 0) ≤
        B * 1 * ν.prob {ω | Compatible (answer ω) r} := by
    have hh := low_mark_expect_prefix μ F H hF hH D t r q
    have hd : ν.expect (fun ω => if Compatible (answer ω) r then cost ω r q else 0) ≤
        (2 * Fintype.card I * ν.prob {ω | Compatible (answer ω) r}) /
          ((Fintype.card G * Fintype.card I : ℝ) -
            (Fintype.card I + 2 * t + D * Fintype.card I)) := by
      apply (le_div_iff₀ hsize).mpr
      dsimp only [ν, answer, cost]
      nlinarith [hh]
    simpa only [B, div_mul_eq_mul_div, mul_one, ν, answer, cost] using hd
  have hcharge := DecisionTree.charging ν answer cost (fun _ _ => 1) B hlocal tree []
  simp only [compatible_nil, ↓reduceIte] at hcharge
  have hrun : ν.expect (fun ω =>
      DecisionTree.accumulate answer (fun _ _ _ => 1) ω [] tree) ≤ q := by
    exact (ν.expect_mono (fun ω => DecisionTree.accumulate_one_le answer ω tree q hquery [])).trans_eq
      (ν.expect_const _)
  have hlow : ν.expect (fun ω =>
      ((lowMarks ω.2 D t (questions (DecisionTree.run answer ω [] tree))).card : ℝ)) ≤
        ν.expect (fun ω => DecisionTree.accumulate answer cost ω [] tree) := by
    apply ν.expect_mono
    intro ω
    simpa only [questions, List.map_nil, lowMarks_nil, Finset.card_empty, Nat.cast_zero,
      zero_add, answer, cost] using lowMarks_run_le F H D t ω tree []
  exact hlow.trans (hcharge.trans (mul_le_mul_of_nonneg_left hrun hB))

theorem cluster_stop_probability_explicit {Z : Type*}
    (μ : Law Ξ) (F H : Ξ → C → Finset (Terminal S G I))
    (hF : ∀ ξ, Supported (F ξ)) (hH : ∀ ξ, Supported (H ξ))
    (D t q : ℕ) (hD : 0 < D) (ht : 0 < t)
    (hsize : 0 < (Fintype.card G * Fintype.card I : ℝ) -
      (Fintype.card I + 2 * t + D * Fintype.card I))
    (tree : SteinerLowerBound.DecisionTree (Query (Terminal S G I) C) Reply Z)
    (hquery : DecisionTree.Bounded tree q) :
    (shuffledLaw (T := Terminal S G I) μ).prob {ω |
      t ≤ (marked ω.2 (questions (DecisionTree.run
        (fun ω => queryAnswer ω.2 (F ω.1) (H ω.1)) ω [] tree))).card} ≤
      (2 * q / D + 2 * q * Fintype.card I / t +
        (2 * Fintype.card I /
          ((Fintype.card G * Fintype.card I : ℝ) -
            (Fintype.card I + 2 * t + D * Fintype.card I))) * q) / t := by
  classical
  let ν := shuffledLaw (T := Terminal S G I) μ
  let final := fun ω : Ξ × Equiv.Perm (Terminal S G I) =>
    questions (DecisionTree.run (fun ω => queryAnswer ω.2 (F ω.1) (H ω.1)) ω [] tree)
  let E := {ω : Ξ × Equiv.Perm (Terminal S G I) | t ≤ (marked ω.2 (final ω)).card}
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hpoint (ω : Ξ × Equiv.Perm (Terminal S G I)) :
      (t : ℝ) * (if ω ∈ E then 1 else 0) ≤
        2 * q / D + 2 * q * Fintype.card I / t +
          ((lowMarks ω.2 D t (final ω)).card : ℝ) := by
    have hlen : (final ω).length ≤ q := by
      simpa only [final, questions, List.length_map, List.length_nil, zero_add] using
        DecisionTree.run_length_le
          (fun ω => queryAnswer ω.2 (F ω.1) (H ω.1)) ω tree q hquery []
    have hd := (highDegree_budget D (final ω)).trans (Nat.mul_le_mul_left 2 hlen)
    have hg := (highClusters_budget ω.2 t (final ω)).trans (Nat.mul_le_mul_left 2 hlen)
    have hd' : ((highDegree D (final ω)).card : ℝ) ≤ 2 * q / D := by
      rw [le_div_iff₀ hD']
      exact_mod_cast (by simpa [Nat.mul_comm] using hd)
    have hg' : ((highClusters ω.2 t (final ω)).card : ℝ) ≤ 2 * q / t := by
      rw [le_div_iff₀ ht']
      exact_mod_cast (by simpa [Nat.mul_comm] using hg)
    have hc : ((highClusterLabels ω.2 t (final ω)).card : ℝ) ≤
        2 * q * Fintype.card I / t := by
      have hh : ((highClusterLabels ω.2 t (final ω)).card : ℝ) ≤
          (highClusters ω.2 t (final ω)).card * Fintype.card I :=
        by exact_mod_cast highClusterLabels_card ω.2 t (final ω)
      exact hh.trans (by
        have hI : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
        have := mul_le_mul_of_nonneg_right hg' hI
        simpa [div_mul_eq_mul_div] using this)
    by_cases he : ω ∈ E
    · have hcharge := (mark_threshold_charged ω.2 D t (final ω)).2 he
      have hcu := Finset.card_union_le
        (highDegree D (final ω) ∪ highClusterLabels ω.2 t (final ω))
        (lowMarks ω.2 D t (final ω))
      have hcu' := Finset.card_union_le (highDegree D (final ω))
        (highClusterLabels ω.2 t (final ω))
      have htotal : (t : ℝ) ≤
          (highDegree D (final ω)).card + (highClusterLabels ω.2 t (final ω)).card +
            (lowMarks ω.2 D t (final ω)).card := by
        exact_mod_cast (show t ≤
          (highDegree D (final ω)).card + (highClusterLabels ω.2 t (final ω)).card +
            (lowMarks ω.2 D t (final ω)).card by
          dsimp only [markCharges] at hcharge
          omega)
      simp only [he, ↓reduceIte, mul_one]
      linarith
    · simp only [he, ↓reduceIte, mul_zero]
      positivity
  have hexpect := ν.expect_mono hpoint
  have heL : ν.expect (fun ω => (t : ℝ) * (if ω ∈ E then 1 else 0)) = t * ν.prob E := by
    simp only [Law.expect, Law.prob, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases he : ω ∈ E <;> simp [he, mul_comm, mul_assoc]
  rw [heL, Law.expect_add, Law.expect_const] at hexpect
  have hlow := expected_lowMarks_le μ F H hF hH D t q hsize tree hquery
  apply (le_div_iff₀ ht').mpr
  change ν.prob E * t ≤ _
  dsimp only [ν, final] at *
  linarith

end Screening

end SteinerLowerBound
