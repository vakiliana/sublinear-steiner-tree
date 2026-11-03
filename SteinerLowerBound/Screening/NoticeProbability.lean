module

public import SteinerLowerBound.Screening.Notices

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

theorem directUnit_source (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C)
    (u : Terminal S G I) (hu : u ∈ directUnitNotices π F H D t R h q) :
    (analyze π F H D t R h).stop = none ∧ specialPosition (π u) ∧
      u ∉ (analyze π F H D t R h).exposed ∧
        ∃ c, q = .ct c u ∧ π u ∈ F c := by
  classical
  dsimp only [directUnitNotices] at hu
  split_ifs at hu with hg
  · obtain ⟨hc, c, hq, ha⟩ := Finset.mem_filter.mp hu
    have hs := (Finset.mem_filter.mp hc).2
    refine ⟨hg.1, hs.1, hs.2.1, c, hq, ?_⟩
    have hans : TwoAnchor.answer (relabel π F) (relabel π H) (centerHistory h) c u = true := by
      by_cases hb : TwoAnchor.answer (relabel π F) (relabel π H) (centerHistory h) c u = true
      · exact hb
      · simp [hq, queryAnswer, hb] at ha
    have hp : u ∈ relabel π F c ∨
        (TwoAnchor.active (relabel π F) (centerHistory h) c ∧
          Disjoint (relabel π H c) (TwoAnchor.blocked (relabel π F) (centerHistory h) c) ∧
            u ∈ relabel π H c) := by simpa only [TwoAnchor.answer, decide_eq_true_eq] using hans
    rcases hp with hf | hh
    · exact (mem_relabel _ _ _ _).mp hf
    · exact False.elim (hg.2 ⟨c, u, hq, hs.1, hs.2.1, (mem_relabel _ _ _ _).mp hh.2.2⟩)
  · simp at hu

theorem directDegree_source (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C)
    (u : Terminal S G I) (hu : u ∈ directDegreeNotices π F H D t R h q) :
    (analyze π F H D t R h).stop = none ∧ specialPosition (π u) ∧
      u ∉ (analyze π F H D t R h).exposed := by
  classical
  dsimp only [directDegreeNotices] at hu
  split_ifs at hu with hg
  · have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
    exact ⟨hg.1, hs.1, hs.2.1⟩
  · simp at hu

variable {Ξ : Type*} [Fintype Ξ]

theorem directUnit_expect_prefix (μ : Law Ξ)
    (F H : Ξ → C → Finset (Terminal S G I))
    (hF : ∀ ξ, Supported (F ξ)) (hH : ∀ ξ, Supported (H ξ))
    (hcard : ∀ ξ c, (F ξ c).card ≤ 2)
    (D t R : ℕ) (hD : 0 < D) (ht : 0 < t)
    (hsize : 0 ≤ (Fintype.card G * Fintype.card I : ℝ) -
      (3 * t + D * Fintype.card I))
    (r : Record (Query (Terminal S G I) C) Reply) (q : Query (Terminal S G I) C) :
    ((Fintype.card G * Fintype.card I : ℝ) - (3 * t + D * Fintype.card I)) *
      (shuffledLaw (T := Terminal S G I) μ).expect (fun ω =>
        if Compatible (queryAnswer ω.2 (F ω.1) (H ω.1)) r then
          ((directUnitNotices ω.2 (F ω.1) (H ω.1) D t R (questions r) q).card : ℝ) else 0) ≤
      2 * (shuffledLaw (T := Terminal S G I) μ).prob
        {ω | Compatible (queryAnswer ω.2 (F ω.1) (H ω.1)) r} := by
  classical
  let ν := shuffledLaw (T := Terminal S G I) μ
  let P := fun ω : Ξ × Equiv.Perm (Terminal S G I) =>
    Compatible (queryAnswer ω.2 (F ω.1) (H ω.1)) r
  cases q with
  | tt a b =>
      have he (ω : Ξ × Equiv.Perm (Terminal S G I)) :
          directUnitNotices ω.2 (F ω.1) (H ω.1) D t R (questions r) (.tt a b) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        obtain ⟨_, _, _, c, hc, _⟩ := directUnit_source _ _ _ _ _ _ _ _ _ hu
        cases hc
      simp only [he, Finset.card_empty, Nat.cast_zero, ite_self, Law.expect_const, mul_zero]
      exact mul_nonneg (by norm_num) (ν.prob_nonneg _)
  | cc c c' =>
      have he (ω : Ξ × Equiv.Perm (Terminal S G I)) :
          directUnitNotices ω.2 (F ω.1) (H ω.1) D t R (questions r) (.cc c c') = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        obtain ⟨_, _, _, c, hc, _⟩ := directUnit_source _ _ _ _ _ _ _ _ _ hu
        cases hc
      simp only [he, Finset.card_empty, Nat.cast_zero, ite_self, Law.expect_const, mul_zero]
      exact mul_nonneg (by norm_num) (ν.prob_nonneg _)
  | ct c v =>
      have hmask := Law.mask_card_bound ν P
        (fun ω => directUnitNotices ω.2 (F ω.1) (H ω.1) D t R (questions r) (.ct c v))
        {v} ((Fintype.card G * Fintype.card I : ℝ) - (3 * t + D * Fintype.card I)) 2
        (by
          intro ω u hu
          obtain ⟨_, _, _, c', hq, _⟩ := directUnit_source _ _ _ _ _ _ _ _ _ hu
          exact Finset.mem_singleton.mpr (Query.ct.inj hq).2.symm)
        (by
          intro u hu
          have huv : u = v := Finset.mem_singleton.mp hu
          subst u
          have hevent : {ω | P ω ∧ v ∈
              directUnitNotices ω.2 (F ω.1) (H ω.1) D t R (questions r) (.ct c v)} ⊆
            {ω | P ω ∧ Screenable ω.2 (F ω.1) (H ω.1) (questions r) v
                (3 * t + D * Fintype.card I) ∧ ω.2 v ∈ F ω.1 c} := by
            intro ω hω
            obtain ⟨hn, hs, hout, c', hq, hf⟩ := directUnit_source _ _ _ _ _ _ _ _ _ hω.2
            have hec := (Query.ct.inj hq).1
            subst c'
            exact ⟨hω.1, screenable_before_stop _ _ _ D t R hD ht
              (hF ω.1) (hH ω.1) (questions r) hn v hs hout, hf⟩
          have hm := mul_le_mul_of_nonneg_left (ν.prob_mono hevent) hsize
          have hb := anchor_prefix_bound μ F H hF hH hcard (questions r)
            (fun i => (r[i.val]'(by simpa [questions] using i.isLt)).2) v c
            (3 * t + D * Fintype.card I)
          exact hm.trans (by simpa only [← compatible_iff_observations, ν, P] using hb))
      simpa only [Finset.card_singleton, Nat.cast_one, one_mul, ν, P] using hmask

theorem directDegree_expect_prefix (μ : Law Ξ)
    (F H : Ξ → C → Finset (Terminal S G I))
    (hF : ∀ ξ, Supported (F ξ)) (hH : ∀ ξ, Supported (H ξ))
    (D t R : ℕ) (hD : 0 < D) (ht : 0 < t)
    (hsize : 0 ≤ (Fintype.card G * Fintype.card I : ℝ) -
      (3 * t + D * Fintype.card I))
    (r : Record (Query (Terminal S G I) C) Reply) (q : Query (Terminal S G I) C) :
    ((Fintype.card G * Fintype.card I : ℝ) - (3 * t + D * Fintype.card I)) *
      (shuffledLaw (T := Terminal S G I) μ).expect (fun ω =>
        if Compatible (queryAnswer ω.2 (F ω.1) (H ω.1)) r then
          ((directDegreeNotices ω.2 (F ω.1) (H ω.1) D t R (questions r) q).card : ℝ) else 0) ≤
      (degreeCrossings D (questions r) q).card *
        (Fintype.card S * (shuffledLaw (T := Terminal S G I) μ).prob
          {ω | Compatible (queryAnswer ω.2 (F ω.1) (H ω.1)) r}) := by
  classical
  apply Law.mask_card_bound
  · intro ω
    exact directDegree_subset_crossings _ _ _ D t R hD ht (questions r) q
  · intro u _
    have hevent : {ω : Ξ × Equiv.Perm (Terminal S G I) |
        Compatible (queryAnswer ω.2 (F ω.1) (H ω.1)) r ∧
        u ∈ directDegreeNotices ω.2 (F ω.1) (H ω.1) D t R (questions r) q} ⊆
      {ω : Ξ × Equiv.Perm (Terminal S G I) |
        Compatible (queryAnswer ω.2 (F ω.1) (H ω.1)) r ∧
        Screenable ω.2 (F ω.1) (H ω.1) (questions r) u (3 * t + D * Fintype.card I)} := by
      intro ω hω
      obtain ⟨hn, hs, hout⟩ := directDegree_source _ _ _ _ _ _ _ _ _ hω.2
      exact ⟨hω.1, screenable_before_stop _ _ _ D t R hD ht (hF ω.1) (hH ω.1)
        (questions r) hn u hs hout⟩
    have hm := mul_le_mul_of_nonneg_left ((shuffledLaw μ).prob_mono hevent) hsize
    have hb := special_prefix_bound μ F H hF hH (questions r)
      (fun i => (r[i.val]'(by simpa [questions] using i.isLt)).2) u
      (3 * t + D * Fintype.card I)
    exact hm.trans (by simpa only [← compatible_iff_observations] using hb)

theorem noticed_expectation_bound {Z : Type*}
    (μ : Law Ξ) (F H : Ξ → C → Finset (Terminal S G I))
    (hF : ∀ ξ, Supported (F ξ)) (hH : ∀ ξ, Supported (H ξ))
    (hcard : ∀ ξ c, (F ξ c).card ≤ 2)
    (D t R q : ℕ) (hD : 0 < D) (ht : 0 < t)
    (hsize : 0 < (Fintype.card G * Fintype.card I : ℝ) -
      (3 * t + D * Fintype.card I))
    (tree : SteinerLowerBound.DecisionTree (Query (Terminal S G I) C) Reply Z)
    (hquery : DecisionTree.Bounded tree q) :
    (shuffledLaw (T := Terminal S G I) μ).expect (fun ω =>
      ((analyze ω.2 (F ω.1) (H ω.1) D t R (questions (DecisionTree.run
        (fun ω => queryAnswer ω.2 (F ω.1) (H ω.1)) ω [] tree))).noticed.card : ℝ)) ≤
      (2 * q + 2 * Fintype.card S * q / D) /
        ((Fintype.card G * Fintype.card I : ℝ) - (3 * t + D * Fintype.card I)) +
          2 * q / t := by
  classical
  let ν := shuffledLaw (T := Terminal S G I) μ
  let answer := fun ω : Ξ × Equiv.Perm (Terminal S G I) => queryAnswer ω.2 (F ω.1) (H ω.1)
  let cost := fun (ω : Ξ × Equiv.Perm (Terminal S G I))
      (h : List (Query (Terminal S G I) C)) q =>
    ((directUnitNotices ω.2 (F ω.1) (H ω.1) D t R h q).card : ℝ) +
      (directDegreeNotices ω.2 (F ω.1) (H ω.1) D t R h q).card
  let quota := fun (r : Record (Query (Terminal S G I) C) Reply) q =>
    2 + (Fintype.card S : ℝ) * (degreeCrossings D (questions r) q).card
  let V := (Fintype.card G * Fintype.card I : ℝ) - (3 * t + D * Fintype.card I)
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hv : 0 < V := hsize
  have hlocal (r : Record (Query (Terminal S G I) C) Reply)
      (q : Query (Terminal S G I) C) :
      ν.expect (fun ω => if Compatible (answer ω) r then cost ω (questions r) q else 0) ≤
        (1 / V) * quota r q * ν.prob {ω | Compatible (answer ω) r} := by
    have hu := directUnit_expect_prefix μ F H hF hH hcard D t R hD ht hsize.le r q
    have hd := directDegree_expect_prefix μ F H hF hH D t R hD ht hsize.le r q
    have he (ω : Ξ × Equiv.Perm (Terminal S G I)) :
        (if Compatible (answer ω) r then cost ω (questions r) q else 0) =
        (if Compatible (answer ω) r then
          ((directUnitNotices ω.2 (F ω.1) (H ω.1) D t R (questions r) q).card : ℝ) else 0) +
        (if Compatible (answer ω) r then
          ((directDegreeNotices ω.2 (F ω.1) (H ω.1) D t R (questions r) q).card : ℝ) else 0) := by
      by_cases hp : Compatible (answer ω) r <;> simp only [cost, hp, ↓reduceIte, add_zero]
    have hb : V * ν.expect (fun ω =>
        if Compatible (answer ω) r then cost ω (questions r) q else 0) ≤
      quota r q * ν.prob {ω | Compatible (answer ω) r} := by
      simp_rw [he]
      rw [Law.expect_add]
      dsimp only [V, quota, ν, answer] at *
      nlinarith
    have hh : ν.expect (fun ω =>
        if Compatible (answer ω) r then cost ω (questions r) q else 0) ≤
      (quota r q * ν.prob {ω | Compatible (answer ω) r}) / V :=
        (le_div_iff₀ hv).mpr (by nlinarith [hb])
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, one_mul] using hh
  have hcharge := DecisionTree.charging ν answer (fun ω r q => cost ω (questions r) q)
    quota (1 / V) hlocal tree []
  simp only [compatible_nil, ↓reduceIte] at hcharge
  have hquota (ω : Ξ × Equiv.Perm (Terminal S G I)) :
      DecisionTree.accumulate answer (fun _ r q => quota r q) ω [] tree ≤
        2 * q + 2 * Fintype.card S * q / D := by
    let h := questions (DecisionTree.run answer ω [] tree)
    have hlen : h.length ≤ q := by
      simpa only [h, questions, List.length_map, List.length_nil, zero_add] using
        DecisionTree.run_length_le answer ω tree q hquery []
    have hdeg := (highDegree_budget D h).trans (Nat.mul_le_mul_left 2 hlen)
    have hdeg' : ((highDegree D h).card : ℝ) ≤ 2 * q / D := by
      rw [le_div_iff₀ hD']
      exact_mod_cast (by simpa only [Nat.mul_comm] using hdeg)
    have he := historyCharge_run answer
      (fun _ h q => 2 + (Fintype.card S : ℝ) * (degreeCrossings D h q).card) ω [] tree
    simp only [questions, List.map_nil, historyCharge_nil, zero_add] at he
    change historyCharge (fun h q => 2 + (Fintype.card S : ℝ) *
      (degreeCrossings D h q).card) h =
        DecisionTree.accumulate answer (fun _ r q => quota r q) ω [] tree at he
    rw [← he, historyCharge_add, historyCharge_const, historyCharge_const_mul,
      degreeCrossings_charge D hD]
    have hlen' : (h.length : ℝ) ≤ q := by exact_mod_cast hlen
    have hm : (0 : ℝ) ≤ Fintype.card S := Nat.cast_nonneg _
    change (2 : ℝ) * h.length + (Fintype.card S : ℝ) * (highDegree D h).card ≤ _
    calc
      _ ≤ 2 * q + (Fintype.card S : ℝ) * (2 * q / D) :=
        add_le_add (by linarith) (mul_le_mul_of_nonneg_left hdeg' hm)
      _ = _ := by ring
  have hqexpect : ν.expect (fun ω =>
      DecisionTree.accumulate answer (fun _ r q => quota r q) ω [] tree) ≤
        2 * q + 2 * Fintype.card S * q / D :=
    (ν.expect_mono hquota).trans_eq (ν.expect_const _)
  have hpoint (ω : Ξ × Equiv.Perm (Terminal S G I)) :
      ((analyze ω.2 (F ω.1) (H ω.1) D t R
        (questions (DecisionTree.run answer ω [] tree))).noticed.card : ℝ) ≤
      DecisionTree.accumulate answer (fun ω r q => cost ω (questions r) q) ω [] tree + 2 * q / t := by
    let h := questions (DecisionTree.run answer ω [] tree)
    have hlen : h.length ≤ q := by
      simpa only [h, questions, List.length_map, List.length_nil, zero_add] using
        DecisionTree.run_length_le answer ω tree q hquery []
    have hhigh := (fillerHigh_budget ω.2 (F ω.1) (hcard ω.1) t h).trans
      (Nat.mul_le_mul_left 2 hlen)
    have hhigh' : ((fillerHigh ω.2 (F ω.1) t h).card : ℝ) ≤ 2 * q / t := by
      rw [le_div_iff₀ ht']
      exact_mod_cast (by simpa only [Nat.mul_comm] using hhigh)
    have hn := noticed_charging ω.2 (F ω.1) (H ω.1) D t R h
    have hsplit := Finset.card_le_card_sdiff_add_card
      (s := (analyze ω.2 (F ω.1) (H ω.1) D t R h).noticed)
      (t := fillerHigh ω.2 (F ω.1) t h)
    have hsplit' : ((analyze ω.2 (F ω.1) (H ω.1) D t R h).noticed.card : ℝ) ≤
        ((analyze ω.2 (F ω.1) (H ω.1) D t R h).noticed \ fillerHigh ω.2 (F ω.1) t h).card +
          (fillerHigh ω.2 (F ω.1) t h).card := by exact_mod_cast hsplit
    have he := historyCharge_run answer cost ω [] tree
    simp only [questions, List.map_nil, historyCharge_nil, zero_add] at he
    change historyCharge (cost ω) h = _ at he
    change ((analyze ω.2 (F ω.1) (H ω.1) D t R h).noticed.card : ℝ) ≤ _
    change _ ≤ historyCharge (cost ω) h at hn
    rw [he] at hn
    change _ ≤ DecisionTree.accumulate answer (fun ω r q => cost ω (questions r) q) ω [] tree at hn
    linarith
  have hb := ν.expect_mono hpoint
  rw [Law.expect_add, Law.expect_const] at hb
  have hmul := mul_le_mul_of_nonneg_left hqexpect (by positivity : 0 ≤ (1 : ℝ) / V)
  have hacc := hcharge.trans hmul
  have hres : ν.expect (fun ω =>
      ((analyze ω.2 (F ω.1) (H ω.1) D t R (questions (DecisionTree.run answer ω [] tree))).noticed.card : ℝ)) ≤
      (1 / V) * (2 * q + 2 * Fintype.card S * q / D) + 2 * q / t := by
    linarith
  simpa only [ν, answer, V, one_div, mul_comm, div_eq_mul_inv, one_mul] using hres

theorem notice_overflow_probability_explicit {Z : Type*}
    (μ : Law Ξ) (F H : Ξ → C → Finset (Terminal S G I))
    (hF : ∀ ξ, Supported (F ξ)) (hH : ∀ ξ, Supported (H ξ))
    (hcard : ∀ ξ c, (F ξ c).card ≤ 2)
    (D t R q : ℕ) (hD : 0 < D) (ht : 0 < t) (hR : 0 < R)
    (hsize : 0 < (Fintype.card G * Fintype.card I : ℝ) -
      (3 * t + D * Fintype.card I))
    (tree : SteinerLowerBound.DecisionTree (Query (Terminal S G I) C) Reply Z)
    (hquery : DecisionTree.Bounded tree q) :
    (shuffledLaw (T := Terminal S G I) μ).prob {ω |
      R < (analyze ω.2 (F ω.1) (H ω.1) D t R (questions (DecisionTree.run
        (fun ω => queryAnswer ω.2 (F ω.1) (H ω.1)) ω [] tree))).noticed.card} ≤
      ((2 * q + 2 * Fintype.card S * q / D) /
        ((Fintype.card G * Fintype.card I : ℝ) - (3 * t + D * Fintype.card I)) +
          2 * q / t) / R := by
  classical
  let ν := shuffledLaw (T := Terminal S G I) μ
  let f := fun ω : Ξ × Equiv.Perm (Terminal S G I) =>
    ((analyze ω.2 (F ω.1) (H ω.1) D t R (questions (DecisionTree.run
      (fun ω => queryAnswer ω.2 (F ω.1) (H ω.1)) ω [] tree))).noticed.card : ℝ)
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have he := noticed_expectation_bound μ F H hF hH hcard D t R q hD ht hsize tree hquery
  have hm := ν.markov_gt (f := f) (fun ω => Nat.cast_nonneg _) hR'
  have hevent : {ω : Ξ × Equiv.Perm (Terminal S G I) |
      R < (analyze ω.2 (F ω.1) (H ω.1) D t R (questions (DecisionTree.run
        (fun ω => queryAnswer ω.2 (F ω.1) (H ω.1)) ω [] tree))).noticed.card} =
      {ω | (R : ℝ) < ((analyze ω.2 (F ω.1) (H ω.1) D t R (questions (DecisionTree.run
        (fun ω => queryAnswer ω.2 (F ω.1) (H ω.1)) ω [] tree))).noticed.card : ℝ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Nat.cast_lt]
  rw [hevent]
  exact hm.trans (div_le_div_of_nonneg_right he hR'.le)

end Screening

end SteinerLowerBound
