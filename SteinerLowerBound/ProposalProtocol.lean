module

public import SteinerLowerBound.CategoricalCoupling
public import SteinerLowerBound.DeferredSampling
public import SteinerLowerBound.StoppingCoupling

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Protocol

variable {X S A R : Type*} [Fintype A]

def Valid (D : Finset S → Finset X) (cap : Finset S → Prop) (I : Finset X) :
    DecisionTree X A R → Prop
  | .leaf _ => ∃ Q, cap Q ∧ I ⊆ D Q
  | .query x next => x ∉ I ∧ ∀ a, Valid D cap (insert x I) (next a)

theorem valid_used_disjoint (D : Finset S → Finset X) (cap : Finset S → Prop)
    (t : DecisionTree X A R) (I : Finset X) (ht : Valid D cap I t) :
    ∀ x ∈ I, x ∉ t.used := by
  induction t generalizing I with
  | leaf => simp [DecisionTree.used]
  | query q next ih =>
      intro x hx hu
      rcases Finset.mem_insert.mp hu with h | h
      · subst x
        exact ht.1 hx
      · obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp h
        exact ih a (insert q I) (ht.2 a) x (Finset.mem_insert_of_mem hx) ha

theorem valid_no_repeats (D : Finset S → Finset X) (cap : Finset S → Prop)
    (t : DecisionTree X A R) (I : Finset X) (ht : Valid D cap I t) : t.NoRepeats := by
  induction t generalizing I with
  | leaf => trivial
  | query q next ih =>
      exact ⟨fun a => ih a _ (ht.2 a),
        fun a => valid_used_disjoint D cap (next a) _ (ht.2 a) q (Finset.mem_insert_self _ _)⟩

noncomputable def height : DecisionTree X A R → ℕ
  | .leaf _ => 0
  | .query _ next => 1 + Finset.univ.sup (fun a => height (next a))

theorem valid_height [Nonempty A] (D : Finset S → Finset X) (cap : Finset S → Prop)
    (N : ℕ) (hD : ∀ Q, cap Q → (D Q).card ≤ N)
    (t : DecisionTree X A R) (I : Finset X) (ht : Valid D cap I t) :
    height t + I.card ≤ N := by
  classical
  induction t generalizing I with
  | leaf =>
      obtain ⟨Q, hQ, hIQ⟩ := ht
      simpa only [height, zero_add] using (Finset.card_le_card hIQ).trans (hD Q hQ)
  | query q next ih =>
      have hchild (a : A) : height (next a) + I.card + 1 ≤ N := by
        have h := ih a (insert q I) (ht.2 a)
        rw [Finset.card_insert_of_notMem ht.1] at h
        omega
      have hs : Finset.univ.sup (fun a => height (next a)) ≤ N - (I.card + 1) := by
        apply Finset.sup_le
        intro a _
        have := hchild a
        omega
      have := hchild (Classical.arbitrary A)
      simp only [height]
      omega

theorem lazy_close [Fintype R] (μ ν : X → Law A) (δ : ℝ) (hδ : 0 ≤ δ)
    (hμν : ∀ x, Law.Close (μ x) (ν x) δ) (t : DecisionTree X A R) (N : ℕ)
    (hN : height t ≤ N) : Law.Close (t.runLaw μ) (t.runLaw ν) ((N : ℝ) * δ) := by
  classical
  induction N generalizing t with
  | zero =>
      cases t with
      | leaf r => simpa [DecisionTree.runLaw] using (Law.close_refl (Law.pure r))
      | query x next => simp [height] at hN
  | succ N ih =>
      cases t with
      | leaf r =>
          exact (Law.close_refl _).mono (by positivity)
      | query x next =>
          have hchild (a : A) : height (next a) ≤ N := by
            have hsup := Finset.le_sup (f := fun a => height (next a)) (Finset.mem_univ a)
            simp only [height] at hN
            omega
          have h := (hμν x).bind (fun a => (next a).runLaw μ) (fun a => (next a).runLaw ν)
            (fun a => ih (next a) (hchild a))
          have heq : δ + (N : ℝ) * δ = ((N + 1 : ℕ) : ℝ) * δ := by push_cast; ring
          rw [heq] at h
          exact h

end Protocol

namespace ProposalProtocol

variable {X S R : Type*} [Fintype X] [Fintype S] [Fintype R]

noncomputable def trialLaw (rate keep : Rate) : Law (Option Bool) where
  mass
    | none => 1 - (rate : ℝ)
    | some false => (rate : ℝ) * (1 - (keep : ℝ))
    | some true => (rate : ℝ) * (keep : ℝ)
  nonneg a := by
    cases a with
    | none => exact sub_nonneg.mpr rate.property.2
    | some b =>
        cases b
        · exact mul_nonneg rate.property.1 (sub_nonneg.mpr keep.property.2)
        · exact mul_nonneg rate.property.1 keep.property.1
  total := by simp [Fintype.sum_option]; ring

@[simp]
theorem trial_mass_none (rate keep : Rate) : (trialLaw rate keep).mass none = 1 - (rate : ℝ) := rfl

@[simp]
theorem trial_mass_false (rate keep : Rate) :
    (trialLaw rate keep).mass (some false) = (rate : ℝ) * (1 - (keep : ℝ)) := rfl

@[simp]
theorem trial_mass_true (rate keep : Rate) :
    (trialLaw rate keep).mass (some true) = (rate : ℝ) * (keep : ℝ) := rfl

noncomputable def compile (H : X → Finset S) (rate : X → Rate) :
    DecisionTree X (Option Bool) R → ProposalTree S R
  | .leaf r => .leaf r
  | .query x next =>
      .inspect (H x) (rate x) (compile H rate (next none))
        (compile H rate (next (some false))) (compile H rate (next (some true)))

omit [Fintype X] [Fintype S] in
theorem compile_prob (H : X → Finset S) (rate : X → Rate)
    (w : S → Rate) (t : DecisionTree X (Option Bool) R) (E : Set R) :
    (t.runLaw (fun x => trialLaw (rate x) (ProposalTree.retention (H x) w))).prob E =
      ((compile H rate t).run w).prob E := by
  induction t with
  | leaf r => rfl
  | query x next ih =>
      simp only [DecisionTree.runLaw, Law.prob_bind, Law.expect,
        Fintype.sum_option, Fintype.sum_bool, trial_mass_none, trial_mass_false, trial_mass_true,
        compile, ProposalTree.run, Law.prob_mix, ih]
      ring

noncomputable def pathBudget (cost : X → ℝ) : DecisionTree X (Option Bool) R → ℝ
  | .leaf _ => 0
  | .query x next => cost x +
      max (pathBudget cost (next none))
        (max (pathBudget cost (next (some false))) (pathBudget cost (next (some true))))

omit [Fintype X] [Fintype S] [Fintype R] in
theorem budget_valid (cost : X → ℝ) (hcost : ∀ x, 0 ≤ cost x)
    (D : Finset S → Finset X) (cap : Finset S → Prop) (B : ℝ)
    (hD : ∀ Q, cap Q → ∑ x ∈ D Q, cost x ≤ B)
    (t : DecisionTree X (Option Bool) R) (I : Finset X) (ht : Protocol.Valid D cap I t) :
    pathBudget cost t + ∑ x ∈ I, cost x ≤ B := by
  classical
  induction t generalizing I with
  | leaf r =>
      obtain ⟨Q, hQ, hs⟩ := ht
      simpa [pathBudget] using (Finset.sum_le_sum_of_subset_of_nonneg hs
        (fun x _ _ => hcost x)).trans (hD Q hQ)
  | query x next ih =>
      have hnone := ih none (insert x I) (ht.2 none)
      have hfalse := ih (some false) (insert x I) (ht.2 (some false))
      have htrue := ih (some true) (insert x I) (ht.2 (some true))
      rw [Finset.sum_insert ht.1] at hnone hfalse htrue
      have hmax :
          max (pathBudget cost (next none))
            (max (pathBudget cost (next (some false))) (pathBudget cost (next (some true)))) ≤
              B - cost x - ∑ y ∈ I, cost y := by
        apply max_le
        · linarith
        · apply max_le <;> linarith
      simp only [pathBudget]
      linarith

omit [Fintype X] [Fintype S] [Fintype R] in
theorem compiled_budget (H : X → Finset S) (rate : X → Rate)
    (t : DecisionTree X (Option Bool) R) (u : S) :
    (compile H rate t).budget u =
      pathBudget (fun x => if u ∈ H x then (rate x : ℝ) else 0) t := by
  induction t with
  | leaf => rfl
  | query x next ih => simp [compile, ProposalTree.budget, pathBudget, ih]

noncomputable def model {Ω : Type*} [Fintype Ω] (H : X → Finset S) (rate : X → Rate)
    (t : DecisionTree X (Option Bool) R) (μ : Law Ω) (w : Ω → Rate) : Law R :=
  (μ.iid S).bind (fun a =>
    (Law.pi (fun x => trialLaw (rate x) (ProposalTree.retention (H x) (fun u => w (a u))))).map
      (fun o => t.output o))

theorem model_compile_close {Ω : Type*} [Fintype Ω] (H : X → Finset S) (rate : X → Rate)
    (t : DecisionTree X (Option Bool) R) (ht : t.NoRepeats)
    (μ : Law Ω) (w : Ω → Rate) :
    Law.Close (model H rate t μ w) ((compile H rate t).marginal μ w) 0 := by
  have h := Law.Close.bind_same (μ.iid S)
    (fun a => (Law.pi (fun x =>
      trialLaw (rate x) (ProposalTree.retention (H x) (fun u => w (a u))))).map (fun o => t.output o))
    (fun a => (compile H rate t).run (fun u => w (a u))) (fun _ => 0) (fun a => by
    intro E
    rw [Law.prob_map]
    have he := (DecisionTree.deferred_sampling
      (fun x => trialLaw (rate x) (ProposalTree.retention (H x) (fun u => w (a u))))
      t ht E).trans (compile_prob H rate (fun u => w (a u)) t E)
    simp only [Set.preimage, he, sub_self, abs_zero, le_refl])
  simpa only [model, ProposalTree.marginal, Law.expect_const] using h

theorem adaptive_region_close {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (H : X → Finset S) (rate : X → Rate) (t : DecisionTree X (Option Bool) R)
    (D : Finset S → Finset X) (cap : Finset S → Prop)
    (ht : Protocol.Valid D cap ∅ t) (G : ℝ) (hG : 0 ≤ G)
    (hD : ∀ Q, cap Q → ∀ u, ∑ x ∈ D Q, (if u ∈ H x then (rate x : ℝ) else 0) ≤ G)
    (fallback : R) {μ : Law Ω} {ν : Law Γ} {w : Ω → Rate} {v : Γ → Rate} {s : ℕ}
    (hmom : Law.MatchingMoments μ ν (fun a => (w a : ℝ)) (fun b => (v b : ℝ)) s) :
    Law.Close (model H rate t μ w) (model H rate t ν v)
      (2 * Fintype.card S * G ^ (s + 1)) := by
  have hbudget (u : S) : (compile H rate t).budget u ≤ G := by
    rw [compiled_budget]
    simpa using budget_valid (fun x => if u ∈ H x then (rate x : ℝ) else 0)
      (fun x => by split_ifs <;> simp_all [(rate x).property.1]) D cap G
      (fun Q hQ => hD Q hQ u) t ∅ ht
  have hnr := Protocol.valid_no_repeats D cap t ∅ ht
  have hy := model_compile_close H rate t hnr μ w
  have hn := (model_compile_close H rate t hnr ν v).symm
  have hc := (compile H rate t).adaptive_proposals_close fallback hmom G hG hbudget
  convert (hy.trans hc).trans hn using 1
  ring

noncomputable def proposalsRead : DecisionTree X (Option Bool) R → (X → Option Bool) → ℕ
  | .leaf _, _ => 0
  | .query x next, o =>
      (if o x = none then 0 else 1) + proposalsRead (next (o x)) o

omit [Fintype X] [Fintype R] in
theorem proposals_agree (t : DecisionTree X (Option Bool) R) (o o' : X → Option Bool)
    (h : ∀ x ∈ t.used, o x = o' x) : proposalsRead t o = proposalsRead t o' := by
  induction t with
  | leaf => rfl
  | query x next ih =>
      have hx := h x (Finset.mem_insert_self _ _)
      simp only [proposalsRead, hx]
      congr 1
      apply ih
      intro y hy
      exact h y (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
        ⟨o' x, Finset.mem_univ _, hy⟩))

omit [Fintype X] [Fintype R] in
theorem proposals_update (t : DecisionTree X (Option Bool) R) (o : X → Option Bool)
    (x : X) (a : Option Bool) (hx : x ∉ t.used) :
    proposalsRead t (Function.update o x a) = proposalsRead t o := by
  apply proposals_agree
  intro y hy
  have hne : y ≠ x := by intro h; subst y; exact hx hy
  rw [Function.update_of_ne hne]

omit [Fintype S] [Fintype R] in
theorem expected_proposals_conditional (H : X → Finset S) (rate : X → Rate)
    (w : S → Rate) (t : DecisionTree X (Option Bool) R) (ht : t.NoRepeats) :
    (Law.pi (fun x => trialLaw (rate x) (ProposalTree.retention (H x) w))).expect
        (fun o => (proposalsRead t o : ℝ)) ≤ pathBudget (fun x => (rate x : ℝ)) t := by
  classical
  let μ := fun x => trialLaw (rate x) (ProposalTree.retention (H x) w)
  induction t with
  | leaf r => simp [proposalsRead, pathBudget]
  | query x next ih =>
      have hread :
          (fun o : X → Option Bool => (proposalsRead (.query x next) o : ℝ)) =
            fun o => (if o x = none then 0 else 1) + (proposalsRead (next (o x)) o : ℝ) := by
        funext o
        by_cases hx : o x = none <;> simp [proposalsRead, hx]
      rw [hread, Law.expect_add]
      have hfirst :
          (Law.pi μ).expect (fun o => if o x = none then (0 : ℝ) else 1) = (rate x : ℝ) := by
        rw [Law.expect_pi_coordinate μ (fun a => if a = none then (0 : ℝ) else 1) x]
        simp only [Law.expect, Fintype.sum_option, Fintype.sum_bool, μ,
          trial_mass_none, trial_mass_false, trial_mass_true]
        simp
        ring
      rw [hfirst, Law.expect_adaptive_coordinate μ x
        (fun a o => (proposalsRead (next a) o : ℝ))
        (fun a o b => by rw [proposals_update _ _ _ _ (ht.2 a)])]
      let B := max (pathBudget (fun x => (rate x : ℝ)) (next none))
        (max (pathBudget (fun x => (rate x : ℝ)) (next (some false)))
          (pathBudget (fun x => (rate x : ℝ)) (next (some true))))
      have hb (a : Option Bool) : pathBudget (fun x => (rate x : ℝ)) (next a) ≤ B := by
        cases a with
        | none => exact le_max_left _ _
        | some b =>
            cases b
            · exact (le_max_left _ _).trans (le_max_right _ _)
            · exact (le_max_right _ _).trans (le_max_right _ _)
      have hbound :
          (∑ a, (μ x).mass a * (Law.pi μ).expect (fun o => (proposalsRead (next a) o : ℝ))) ≤ B := by
        calc
          _ ≤ ∑ a, (μ x).mass a * B :=
            Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ((ih a (ht.1 a)).trans (hb a))
              ((μ x).nonneg a)
          _ = B := by rw [← Finset.sum_mul, (μ x).total, one_mul]
      exact add_le_add (le_refl _) hbound

noncomputable def oracleModel {Ω : Type*} [Fintype Ω] (H : X → Finset S) (rate : X → Rate)
    (μ : Law Ω) (w : Ω → Rate) : Law (X → Option Bool) :=
  (μ.iid S).bind (fun a =>
    Law.pi (fun x => trialLaw (rate x) (ProposalTree.retention (H x) (fun u => w (a u)))))

theorem expected_proposals {Ω : Type*} [Fintype Ω] (H : X → Finset S) (rate : X → Rate)
    (t : DecisionTree X (Option Bool) R) (D : Finset S → Finset X) (cap : Finset S → Prop)
    (ht : Protocol.Valid D cap ∅ t) (L : ℝ)
    (hD : ∀ Q, cap Q → ∑ x ∈ D Q, (rate x : ℝ) ≤ L)
    (μ : Law Ω) (w : Ω → Rate) :
    (oracleModel H rate μ w).expect (fun o => (proposalsRead t o : ℝ)) ≤ L := by
  rw [oracleModel, Law.expect_bind]
  have hnr := Protocol.valid_no_repeats D cap t ∅ ht
  have hb : pathBudget (fun x => (rate x : ℝ)) t ≤ L := by
    simpa using budget_valid (fun x => (rate x : ℝ)) (fun x => (rate x).property.1)
      D cap L hD t ∅ ht
  calc
    _ ≤ (μ.iid S).expect (fun _ => L) :=
      Law.expect_mono _ (fun a => (expected_proposals_conditional H rate (fun u => w (a u)) t hnr).trans hb)
    _ = L := Law.expect_const _ _

theorem proposals_tail {Ω : Type*} [Fintype Ω] (H : X → Finset S) (rate : X → Rate)
    (t : DecisionTree X (Option Bool) R) (D : Finset S → Finset X) (cap : Finset S → Prop)
    (ht : Protocol.Valid D cap ∅ t) (L : ℝ)
    (hD : ∀ Q, cap Q → ∑ x ∈ D Q, (rate x : ℝ) ≤ L)
    (μ : Law Ω) (w : Ω → Rate) (B : ℝ) (hB : 0 < B) :
    (oracleModel H rate μ w).prob {o | B < (proposalsRead t o : ℝ)} ≤ L / B :=
  (Law.markov_gt _ (fun o => Nat.cast_nonneg (proposalsRead t o)) hB).trans
    (div_le_div_of_nonneg_right (expected_proposals H rate t D cap ht L hD μ w) hB.le)

end ProposalProtocol

end SteinerLowerBound
