module

public import SteinerLowerBound.Caching
public import SteinerLowerBound.LawOperations

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace RetainedProtocol

variable {X S R : Type*} [Fintype X] [Fintype S] [Fintype R]

noncomputable def mulRate (p q : Rate) : Rate :=
  ⟨(p : ℝ) * (q : ℝ), mul_nonneg p.property.1 q.property.1,
    by simpa using mul_le_mul p.property.2 q.property.2 q.property.1 (show (0 : ℝ) ≤ 1 by norm_num)⟩

@[simp]
theorem mulRate_val (p q : Rate) : (mulRate p q : ℝ) = (p : ℝ) * (q : ℝ) := rfl

@[simp]
theorem bernoulli_false (p : Rate) :
    (CategoricalCoupling.bernoulli p).mass false = 1 - (p : ℝ) := rfl

@[simp]
theorem bernoulli_true (p : Rate) : (CategoricalCoupling.bernoulli p).mass true = (p : ℝ) := rfl

def retained : Option Bool → Bool
  | some true => true
  | _ => false

noncomputable def lift : DecisionTree X Bool R → DecisionTree X (Option Bool) R
  | .leaf r => .leaf r
  | .query x next => .query x (fun a => lift (next (retained a)))

omit [Fintype X] [Fintype S] [Fintype R] in
theorem lift_valid (D : Finset S → Finset X) (cap : Finset S → Prop)
    (t : DecisionTree X Bool R) (I : Finset X) (ht : Protocol.Valid D cap I t) :
    Protocol.Valid D cap I (lift t) := by
  induction t generalizing I with
  | leaf => exact ht
  | query x next ih => exact ⟨ht.1, fun a => ih (retained a) _ (ht.2 (retained a))⟩

omit [Fintype X] [Fintype R] in
theorem lift_used (t : DecisionTree X Bool R) : (lift t).used = t.used := by
  classical
  induction t with
  | leaf => rfl
  | query x next ih =>
      simp only [lift, DecisionTree.used, ih]
      ext y
      simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro (h | ⟨a, ha⟩)
        · exact Or.inl h
        · exact Or.inr ⟨retained a, ha⟩
      · rintro (h | ⟨b, hb⟩)
        · exact Or.inl h
        · exact Or.inr ⟨some b, by cases b <;> simpa [retained] using hb⟩

omit [Fintype X] [Fintype R] in
theorem lift_no_repeats (t : DecisionTree X Bool R) (ht : t.NoRepeats) :
    (lift t).NoRepeats := by
  induction t with
  | leaf => trivial
  | query x next ih =>
      exact ⟨fun a => ih (retained a) (ht.1 (retained a)),
        fun a => by simpa only [lift_used] using ht.2 (retained a)⟩

omit [Fintype X] [Fintype S] in
theorem lift_runLaw (H : X → Finset S) (rate : X → Rate) (w : S → Rate)
    (t : DecisionTree X Bool R) (E : Set R) :
    ((lift t).runLaw (fun x => ProposalProtocol.trialLaw (rate x) (ProposalTree.retention (H x) w))).prob E =
      (t.runLaw (fun x => CategoricalCoupling.bernoulli
        (mulRate (rate x) (ProposalTree.retention (H x) w)))).prob E := by
  induction t with
  | leaf => rfl
  | query x next ih =>
      simp only [lift, DecisionTree.runLaw, Law.prob_bind, Law.expect,
        Fintype.sum_option, Fintype.sum_bool, ProposalProtocol.trial_mass_none,
        ProposalProtocol.trial_mass_false, ProposalProtocol.trial_mass_true,
        bernoulli_false, bernoulli_true, mulRate_val, retained, ih]
      ring

noncomputable def model {Ω : Type*} [Fintype Ω] (H : X → Finset S) (rate : X → Rate)
    (t : DecisionTree X Bool R) (μ : Law Ω) (w : Ω → Rate) : Law R :=
  (μ.iid S).bind (fun a =>
    (Law.pi (fun x => CategoricalCoupling.bernoulli
      (mulRate (rate x) (ProposalTree.retention (H x) (fun u => w (a u)))))).map (fun o => t.output o))

theorem model_lift {Ω : Type*} [Fintype Ω] (H : X → Finset S) (rate : X → Rate)
    (t : DecisionTree X Bool R) (ht : t.NoRepeats) (μ : Law Ω) (w : Ω → Rate) :
    model H rate t μ w = ProposalProtocol.model H rate (lift t) μ w := by
  apply LawOperations.ext_prob
  intro E
  simp only [model, ProposalProtocol.model, Law.prob_bind, Law.prob_map]
  apply congrArg
  funext a
  have hleft := DecisionTree.deferred_sampling
    (fun x => CategoricalCoupling.bernoulli
      (mulRate (rate x) (ProposalTree.retention (H x) (fun u => w (a u))))) t ht E
  have hright := DecisionTree.deferred_sampling
    (fun x => ProposalProtocol.trialLaw (rate x) (ProposalTree.retention (H x) (fun u => w (a u))))
    (lift t) (lift_no_repeats t ht) E
  rw [lift_runLaw] at hright
  simpa only [Set.preimage] using hleft.trans hright.symm

theorem matching_close {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (H : X → Finset S) (rate : X → Rate) (t : DecisionTree X Bool R)
    (D : Finset S → Finset X) (cap : Finset S → Prop)
    (ht : Protocol.Valid D cap ∅ t) (G : ℝ) (hG : 0 ≤ G)
    (hD : ∀ Q, cap Q → ∀ u, ∑ x ∈ D Q, (if u ∈ H x then (rate x : ℝ) else 0) ≤ G)
    (fallback : R) {μ : Law Ω} {ν : Law Γ} {w : Ω → Rate} {v : Γ → Rate} {s : ℕ}
    (hmom : Law.MatchingMoments μ ν (fun a => (w a : ℝ)) (fun b => (v b : ℝ)) s) :
    Law.Close (model H rate t μ w) (model H rate t ν v)
      (2 * Fintype.card S * G ^ (s + 1)) := by
  have hnr := Protocol.valid_no_repeats D cap t ∅ ht
  rw [model_lift H rate t hnr, model_lift H rate t hnr]
  exact ProposalProtocol.adaptive_region_close H rate (lift t) D cap
    (lift_valid D cap t ∅ ht) G hG hD fallback hmom

end RetainedProtocol

namespace RetainedProtocol

variable {C U S R : Type*} [Fintype C] [Fintype U] [Fintype S] [Fintype R]

noncomputable local instance : DecidableEq (C × U) := Classical.decEq _

noncomputable def categoricalModel (p : C → U → Rate)
    (hs : ∀ c, ∑ u, (p c u : ℝ) ≤ 1) (t : DecisionTree (C × U) Bool R) : Law R :=
  (Law.pi (fun c => (CategoricalCoupling.categorical (p c) (hs c)).map
    CategoricalCoupling.characteristic)).map
    (fun o => t.output (fun q => o q.1 q.2))

noncomputable def independentModel (p : C → U → Rate) (t : DecisionTree (C × U) Bool R) : Law R :=
  (Law.pi (fun q : C × U => CategoricalCoupling.bernoulli (p q.1 q.2))).map (fun o => t.output o)

theorem independent_centers (p : C → U → Rate) (t : DecisionTree (C × U) Bool R) :
    (Law.pi (fun c => Law.pi (fun u => CategoricalCoupling.bernoulli (p c u)))).map
        (fun o => t.output (fun q => o q.1 q.2)) = independentModel p t := by
  have h := congrArg (fun μ => μ.map (fun o => t.output o))
    (LawOperations.pi_uncurry (fun c u => CategoricalCoupling.bernoulli (p c u)))
  rw [LawOperations.map_comp] at h
  exact h

omit [Fintype S] in
theorem categorical_independent_close (p : C → U → Rate)
    (hs : ∀ c, ∑ u, (p c u : ℝ) ≤ 1)
    (b : ℝ) (_hb : 0 ≤ b) (hpc : ∀ c, ∑ u, (p c u : ℝ) ≤ b)
    (D : Finset S → Finset (C × U)) (O : Finset S → Finset C) (cap : Finset S → Prop)
    (hD : ∀ E, cap E → ∀ q ∈ D E, q.1 ∈ O E)
    (N : ℕ) (hN : ∀ E, cap E → (O E).card ≤ N)
    (t : DecisionTree (C × U) Bool R) (ht : Protocol.Valid D cap ∅ t) :
    Law.Close (categoricalModel p hs t) (independentModel p t) ((N : ℝ) * b ^ 2) := by
  let μ : C → Law (U → Bool) := fun c =>
    (CategoricalCoupling.categorical (p c) (hs c)).map CategoricalCoupling.characteristic
  let ν : C → Law (U → Bool) := fun c => Law.pi (fun u => CategoricalCoupling.bernoulli (p c u))
  have hc : ∀ c, Law.Close (μ c) (ν c) (b ^ 2) := by
    intro c
    apply (CategoricalCoupling.categorical_function_close (p c) (hs c)).mono
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun u _ => (p c u).property.1) (hpc c) 2
  have h := Caching.adaptive_cached_close
    (Q := C × U) (C := C) (W := U → Bool) (A := Bool) (S := S) (R := R)
    Prod.fst (fun q o => o q.2) D O cap hD N hN t ht μ ν (b ^ 2) (sq_nonneg b) hc
  have he := independent_centers p t
  exact he ▸ h

end RetainedProtocol

end SteinerLowerBound
