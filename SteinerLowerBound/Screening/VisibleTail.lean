module

public import SteinerLowerBound.Screening.VisibleLaw
public import SteinerLowerBound.Simulation.Tree

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {X Z : Type*}

abbrev positiveRead (t : DecisionTree X Bool Z) (o : X → Bool) : ℕ :=
  Simulation.retainedRead t o

noncomputable def countAbove (B : ℝ) (n : ℕ) :
    DecisionTree X Bool Z → DecisionTree X Bool Bool
  | .leaf _ => .leaf (decide (B < (n : ℝ)))
  | .query x next => .query x (fun b => countAbove B (n + if b then 1 else 0) (next b))

theorem countAbove_output (B : ℝ) (n : ℕ) (t : DecisionTree X Bool Z) (o : X → Bool) :
    (countAbove B n t).output o = decide (B < ((n + positiveRead t o : ℕ) : ℝ)) := by
  induction t generalizing n with
  | leaf => simp [countAbove, positiveRead, Simulation.retainedRead, DecisionTree.output]
  | query x next ih =>
      simp only [countAbove, DecisionTree.output, ih, positiveRead,
        Simulation.retainedRead, Nat.add_assoc]
      exact Bool.decide_congr Iff.rfl

theorem retainedRead_countAbove (B : ℝ) (n : ℕ) (t : DecisionTree X Bool Z) (o : X → Bool) :
    Simulation.retainedRead (countAbove B n t) o = Simulation.retainedRead t o := by
  induction t generalizing n with
  | leaf => rfl
  | query x next ih => simp only [countAbove, Simulation.retainedRead, ih]

theorem positiveRead_le_proposals (t : DecisionTree X Bool Z) (o : X → Option Bool) :
    positiveRead t (fun x => RetainedProtocol.retained (o x)) ≤
      ProposalProtocol.proposalsRead (RetainedProtocol.lift t) o := by
  induction t with
  | leaf => exact Nat.le_refl _
  | query x next ih =>
      have hh := ih (RetainedProtocol.retained (o x))
      cases hb : o x with
      | none =>
          simpa [positiveRead, Simulation.retainedRead, RetainedProtocol.lift,
            ProposalProtocol.proposalsRead, hb, RetainedProtocol.retained] using hh
      | some b =>
          cases b <;>
            simp [positiveRead, Simulation.retainedRead, RetainedProtocol.lift,
              ProposalProtocol.proposalsRead, hb, RetainedProtocol.retained] at * <;> omega

theorem proposalsRead_countAbove (B : ℝ) (n : ℕ) (t : DecisionTree X Bool Z)
    (o : X → Option Bool) :
    ProposalProtocol.proposalsRead (RetainedProtocol.lift (countAbove B n t)) o =
      ProposalProtocol.proposalsRead (RetainedProtocol.lift t) o := by
  induction t generalizing n with
  | leaf => rfl
  | query x next ih =>
      simp only [countAbove, RetainedProtocol.lift, ProposalProtocol.proposalsRead, ih]

theorem countAbove_valid {S : Type*} (D : Finset S → Finset X) (cap : Finset S → Prop)
    (B : ℝ) (n : ℕ) (t : DecisionTree X Bool Z) (I : Finset X)
    (ht : Protocol.Valid D cap I t) : Protocol.Valid D cap I (countAbove B n t) := by
  induction t generalizing n I with
  | leaf => exact ht
  | query x next ih => exact ⟨ht.1, fun b => ih b _ _ (ht.2 b)⟩

variable {S W : Type*} [Fintype X] [Fintype S] [Fintype W]

theorem proposal_model_oracle {Y : Type*} [Fintype Y]
    (H : X → Finset S) (rate : X → Rate) (t : DecisionTree X (Option Bool) Y)
    (μ : Law W) (w : W → Rate) :
    ProposalProtocol.model H rate t μ w =
      (ProposalProtocol.oracleModel H rate μ w).map (fun o => t.output o) := by
  rw [ProposalProtocol.oracleModel, LawOperations.map_bind]
  rfl

theorem independent_positive_tail
    (H : X → Finset S) (rate : X → Rate)
    (t : DecisionTree X Bool Z) (D : Finset S → Finset X) (cap : Finset S → Prop)
    (ht : Protocol.Valid D cap ∅ t) (L : ℝ)
    (hD : ∀ Q, cap Q → ∑ x ∈ D Q, (rate x : ℝ) ≤ L)
    (μ : Law W) (w : W → Rate) (B : ℝ) (hB : 0 < B) :
    (RetainedProtocol.model H rate (countAbove B 0 t) μ w).prob {true} ≤ L / B := by
  classical
  let counted := countAbove B 0 t
  have hcount : Protocol.Valid D cap ∅ counted := countAbove_valid D cap B 0 t ∅ ht
  have hnr := Protocol.valid_no_repeats D cap counted ∅ hcount
  rw [RetainedProtocol.model_lift H rate counted hnr, proposal_model_oracle, Law.prob_map]
  have hsub : (fun o => (RetainedProtocol.lift counted).output o) ⁻¹' ({true} : Set Bool) ⊆
      {o | B < (ProposalProtocol.proposalsRead (RetainedProtocol.lift counted) o : ℝ)} := by
    intro o ho
    have hret := positiveRead_le_proposals t o
    rw [← proposalsRead_countAbove B 0 t o] at hret
    have hret' : (positiveRead t (fun x => RetainedProtocol.retained (o x)) : ℝ) ≤
        ProposalProtocol.proposalsRead (RetainedProtocol.lift counted) o := by exact_mod_cast hret
    have hout : (RetainedProtocol.lift counted).output o = true := ho
    rw [Simulation.output_lift] at hout
    change (countAbove B 0 t).output _ = true at hout
    rw [countAbove_output] at hout
    have hpos : B < (positiveRead t (fun x => RetainedProtocol.retained (o x)) : ℝ) := by
      simpa only [Nat.zero_add, decide_eq_true_eq] using hout
    exact hpos.trans_le hret'
  exact ((ProposalProtocol.oracleModel H rate μ w).prob_mono hsub).trans
    (ProposalProtocol.proposals_tail H rate (RetainedProtocol.lift counted) D cap
      (RetainedProtocol.lift_valid D cap counted ∅ hcount) L hD μ w B hB)

end Screening

namespace Screening.Experiment

open HardDistribution

variable {S G I C W Z : Type*}
  [Fintype S] [Fintype G] [Fintype I] [Fintype C] [Fintype W]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq
noncomputable local instance (d : ℕ) : DecidableEq (Subsets S d) := Classical.decEq _
noncomputable local instance (d : ℕ) : DecidableEq (C × Subsets S d) := Classical.decEq _

noncomputable def visibleLoad (k : Setup S W) : ℝ :=
  2 * VisibleMass.tripleConstant k.d k.H0 k.M * VisibleMass.openedBudget (S := S) k.R /
    Fintype.card S

noncomputable def categoricalError (k : Setup S W) : ℝ :=
  VisibleMass.openedBudget (S := S) k.R * (anchorConstant k.d k.H0 k.M / k.R) ^ 2

theorem visibleLoad_nonneg (k : Setup S W) (hM : 0 < k.M) : 0 ≤ visibleLoad k := by
  have hlog : 0 ≤ Real.log (Fintype.card S) :=
    Real.log_nonneg (by exact_mod_cast
      (show 1 ≤ Fintype.card S by have := k.d_ge_three; have := k.enough_special; omega))
  have hR := k.R_pos
  have hH₀ := k.H0_nonneg
  unfold visibleLoad VisibleMass.tripleConstant VisibleMass.openedBudget
  positivity

theorem categoricalError_nonneg (k : Setup S W) : 0 ≤ categoricalError k := by
  have hlog : 0 ≤ Real.log (Fintype.card S) :=
    Real.log_nonneg (by exact_mod_cast
      (show 1 ≤ Fintype.card S by have := k.d_ge_three; have := k.enough_special; omega))
  have hR := k.R_pos
  unfold categoricalError VisibleMass.openedBudget
  positivity

theorem categorical_positive_tail (k : Setup S W) (μ : Law W)
    (hM : 0 < k.M) (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (F : C → Filler S) (hF : FillerSparsity.Good k.R F)
    (t : DecisionTree (C × Subsets S k.d) Bool Z)
    (ht : Protocol.Valid (VisibleMass.region k.d F)
      (fun Q => (Q.card : ℝ) ≤ 2 * k.R) ∅ t) (B : ℝ) (hB : 0 < B) :
    (VisibleOracle.model k.d k.d_ge_three k.enough_special k.H0 k.R k.M
      k.H0_nonneg k.R_pos hM.le hsmall F (visibleRate k hM hsmall) rfl
      (countAbove B 0 t) μ (normalizedWeight k hM)).prob {true} ≤
        categoricalError k + visibleLoad k / B := by
  have hc := VisibleOracle.model_independent
    k.d k.d_ge_three k.enough_special k.H0 k.R k.M k.H0_nonneg k.R_pos hM.le
    hsmall F hF (visibleRate k hM hsmall) rfl (countAbove B 0 t)
    (countAbove_valid _ _ B 0 t ∅ ht) μ (normalizedWeight k hM)
  have hi := independent_positive_tail (fun x : C × Subsets S k.d => x.2.val)
    (VisibleOracle.maskedRate k.d F (visibleRate k hM hsmall)) t
    (VisibleMass.region k.d F) (fun Q => (Q.card : ℝ) ≤ 2 * k.R) ht (visibleLoad k)
    (by
      intro Q hQ
      rw [VisibleOracle.rates_region, visibleRate_val]
      exact VisibleMass.total_mass_le k.d k.d_ge_three k.enough_special
        k.H0_nonneg k.R_pos hM.le F hF Q hQ)
    μ (normalizedWeight k hM) B hB
  have hdiff := (abs_le.mp (hc {true})).2
  dsimp only [categoricalError] at *
  linarith

/-- Actual retained-read tail, including categorical replacement and the
single uniform filler failure.  The original tree may have arbitrary results. -/
theorem visible_positive_tail (k : Setup S W) (μ : Law W)
    (hM : 0 < k.M) (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * k.R)
    (t : Equiv.Perm (Terminal S G I) → (C → Filler S) →
      DecisionTree (C × Subsets S k.d) Bool Z)
    (ht : ∀ π F, Protocol.Valid (VisibleMass.region k.d F)
      (fun Q => (Q.card : ℝ) ≤ 2 * k.R) ∅ (t π F))
    (B : ℝ) (hB : 0 < B) :
    (law k μ hsmall).prob {ω |
      B < (Simulation.retainedRead (t ω.2 ω.1.1.2) (visibleBits k ω.1.2) : ℝ)} ≤
      categoricalError k + visibleLoad k / B + 3 / (Fintype.card S : ℝ) ^ 3 := by
  classical
  let counted := fun π F => countAbove B 0 (t π F)
  let model := fun (common : Equiv.Perm (Terminal S G I) × (C → Filler S)) =>
    VisibleOracle.model k.d k.d_ge_three k.enough_special k.H0 k.R k.M
      k.H0_nonneg k.R_pos hM.le hsmall common.2 (visibleRate k hM hsmall) rfl
      (counted common.1 common.2) μ (normalizedWeight k hM)
  let good := {common : Equiv.Perm (Terminal S G I) × (C → Filler S) |
    FillerSparsity.Good k.R common.2}
  let ε := categoricalError k + visibleLoad k / B
  have hε : 0 ≤ ε := add_nonneg (categoricalError_nonneg k)
    (div_nonneg (visibleLoad_nonneg k hM) hB.le)
  have hevent :
      (law k μ hsmall).prob {ω |
        B < (Simulation.retainedRead (t ω.2 ω.1.1.2) (visibleBits k ω.1.2) : ℝ)} =
      (visibleOutputLaw k μ hsmall counted).prob {true} := by
    rw [visibleOutputLaw, Law.prob_map]
    apply congrArg (Law.prob _)
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
      counted, countAbove_output, Nat.zero_add, decide_eq_true_eq, positiveRead]
  rw [hevent, visibleOutputLaw_eq_common_model k μ hM hsmall, Law.prob_bind]
  have hpoint (common : Equiv.Perm (Terminal S G I) × (C → Filler S)) :
      (model common).prob {true} ≤ ε + if common ∈ good then 0 else 1 := by
    by_cases hgood : common ∈ good
    · simpa only [ε, hgood, ↓reduceIte, add_zero, model, counted] using
        categorical_positive_tail k μ hM hsmall common.2 hgood
          (t common.1 common.2) (ht common.1 common.2) B hB
    · have hp := (model common).prob_le_one {true}
      simp only [hgood, ↓reduceIte]
      linarith
  have havg := (commonLaw (G := G) (I := I) k).expect_mono hpoint
  rw [Law.expect_add, Law.expect_const] at havg
  have hind :
      (commonLaw (G := G) (I := I) k).expect (fun common =>
        if common ∈ good then (0 : ℝ) else 1) =
          (commonLaw (G := G) (I := I) k).prob goodᶜ := by
    rw [Law.prob_eq_expect]
    apply congrArg
    funext common
    by_cases hg : common ∈ good <;> simp [hg]
  rw [hind] at havg
  have hbad := common_bad_probability (G := G) (I := I) k hC
  change _ ≤ ε + _
  dsimp only [good] at *
  exact havg.trans (by linarith)

theorem visible_retained_tail (k : Setup S W) (μ : Law W)
    (hM : 0 < k.M) (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * k.R)
    (t : Equiv.Perm (Terminal S G I) → (C → Filler S) →
      DecisionTree (C × Subsets S k.d) Bool Z)
    (ht : ∀ π F, Protocol.Valid (VisibleMass.region k.d F)
      (fun Q => (Q.card : ℝ) ≤ 2 * k.R) ∅ (t π F)) :
    (law k μ hsmall).prob {ω |
      k.R / k.d < (Simulation.retainedRead (t ω.2 ω.1.1.2) (visibleBits k ω.1.2) : ℝ)} ≤
      VisibleMass.openedBudget (S := S) k.R * (anchorConstant k.d k.H0 k.M / k.R) ^ 2 +
        k.d * (2 * VisibleMass.tripleConstant k.d k.H0 k.M *
          VisibleMass.openedBudget (S := S) k.R / Fintype.card S) / k.R +
        3 / (Fintype.card S : ℝ) ^ 3 := by
  have hd : (0 : ℝ) < k.d := by exact_mod_cast (show 0 < k.d by have := k.d_ge_three; omega)
  have h := visible_positive_tail k μ hM hsmall hC t ht (k.R / k.d) (div_pos k.R_pos hd)
  convert h using 1
  unfold categoricalError visibleLoad
  field_simp
  <;> ring

theorem visible_retained_product_tail (k : Setup S W) (μ : Law W)
    (hM : 0 < k.M) (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * k.R)
    (t : Equiv.Perm (Terminal S G I) → (C → Filler S) →
      DecisionTree (C × Subsets S k.d) Bool Z)
    (ht : ∀ π F, Protocol.Valid (VisibleMass.region k.d F)
      (fun Q => (Q.card : ℝ) ≤ 2 * k.R) ∅ (t π F)) :
    (law k μ hsmall).prob {ω |
      k.R < k.d * (Simulation.retainedRead (t ω.2 ω.1.1.2) (visibleBits k ω.1.2) : ℝ)} ≤
      categoricalError k + k.d * visibleLoad k / k.R + 3 / (Fintype.card S : ℝ) ^ 3 := by
  have hd : (0 : ℝ) < k.d := by exact_mod_cast (show 0 < k.d by have := k.d_ge_three; omega)
  have hevent :
      {ω : Configuration (G := G) (I := I) (C := C) k |
        k.R < k.d * (Simulation.retainedRead (t ω.2 ω.1.1.2) (visibleBits k ω.1.2) : ℝ)} =
      {ω | k.R / k.d <
        (Simulation.retainedRead (t ω.2 ω.1.1.2) (visibleBits k ω.1.2) : ℝ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, div_lt_iff₀ hd]
    rw [mul_comm]
  rw [hevent]
  exact visible_retained_tail k μ hM hsmall hC t ht

end Screening.Experiment

end SteinerLowerBound
