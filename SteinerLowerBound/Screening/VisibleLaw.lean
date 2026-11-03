module

public import SteinerLowerBound.Screening
public import SteinerLowerBound.VisibleOracle

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening.Experiment

open HardDistribution

variable {S G I C W Z : Type*}
  [Fintype S] [Fintype G] [Fintype I] [Fintype C] [Fintype W] [Fintype Z]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq
noncomputable local instance (d : ℕ) : DecidableEq (Subsets S d) := Classical.decEq _
noncomputable local instance (d : ℕ) : DecidableEq (C × Subsets S d) := Classical.decEq _

noncomputable def normalizedWeight (k : Setup S W) (hM : 0 < k.M) (w : W) : Rate :=
  ⟨k.value w / k.M, div_nonneg (k.bounded w).1 hM.le,
    (div_le_one hM).mpr (k.bounded w).2⟩

@[simp]
theorem normalizedWeight_val (k : Setup S W) (hM : 0 < k.M) (w : W) :
    (normalizedWeight k hM w : ℝ) = k.value w / k.M := rfl

@[simp]
theorem normalizedWeight_restore (k : Setup S W) (hM : 0 < k.M) (w : W) :
    k.M * (normalizedWeight k hM w : ℝ) = k.value w := by
  simp only [normalizedWeight_val]
  field_simp

noncomputable def visibleRate (k : Setup S W) (hM : 0 < k.M)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) : Rate :=
  VisibleOracle.rate k.d k.d_ge_three k.enough_special k.H0 k.R k.M
    k.H0_nonneg k.R_pos hM.le hsmall

@[simp]
theorem visibleRate_val (k : Setup S W) (hM : 0 < k.M)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) :
    (visibleRate k hM hsmall : ℝ) =
      VisibleMass.candidateRate (S := S) k.d k.H0 k.R k.M := rfl

noncomputable def fillerFamilyLaw (k : Setup S W) : Law (C → Filler S) :=
  Law.pi (fun _ : C =>
    fillerLaw (by have := k.d_ge_three; have := k.enough_special; omega))

noncomputable def commonLaw (k : Setup S W) :
    Law (Equiv.Perm (Terminal S G I) × (C → Filler S)) :=
  Law.conditionalProduct (Law.uniform (Equiv.Perm (Terminal S G I)))
    (fun _ _ => fillerLaw (by have := k.d_ge_three; have := k.enough_special; omega))

noncomputable def visibleBits (k : Setup S W) (marks : C → Option (Subsets S k.d))
    (x : C × Subsets S k.d) : Bool :=
  decide (marks x.1 = some x.2)

noncomputable def visibleOutputLaw (k : Setup S W) (μ : Law W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (t : Equiv.Perm (Terminal S G I) → (C → Filler S) →
      DecisionTree (C × Subsets S k.d) Bool Z) : Law Z :=
  (law k μ hsmall).map (fun ω => (t ω.2 ω.1.1.2).output (visibleBits k ω.1.2))

theorem retainedRates_mass (k : Setup S W) (hM : 0 < k.M)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (w : S → W) (F : C → Filler S) (c : C) (H : Subsets S k.d) :
    (VisibleOracle.retainedRates k.d F (visibleRate k hM hsmall)
      (fun u => normalizedWeight k hM (w u)) c H : ℝ) =
      if VisibleOracle.ValidType k.d F (c, H) then
        starMass k.d k.H0 k.R (fun u => k.value (w u)) H / beta S else 0 := by
  classical
  by_cases hv : VisibleOracle.ValidType k.d F (c, H)
  · simp only [VisibleOracle.retainedRates, RetainedProtocol.mulRate_val,
      VisibleOracle.maskedRate, hv, ↓reduceIte, ProposalTree.retention, visibleRate_val]
    have h := VisibleOracle.retained_starMass k.d k.H0 k.R k.M
      (fun u => normalizedWeight k hM (w u)) H
    have hw : (fun u => k.M * (normalizedWeight k hM (w u) : ℝ)) =
        (fun u => k.value (w u)) := funext (fun u => normalizedWeight_restore k hM (w u))
    rwa [hw] at h
  · simp [VisibleOracle.retainedRates, VisibleOracle.maskedRate, hv]

theorem markLaw_some_retained (k : Setup S W) (hM : 0 < k.M)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (w : S → W) (F : C → Filler S) (c : C) (H : Subsets S k.d) :
    (MetricComparison.markLaw k w hsmall (F c)).mass (some H) =
      (VisibleOracle.retainedRates k.d F (visibleRate k hM hsmall)
        (fun u => normalizedWeight k hM (w u)) c H : ℝ) := by
  classical
  rw [retainedRates_mass]
  rcases hf : F c with (_ | u | e)
  · simp [MetricComparison.markLaw, VisibleOracle.ValidType, FillerSparsity.isPair, hf, Law.pure]
  · simp [MetricComparison.markLaw, VisibleOracle.ValidType, FillerSparsity.isPair, hf, Law.pure]
  · simp [MetricComparison.markLaw, VisibleOracle.ValidType, FillerSparsity.isPair, hf,
      fillerNeighbors, potentialLaw, Law.withNone]

theorem markLaw_eq_withNone (k : Setup S W) (hM : 0 < k.M)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (w : S → W) (F : C → Filler S) (c : C) :
    let p := VisibleOracle.retainedRates k.d F (visibleRate k hM hsmall)
      (fun u => normalizedWeight k hM (w u))
    let hs := (VisibleOracle.retained_sum k.d k.d_ge_three k.enough_special
      k.H0 k.R k.M k.H0_nonneg k.R_pos hM.le F (visibleRate k hM hsmall)
      rfl (fun u => normalizedWeight k hM (w u)) c).trans hsmall
    MetricComparison.markLaw k w hsmall (F c) =
      Law.withNone (fun H => (p c H : ℝ)) (fun H => (p c H).property.1) hs := by
  classical
  dsimp only
  let ν := MetricComparison.markLaw k w hsmall (F c)
  have hs (H : Subsets S k.d) : ν.mass (some H) =
      (VisibleOracle.retainedRates k.d F (visibleRate k hM hsmall)
        (fun u => normalizedWeight k hM (w u)) c H : ℝ) := markLaw_some_retained k hM hsmall w F c H
  apply LawOperations.ext_mass
  intro a
  cases a with
  | some H => exact hs H
  | none =>
      have ht := ν.total
      rw [Fintype.sum_option] at ht
      simp_rw [hs] at ht
      change ν.mass none = 1 - _
      linarith

theorem markLaw_characteristic (k : Setup S W) (hM : 0 < k.M)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (w : S → W) (F : C → Filler S) (c : C) :
    let p := VisibleOracle.retainedRates k.d F (visibleRate k hM hsmall)
      (fun u => normalizedWeight k hM (w u))
    let hs := (VisibleOracle.retained_sum k.d k.d_ge_three k.enough_special
      k.H0 k.R k.M k.H0_nonneg k.R_pos hM.le F (visibleRate k hM hsmall)
      rfl (fun u => normalizedWeight k hM (w u)) c).trans hsmall
    (MetricComparison.markLaw k w hsmall (F c)).map
        (fun a H => decide (a = some H)) =
      (CategoricalCoupling.categorical (p c) hs).map CategoricalCoupling.characteristic := by
  classical
  dsimp only
  rw [markLaw_eq_withNone k hM hsmall w F c, CategoricalCoupling.categorical,
    LawOperations.map_comp]
  apply congrArg
  funext a H
  cases a <;> simp [CategoricalCoupling.characteristic, eq_comm]

theorem marks_output_categorical (k : Setup S W) (hM : 0 < k.M)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (w : S → W) (F : C → Filler S) (t : DecisionTree (C × Subsets S k.d) Bool Z) :
    let p := VisibleOracle.retainedRates k.d F (visibleRate k hM hsmall)
      (fun u => normalizedWeight k hM (w u))
    let hs := fun c => (VisibleOracle.retained_sum k.d k.d_ge_three k.enough_special
      k.H0 k.R k.M k.H0_nonneg k.R_pos hM.le F (visibleRate k hM hsmall)
      rfl (fun u => normalizedWeight k hM (w u)) c).trans hsmall
    (Law.pi (fun c => MetricComparison.markLaw k w hsmall (F c))).map
        (fun marks => t.output (visibleBits k marks)) =
      RetainedProtocol.categoricalModel p hs t := by
  classical
  dsimp only
  have hcenters := LawOperations.pi_map
    (fun c => MetricComparison.markLaw k w hsmall (F c))
    (fun _ a H => decide (a = some H))
  simp_rw [markLaw_characteristic k hM hsmall w F] at hcenters
  have h := congrArg (fun μ : Law (C → Subsets S k.d → Bool) =>
    μ.map (fun o => t.output (fun x => o x.1 x.2))) hcenters
  rw [LawOperations.map_comp] at h
  exact h

theorem commonLaw_bind (k : Setup S W)
    (f : (Equiv.Perm (Terminal S G I) × (C → Filler S)) → Law Z) :
    (commonLaw (G := G) (I := I) k).bind f =
      (Law.uniform (Equiv.Perm (Terminal S G I))).bind
        (fun π => (fillerFamilyLaw (C := C) k).bind (fun F => f (π, F))) := by
  apply LawOperations.ext_prob
  intro E
  simp only [Law.prob_bind, commonLaw, Law.expect_conditionalProduct, fillerFamilyLaw]

/-- Exact disintegration: permutation and fillers are drawn before the
independent weight vector, with no restriction on the reported function. -/
theorem law_map_disintegrate (k : Setup S W) (μ : Law W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (f : Configuration (G := G) (I := I) (C := C) k → Z) :
    (law k μ hsmall).map f =
      (commonLaw (G := G) (I := I) k).bind (fun common =>
        (μ.iid S).bind (fun w =>
          (Law.pi (fun c => MetricComparison.markLaw k w hsmall (common.2 c))).map
            (fun marks => f (((w, common.2), marks), common.1)))) := by
  classical
  let πLaw := Law.uniform (Equiv.Perm (Terminal S G I))
  let FLaw := fillerFamilyLaw (C := C) k
  let out := fun w F (π : Equiv.Perm (Terminal S G I)) =>
    (Law.pi (fun c => MetricComparison.markLaw k w hsmall (F c))).map
      (fun marks => f (((w, F), marks), π))
  calc
    _ = (μ.iid S).bind (fun w => FLaw.bind (fun F => πLaw.bind (fun π => out w F π))) := by
      apply LawOperations.ext_prob
      intro E
      rw [Law.prob_map, law, Law.prob_shuffled_conditionalProduct, baseLaw,
        Law.expect_conditionalProduct]
      simp only [Law.prob_bind, out, FLaw, πLaw, fillerFamilyLaw, Law.prob_map,
        kernel, Set.mem_preimage, Set.mem_ofPred_eq]
      apply congrArg
      funext w
      apply congrArg
      funext F
      apply congrArg
      funext π
      have hk : kernel k hsmall (w, F) = (fun c => MetricComparison.markLaw k w hsmall (F c)) := by
        funext c
        rfl
      rw [hk]
      apply congrArg (Law.prob _)
      ext marks
      rfl
    _ = (μ.iid S).bind (fun w => πLaw.bind (fun π => FLaw.bind (fun F => out w F π))) := by
      apply congrArg
      funext w
      exact LawOperations.bind_comm FLaw πLaw (fun F π => out w F π)
    _ = πLaw.bind (fun π => (μ.iid S).bind (fun w => FLaw.bind (fun F => out w F π))) :=
      LawOperations.bind_comm (μ.iid S) πLaw _
    _ = πLaw.bind (fun π => FLaw.bind (fun F => (μ.iid S).bind (fun w => out w F π))) := by
      apply congrArg
      funext π
      exact LawOperations.bind_comm (μ.iid S) FLaw _
    _ = _ := by
      rw [commonLaw_bind]

theorem visibleOutputLaw_eq_common_model (k : Setup S W) (μ : Law W)
    (hM : 0 < k.M) (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (t : Equiv.Perm (Terminal S G I) → (C → Filler S) →
      DecisionTree (C × Subsets S k.d) Bool Z) :
    visibleOutputLaw k μ hsmall t =
      (commonLaw (G := G) (I := I) k).bind (fun common =>
        VisibleOracle.model k.d k.d_ge_three k.enough_special
          k.H0 k.R k.M k.H0_nonneg k.R_pos hM.le hsmall common.2
          (visibleRate k hM hsmall) rfl (t common.1 common.2) μ (normalizedWeight k hM)) := by
  rw [visibleOutputLaw, law_map_disintegrate]
  apply congrArg
  funext common
  apply congrArg
  funext w
  exact marks_output_categorical k hM hsmall w common.2 (t common.1 common.2)

theorem commonLaw_filler_probability (k : Setup S W) (E : Set (C → Filler S)) :
    (commonLaw (G := G) (I := I) k).prob {common | common.2 ∈ E} =
      (fillerFamilyLaw (C := C) k).prob E := by
  classical
  rw [Law.prob_eq_expect, commonLaw, Law.expect_conditionalProduct]
  change (Law.uniform (Equiv.Perm (Terminal S G I))).expect
    (fun _ => (fillerFamilyLaw (C := C) k).expect (fun F => if F ∈ E then 1 else 0)) = _
  rw [Law.expect_const, ← Law.prob_eq_expect]

theorem common_weights_independent (k : Setup S W) (μ : Law W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) :
    (law (G := G) (I := I) (C := C) k μ hsmall).map
      (fun ω => ((ω.2, ω.1.1.2), ω.1.1.1)) =
      Law.conditionalProduct (commonLaw (G := G) (I := I) (C := C) k)
        (fun _ _ => μ) := by
  classical
  rw [law_map_disintegrate]
  apply LawOperations.ext_prob
  intro E
  rw [Law.prob_bind, Law.prob_eq_expect, Law.expect_conditionalProduct]
  apply congrArg
  funext common
  simp only [Law.prob_bind, Law.prob_map]
  apply congrArg
  funext w
  by_cases he : (common, w) ∈ E
  · have hs : {marks : C → Option (Subsets S k.d) | (common, w) ∈ E} = Set.univ := by
      ext marks
      simp [he]
    simp only [Set.mem_ofPred_eq, he, ↓reduceIte]
    change (Law.pi (fun c => MetricComparison.markLaw k w hsmall (common.2 c))).prob
      {marks | (common, w) ∈ E} = 1
    rw [hs, Law.prob_univ]
  · have hs : {marks : C → Option (Subsets S k.d) | (common, w) ∈ E} = ∅ := by
      ext marks
      simp [he]
    simp only [Set.mem_ofPred_eq, he, ↓reduceIte]
    change (Law.pi (fun c => MetricComparison.markLaw k w hsmall (common.2 c))).prob
      {marks | (common, w) ∈ E} = 0
    rw [hs, Law.prob_empty]

theorem common_bad_probability (k : Setup S W)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * k.R) :
    (commonLaw (G := G) (I := I) (C := C) k).prob
        {common | FillerSparsity.Good k.R common.2}ᶜ ≤ 3 / (Fintype.card S : ℝ) ^ 3 := by
  have hm : 2 ≤ Fintype.card S := by have := k.d_ge_three; have := k.enough_special; omega
  have hgood := FillerSparsity.good_probability (C := C) hm k.R k.R_pos.le hC
  have hprob := commonLaw_filler_probability (G := G) (I := I) k
    {F : C → Filler S | FillerSparsity.Good k.R F}
  simp only [Set.mem_ofPred_eq] at hprob
  rw [Law.prob_compl, hprob]
  change 1 - (fillerFamilyLaw (C := C) k).prob {F | FillerSparsity.Good k.R F} ≤ _
  dsimp only [fillerFamilyLaw]
  linarith

/-- Visible-star records sampled from the actual gated distribution are close
for matching raw weight moments.  The only protocol hypothesis is pathwise
fresh reading within an accessible region of at most `2R` terminals. -/
theorem visible_protocol_close (k : Setup S W) (μ ν : Law W)
    (hM : 0 < k.M) (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (hRm : k.R ≤ Fintype.card S) (hlog : Real.log (Fintype.card S) ≤ k.R)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * k.R)
    (s : ℕ) (hmom : Law.MatchingMoments μ ν k.value k.value s)
    (t : Equiv.Perm (Terminal S G I) → (C → Filler S) →
      DecisionTree (C × Subsets S k.d) Bool Z)
    (ht : ∀ π F, Protocol.Valid (VisibleMass.region k.d F)
      (fun Q => (Q.card : ℝ) ≤ 2 * k.R) ∅ (t π F)) :
    Law.Close (visibleOutputLaw k μ hsmall t) (visibleOutputLaw k ν hsmall t)
      (2 * VisibleMass.openedBudget (S := S) k.R * (anchorConstant k.d k.H0 k.M / k.R) ^ 2 +
        2 * Fintype.card S *
          (VisibleMass.tripleConstant k.d k.H0 k.M *
            (5 * Real.exp 1 + 16) * k.R / Fintype.card S) ^ (s + 1) +
        3 / (Fintype.card S : ℝ) ^ 3) := by
  classical
  let ε := 2 * VisibleMass.openedBudget (S := S) k.R * (anchorConstant k.d k.H0 k.M / k.R) ^ 2 +
    2 * Fintype.card S *
      (VisibleMass.tripleConstant k.d k.H0 k.M *
        (5 * Real.exp 1 + 16) * k.R / Fintype.card S) ^ (s + 1)
  let model := fun (ρ : Law W) (common : Equiv.Perm (Terminal S G I) × (C → Filler S)) =>
    VisibleOracle.model k.d k.d_ge_three k.enough_special k.H0 k.R k.M
      k.H0_nonneg k.R_pos hM.le hsmall common.2 (visibleRate k hM hsmall) rfl
      (t common.1 common.2) ρ (normalizedWeight k hM)
  let good := {common : Equiv.Perm (Terminal S G I) × (C → Filler S) |
    FillerSparsity.Good k.R common.2}
  have hraw : Law.MatchingMoments μ ν
      (fun w => (normalizedWeight k hM w : ℝ))
      (fun w => (normalizedWeight k hM w : ℝ)) s := by
    simpa only [normalizedWeight_val] using hmom.scale k.M
  have hlog₀ : 0 ≤ Real.log (Fintype.card S) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ Fintype.card S by
      have := k.d_ge_three; have := k.enough_special; omega)
  have hbudget : 0 ≤ VisibleMass.openedBudget (S := S) k.R := by
    unfold VisibleMass.openedBudget
    have hR := k.R_pos
    positivity
  have htriple : 0 ≤ VisibleMass.tripleConstant k.d k.H0 k.M := by
    unfold VisibleMass.tripleConstant
    have hH₀ := k.H0_nonneg
    positivity
  have hε : 0 ≤ ε := by
    dsimp only [ε]
    have hR := k.R_pos
    positivity
  let fallback := (t (Equiv.refl (Terminal S G I)) (fun _ => Sum.inl ())).output (fun _ => false)
  have hpoint : ∀ common ∈ good, Law.Close (model μ common) (model ν common) ε := by
    intro common hgood
    exact VisibleOracle.moment_matched_records
      k.d k.d_ge_three k.enough_special k.H0 k.R k.M k.H0_nonneg k.R_pos hM.le
      hRm hlog hsmall common.2 hgood (visibleRate k hM hsmall) rfl
      (t common.1 common.2) (ht common.1 common.2) fallback hraw
  have hmix := LawOperations.bind_good (commonLaw (G := G) (I := I) k)
    (model μ) (model ν) good ε hε hpoint
  have hbad := common_bad_probability (G := G) (I := I) k hC
  rw [visibleOutputLaw_eq_common_model k μ hM hsmall,
    visibleOutputLaw_eq_common_model k ν hM hsmall]
  exact hmix.mono (by dsimp only [ε, good] at *; linarith)

end Screening.Experiment

end SteinerLowerBound
