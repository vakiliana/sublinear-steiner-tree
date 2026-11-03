module

public import SteinerLowerBound.RetainedProtocol
public import SteinerLowerBound.VisibleMass

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace VisibleOracle

open HardDistribution

variable {S C ROut : Type*} [Fintype S] [Fintype C] [Fintype ROut]

def ValidType (d : ℕ) (F : C → Filler S) (x : C × Subsets S d) : Prop :=
  FillerSparsity.isPair (F x.1) = true ∧ fillerNeighbors (F x.1) ⊆ x.2.val

noncomputable def maskedRate (d : ℕ) (F : C → Filler S) (rate : Rate)
    (x : C × Subsets S d) : Rate :=
  if ValidType d F x then rate else ⟨0, le_refl _, zero_le_one⟩

theorem region_valid (d : ℕ) (F : C → Filler S) (Q : Finset S)
    (x : C × Subsets S d) (hx : x ∈ VisibleMass.region d F Q) :
    ValidType d F x ∧ x.1 ∈ VisibleMass.openCenters F Q := by
  obtain ⟨c, hc, hH⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨H, hSupport, rfl⟩ := Finset.mem_image.mp hH
  exact ⟨⟨(Finset.mem_filter.mp hc).2.1, (Finset.mem_filter.mp hSupport).2.1⟩, hc⟩

theorem rates_region (d : ℕ) (F : C → Filler S) (Q : Finset S) (rate : Rate) :
    (∑ x ∈ VisibleMass.region d F Q, (maskedRate d F rate x : ℝ)) =
      (rate : ℝ) * (VisibleMass.region d F Q).card := by
  calc
    _ = ∑ _x ∈ VisibleMass.region d F Q, (rate : ℝ) :=
      Finset.sum_congr rfl fun x hx => by simp [maskedRate, (region_valid d F Q x hx).1]
    _ = _ := by simp [mul_comm]

theorem usage_region (d : ℕ) (F : C → Filler S) (Q : Finset S) (rate : Rate) (u : S) :
    (∑ x ∈ VisibleMass.region d F Q, (if u ∈ x.2.val then (maskedRate d F rate x : ℝ) else 0)) =
      (rate : ℝ) * ((VisibleMass.region d F Q).filter (fun x => u ∈ x.2.val)).card := by
  classical
  calc
    _ = ∑ x ∈ VisibleMass.region d F Q, if u ∈ x.2.val then (rate : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [maskedRate, (region_valid d F Q x hx).1]
    _ = _ := by rw [← Finset.sum_filter]; simp [mul_comm]

theorem candidate_le_anchor (d : ℕ) (hd : 3 ≤ d) (hm : d ≤ Fintype.card S)
    {H0 R M : ℝ} (hH0 : 0 ≤ H0) (hR : 0 < R) (hM : 0 ≤ M) :
    VisibleMass.candidateRate (S := S) d H0 R M ≤ anchorConstant d H0 M / R := by
  have hr := VisibleMass.candidateRate_nonneg (S := S) d hH0 hR.le hM
  have hc : (1 : ℝ) ≤ (Fintype.card S - 2).choose (d - 2) := by
    exact_mod_cast Nat.choose_pos (show d - 2 ≤ Fintype.card S - 2 by omega)
  have hid :
      ((Fintype.card S).choose d : ℝ) * (d.choose 2 : ℝ) =
        ((Fintype.card S).choose 2 : ℝ) *
          ((Fintype.card S - 2).choose (d - 2) : ℝ) := by
    exact_mod_cast (Nat.choose_mul (n := Fintype.card S) (show 2 ≤ d by omega))
  have hd₀ : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hR₀ : R ≠ 0 := hR.ne'
  have hm₂ : ((Fintype.card S).choose 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show 2 ≤ Fintype.card S by omega)).ne'
  have hmd : ((Fintype.card S).choose d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hm).ne'
  calc
    _ ≤ VisibleMass.candidateRate (S := S) d H0 R M *
        (Fintype.card S - 2).choose (d - 2) := by nlinarith
    _ = _ := by
      unfold VisibleMass.candidateRate beta anchorConstant
      field_simp
      nlinarith [congrArg (fun z : ℝ => H0 * M ^ d * z) hid]

noncomputable def rate (d : ℕ) (hd : 3 ≤ d) (hm : d ≤ Fintype.card S)
    (H0 R M : ℝ) (hH0 : 0 ≤ H0) (hR : 0 < R) (hM : 0 ≤ M)
    (hsmall : anchorConstant d H0 M / R ≤ 1) : Rate :=
  ⟨VisibleMass.candidateRate (S := S) d H0 R M,
    VisibleMass.candidateRate_nonneg d hH0 hR.le hM,
    (candidate_le_anchor d hd hm hH0 hR hM).trans hsmall⟩

noncomputable def retainedRates (d : ℕ) (F : C → Filler S) (rate : Rate) (w : S → Rate)
    (c : C) (H : Subsets S d) : Rate :=
  RetainedProtocol.mulRate (maskedRate d F rate (c, H)) (ProposalTree.retention H.val w)

theorem retained_starMass (d : ℕ) (H0 R M : ℝ) (w : S → Rate) (H : Subsets S d) :
    VisibleMass.candidateRate (S := S) d H0 R M * ∏ u ∈ H.val, (w u : ℝ) =
      starMass d H0 R (fun u => M * (w u : ℝ)) H / beta S := by
  have hp : (∏ u ∈ H.val, M * (w u : ℝ)) =
      M ^ d * ∏ u ∈ H.val, (w u : ℝ) := by
    rw [Finset.prod_mul_distrib]
    simp [H.property]
  rw [starMass, hp]
  unfold VisibleMass.candidateRate
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

omit [Fintype C] in
theorem retained_sum (d : ℕ) (hd : 3 ≤ d) (hm : d ≤ Fintype.card S)
    (H0 R M : ℝ) (hH0 : 0 ≤ H0) (hR : 0 < R) (hM : 0 ≤ M)
    (F : C → Filler S) (rate : Rate)
    (hRate : (rate : ℝ) = VisibleMass.candidateRate (S := S) d H0 R M)
    (w : S → Rate) (c : C) :
    (∑ H : Subsets S d, (retainedRates d F rate w c H : ℝ)) ≤ anchorConstant d H0 M / R := by
  classical
  by_cases hc : FillerSparsity.isPair (F c) = true
  · let e : Subsets S 2 := ⟨fillerNeighbors (F c), FillerSparsity.pair_card (F c) hc⟩
    have hmass (H : Subsets S d) :
        (retainedRates d F rate w c H : ℝ) =
          if e.val ⊆ H.val then starMass d H0 R (fun u => M * (w u : ℝ)) H / beta S else 0 := by
      by_cases hH : e.val ⊆ H.val
      · have hH' : fillerNeighbors (F c) ⊆ H.val := hH
        simp only [retainedRates, RetainedProtocol.mulRate_val, maskedRate, ValidType, hc,
          true_and, hH', hH, ↓reduceIte, ProposalTree.retention, hRate]
        exact retained_starMass d H0 R M w H
      · have hH' : ¬fillerNeighbors (F c) ⊆ H.val := hH
        simp [retainedRates, maskedRate, ValidType, hc, hH', hH]
    simp_rw [hmass]
    exact anchor_mass_le d (by omega) hm e hH0 hR
      (fun u => mul_nonneg hM (w u).property.1)
      (fun u => by nlinarith [(w u).property.2])
  · have hb : 0 ≤ anchorConstant d H0 M / R := by unfold anchorConstant; positivity
    simpa [retainedRates, maskedRate, ValidType, hc] using hb

theorem opened_quota (d : ℕ) (hd : 3 ≤ d) (hm : d ≤ Fintype.card S)
    (R : ℝ) (hR : 0 < R) (F : C → Filler S) (hF : FillerSparsity.Good R F) :
    ∀ Q : Finset S, (Q.card : ℝ) ≤ 2 * R →
      (VisibleMass.openCenters F Q).card ≤ ⌊VisibleMass.openedBudget (S := S) R⌋₊ := by
  have hB₀ : 0 ≤ VisibleMass.openedBudget (S := S) R := by
    apply (Nat.cast_nonneg (FillerSparsity.edgeCount F ∅)).trans
    exact VisibleMass.opened_le F R hR.le (by omega) hF ∅ (by simp; linarith)
  intro Q hQ
  apply (Nat.le_floor_iff hB₀).mpr
  simpa only [VisibleMass.open_card] using VisibleMass.opened_le F R hR.le (by omega) hF Q hQ

theorem categorical_replacement (d : ℕ) (hd : 3 ≤ d) (hm : d ≤ Fintype.card S)
    (H0 R M : ℝ) (hH0 : 0 ≤ H0) (hR : 0 < R) (hM : 0 ≤ M)
    (hsmall : anchorConstant d H0 M / R ≤ 1)
    (F : C → Filler S) (hF : FillerSparsity.Good R F) (rate : Rate)
    (hRate : (rate : ℝ) = VisibleMass.candidateRate (S := S) d H0 R M)
    (w : S → Rate) (t : DecisionTree (C × Subsets S d) Bool ROut)
    (ht : Protocol.Valid (VisibleMass.region d F) (fun Q => (Q.card : ℝ) ≤ 2 * R) ∅ t) :
    let p := retainedRates d F rate w
    let hs := fun c => (retained_sum d hd hm H0 R M hH0 hR hM F rate hRate w c).trans hsmall
    Law.Close (RetainedProtocol.categoricalModel p hs t) (RetainedProtocol.independentModel p t)
      (VisibleMass.openedBudget (S := S) R * (anchorConstant d H0 M / R) ^ 2) := by
  classical
  dsimp only
  have hb : 0 ≤ anchorConstant d H0 M / R := by unfold anchorConstant; positivity
  have h := RetainedProtocol.categorical_independent_close
    (retainedRates d F rate w)
    (fun c => (retained_sum d hd hm H0 R M hH0 hR hM F rate hRate w c).trans hsmall)
    (anchorConstant d H0 M / R) hb
    (retained_sum d hd hm H0 R M hH0 hR hM F rate hRate w)
    (VisibleMass.region d F) (VisibleMass.openCenters F)
    (fun Q => (Q.card : ℝ) ≤ 2 * R)
    (fun Q _ x hx => (region_valid d F Q x hx).2)
    ⌊VisibleMass.openedBudget (S := S) R⌋₊ (opened_quota d hd hm R hR F hF) t ht
  apply h.mono
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Nat.floor_le
  have h' := VisibleMass.opened_le F R hR.le (show 1 ≤ Fintype.card S by omega) hF ∅
    (by simp; linarith)
  exact (Nat.cast_nonneg _).trans h'

theorem independent_matching {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (d : ℕ) (hd : 3 ≤ d) (hm : d ≤ Fintype.card S)
    (H0 R M : ℝ) (hH0 : 0 ≤ H0) (hR : 0 < R) (hM : 0 ≤ M)
    (hRm : R ≤ Fintype.card S) (hlog : Real.log (Fintype.card S) ≤ R)
    (F : C → Filler S) (hF : FillerSparsity.Good R F) (rate : Rate)
    (hRate : (rate : ℝ) = VisibleMass.candidateRate (S := S) d H0 R M)
    (t : DecisionTree (C × Subsets S d) Bool ROut)
    (ht : Protocol.Valid (VisibleMass.region d F) (fun Q => (Q.card : ℝ) ≤ 2 * R) ∅ t)
    (fallback : ROut) {μ : Law Ω} {ν : Law Γ} {w : Ω → Rate} {v : Γ → Rate} {s : ℕ}
    (hmom : Law.MatchingMoments μ ν (fun a => (w a : ℝ)) (fun b => (v b : ℝ)) s) :
    Law.Close
      (RetainedProtocol.model (fun x : C × Subsets S d => x.2.val) (maskedRate d F rate) t μ w)
      (RetainedProtocol.model (fun x : C × Subsets S d => x.2.val) (maskedRate d F rate) t ν v)
      (2 * Fintype.card S *
        (VisibleMass.tripleConstant d H0 M * (5 * Real.exp 1 + 16) * R / Fintype.card S) ^ (s + 1)) := by
  apply RetainedProtocol.matching_close _ _ t (VisibleMass.region d F)
    (fun Q => (Q.card : ℝ) ≤ 2 * R) ht _ _ _ fallback hmom
  · unfold VisibleMass.tripleConstant
    positivity
  · intro Q hQ u
    rw [usage_region, hRate]
    exact VisibleMass.vertex_mass_le d hd hm hH0 hR hM hRm hlog F hF Q hQ u

noncomputable def model {Ω : Type*} [Fintype Ω]
    (d : ℕ) (hd : 3 ≤ d) (hm : d ≤ Fintype.card S)
    (H0 R M : ℝ) (hH0 : 0 ≤ H0) (hR : 0 < R) (hM : 0 ≤ M)
    (hsmall : anchorConstant d H0 M / R ≤ 1) (F : C → Filler S) (rate : Rate)
    (hRate : (rate : ℝ) = VisibleMass.candidateRate (S := S) d H0 R M)
    (t : DecisionTree (C × Subsets S d) Bool ROut) (μ : Law Ω) (w : Ω → Rate) : Law ROut :=
  (μ.iid S).bind (fun a =>
    RetainedProtocol.categoricalModel (retainedRates d F rate (fun u => w (a u)))
      (fun c => (retained_sum d hd hm H0 R M hH0 hR hM F rate hRate
        (fun u => w (a u)) c).trans hsmall) t)

theorem model_independent {Ω : Type*} [Fintype Ω]
    (d : ℕ) (hd : 3 ≤ d) (hm : d ≤ Fintype.card S)
    (H0 R M : ℝ) (hH0 : 0 ≤ H0) (hR : 0 < R) (hM : 0 ≤ M)
    (hsmall : anchorConstant d H0 M / R ≤ 1)
    (F : C → Filler S) (hF : FillerSparsity.Good R F) (rate : Rate)
    (hRate : (rate : ℝ) = VisibleMass.candidateRate (S := S) d H0 R M)
    (t : DecisionTree (C × Subsets S d) Bool ROut)
    (ht : Protocol.Valid (VisibleMass.region d F) (fun Q => (Q.card : ℝ) ≤ 2 * R) ∅ t)
    (μ : Law Ω) (w : Ω → Rate) :
    Law.Close (model d hd hm H0 R M hH0 hR hM hsmall F rate hRate t μ w)
      (RetainedProtocol.model (fun x : C × Subsets S d => x.2.val) (maskedRate d F rate) t μ w)
      (VisibleMass.openedBudget (S := S) R * (anchorConstant d H0 M / R) ^ 2) := by
  have h := Law.Close.bind_same (μ.iid S)
    (fun a => RetainedProtocol.categoricalModel (retainedRates d F rate (fun u => w (a u)))
      (fun c => (retained_sum d hd hm H0 R M hH0 hR hM F rate hRate
        (fun u => w (a u)) c).trans hsmall) t)
    (fun a => RetainedProtocol.independentModel (retainedRates d F rate (fun u => w (a u))) t)
    (fun _ => VisibleMass.openedBudget (S := S) R * (anchorConstant d H0 M / R) ^ 2)
    (fun a => categorical_replacement d hd hm H0 R M hH0 hR hM hsmall F hF rate hRate
      (fun u => w (a u)) t ht)
  simpa only [model, RetainedProtocol.model, RetainedProtocol.independentModel, retainedRates,
    Law.expect_const] using h

theorem moment_matched_records {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (d : ℕ) (hd : 3 ≤ d) (hm : d ≤ Fintype.card S)
    (H0 R M : ℝ) (hH0 : 0 ≤ H0) (hR : 0 < R) (hM : 0 ≤ M)
    (hRm : R ≤ Fintype.card S) (hlog : Real.log (Fintype.card S) ≤ R)
    (hsmall : anchorConstant d H0 M / R ≤ 1)
    (F : C → Filler S) (hF : FillerSparsity.Good R F) (rate : Rate)
    (hRate : (rate : ℝ) = VisibleMass.candidateRate (S := S) d H0 R M)
    (t : DecisionTree (C × Subsets S d) Bool ROut)
    (ht : Protocol.Valid (VisibleMass.region d F) (fun Q => (Q.card : ℝ) ≤ 2 * R) ∅ t)
    (fallback : ROut) {μ : Law Ω} {ν : Law Γ} {w : Ω → Rate} {v : Γ → Rate} {s : ℕ}
    (hmom : Law.MatchingMoments μ ν (fun a => (w a : ℝ)) (fun b => (v b : ℝ)) s) :
    Law.Close (model d hd hm H0 R M hH0 hR hM hsmall F rate hRate t μ w)
      (model d hd hm H0 R M hH0 hR hM hsmall F rate hRate t ν v)
      (2 * VisibleMass.openedBudget (S := S) R * (anchorConstant d H0 M / R) ^ 2 +
        2 * Fintype.card S *
          (VisibleMass.tripleConstant d H0 M * (5 * Real.exp 1 + 16) * R / Fintype.card S) ^ (s + 1)) := by
  have hy := model_independent d hd hm H0 R M hH0 hR hM hsmall F hF rate hRate t ht μ w
  have hn := (model_independent d hd hm H0 R M hH0 hR hM hsmall F hF rate hRate t ht ν v).symm
  have hc := independent_matching d hd hm H0 R M hH0 hR hM hRm hlog F hF rate hRate t ht fallback hmom
  convert (hy.trans hc).trans hn using 1
  ring

end VisibleOracle

end SteinerLowerBound
