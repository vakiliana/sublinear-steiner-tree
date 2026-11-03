module

public import SteinerLowerBound.FillerSparsity

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace VisibleMass

open HardDistribution

variable {S C : Type*} [Fintype S] [Fintype C]

noncomputable def openCenters (F : C → Filler S) (Q : Finset S) : Finset C :=
  Finset.univ.filter (fun c => FillerSparsity.inside Q (F c))

noncomputable def supportsAt (d : ℕ) (F : C → Filler S) (Q : Finset S) (c : C) :
    Finset (Subsets S d) :=
  Finset.univ.filter (fun H => fillerNeighbors (F c) ⊆ H.val ∧ 3 ≤ (H.val ∩ Q).card)

noncomputable def region (d : ℕ) (F : C → Filler S) (Q : Finset S) :
    Finset (C × Subsets S d) :=
  (openCenters F Q).biUnion (fun c => (supportsAt d F Q c).image (fun H => (c, H)))

omit [Fintype S] in
theorem open_card (F : C → Filler S) (Q : Finset S) :
    (openCenters F Q).card = FillerSparsity.edgeCount F Q := rfl

omit [Fintype S] in
theorem anchor_count_le_degree (F : C → Filler S) (Q : Finset S) (u : S) :
    ((openCenters F Q).filter (fun c => u ∈ fillerNeighbors (F c))).card ≤
      FillerSparsity.degree F u := by
  classical
  apply Finset.card_le_card
  intro c hc
  obtain ⟨hc, hu⟩ := Finset.mem_filter.mp hc
  have hp := (Finset.mem_filter.mp hc).2.1
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp, hu⟩

theorem triple_count (d : ℕ) (hd : 3 ≤ d) (e : Finset S) (he : e.card = 2)
    (u : S) (hu : u ∉ e) :
    (Finset.univ.filter (fun H : Subsets S d => insert u e ⊆ H.val)).card =
      (Fintype.card S - 3).choose (d - 3) := by
  have hc : (insert u e).card = 3 := by simp [hu, he]
  simpa only [hc] using prescribed_count d (insert u e) (by omega)

theorem supports_count (d : ℕ) (hd : 3 ≤ d) (F : C → Filler S)
    (Q : Finset S) (c : C) (hc : c ∈ openCenters F Q) :
    (supportsAt d F Q c).card ≤ Q.card * (Fintype.card S - 3).choose (d - 3) := by
  classical
  let e := fillerNeighbors (F c)
  have he : e.card = 2 := FillerSparsity.pair_card (F c) (Finset.mem_filter.mp hc).2.1
  let triples (u : S) : Finset (Subsets S d) :=
    Finset.univ.filter (fun H => insert u e ⊆ H.val)
  have hs : supportsAt d F Q c ⊆ (Q \ e).biUnion triples := by
    intro H hH
    obtain ⟨hEH, hHQ⟩ := (Finset.mem_filter.mp hH).2
    have hlt : e.card < (H.val ∩ Q).card := by omega
    obtain ⟨u, hu, hue⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine Finset.mem_biUnion.mpr ⟨u, Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hu).2, hue⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact Finset.insert_subset_iff.mpr ⟨(Finset.mem_inter.mp hu).1, hEH⟩
  calc
    _ ≤ ((Q \ e).biUnion triples).card := Finset.card_le_card hs
    _ ≤ ∑ u ∈ Q \ e, (triples u).card := Finset.card_biUnion_le
    _ = (Q \ e).card * (Fintype.card S - 3).choose (d - 3) := by
      have h (u : S) (hu : u ∈ Q \ e) :
          (triples u).card = (Fintype.card S - 3).choose (d - 3) :=
        triple_count d hd e he u (Finset.mem_sdiff.mp hu).2
      calc
        _ = ∑ _u ∈ Q \ e, (Fintype.card S - 3).choose (d - 3) :=
          Finset.sum_congr rfl h
        _ = _ := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset)

theorem nonanchor_supports_count (d : ℕ) (hd : 3 ≤ d) (F : C → Filler S)
    (Q : Finset S) (c : C) (hc : c ∈ openCenters F Q) (u : S)
    (hu : u ∉ fillerNeighbors (F c)) :
    ((supportsAt d F Q c).filter (fun H => u ∈ H.val)).card ≤
      (Fintype.card S - 3).choose (d - 3) := by
  classical
  have he : (fillerNeighbors (F c)).card = 2 :=
    FillerSparsity.pair_card (F c) (Finset.mem_filter.mp hc).2.1
  have hs : (supportsAt d F Q c).filter (fun H => u ∈ H.val) ⊆
      Finset.univ.filter (fun H : Subsets S d => insert u (fillerNeighbors (F c)) ⊆ H.val) := by
    intro H hH
    obtain ⟨hH, huH⟩ := Finset.mem_filter.mp hH
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.insert_subset_iff.mpr ⟨huH, (Finset.mem_filter.mp hH).2.1⟩⟩
  exact (Finset.card_le_card hs).trans_eq (triple_count d hd _ he u hu)

theorem region_card (d : ℕ) (hd : 3 ≤ d) (F : C → Filler S) (Q : Finset S) :
    (region d F Q).card ≤
      FillerSparsity.edgeCount F Q * Q.card * (Fintype.card S - 3).choose (d - 3) := by
  classical
  calc
    _ ≤ ∑ c ∈ openCenters F Q, ((supportsAt d F Q c).image (fun H => (c, H))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ openCenters F Q, Q.card * (Fintype.card S - 3).choose (d - 3) :=
      Finset.sum_le_sum fun c hc => Finset.card_image_le.trans (supports_count d hd F Q c hc)
    _ = _ := by simp [open_card, Nat.mul_assoc]

theorem region_vertex_card (d : ℕ) (hd : 3 ≤ d) (F : C → Filler S) (Q : Finset S) (u : S) :
    ((region d F Q).filter (fun x => u ∈ x.2.val)).card ≤
      (FillerSparsity.degree F u * Q.card + FillerSparsity.edgeCount F Q) *
        (Fintype.card S - 3).choose (d - 3) := by
  classical
  let K := (Fintype.card S - 3).choose (d - 3)
  have hs : (region d F Q).filter (fun x => u ∈ x.2.val) ⊆
      (openCenters F Q).biUnion (fun c =>
        ((supportsAt d F Q c).filter (fun H => u ∈ H.val)).image (fun H => (c, H))) := by
    intro x hx
    obtain ⟨hx, hu⟩ := Finset.mem_filter.mp hx
    obtain ⟨c, hc, hImage⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨H, hSupport, rfl⟩ := Finset.mem_image.mp hImage
    exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_image.mpr
      ⟨H, Finset.mem_filter.mpr ⟨hSupport, hu⟩, rfl⟩⟩
  have hp (c : C) (hc : c ∈ openCenters F Q) :
      ((supportsAt d F Q c).filter (fun H => u ∈ H.val)).card ≤
        (if u ∈ fillerNeighbors (F c) then Q.card * K else 0) + K := by
    by_cases hu : u ∈ fillerNeighbors (F c)
    · simp only [hu, ↓reduceIte]
      exact ((Finset.card_filter_le _ _).trans (supports_count d hd F Q c hc)).trans (Nat.le_add_right _ _)
    · simpa only [hu, ↓reduceIte, zero_add] using nonanchor_supports_count d hd F Q c hc u hu
  have hsum : (∑ c ∈ openCenters F Q,
      if u ∈ fillerNeighbors (F c) then Q.card * K else 0) =
        ((openCenters F Q).filter (fun c => u ∈ fillerNeighbors (F c))).card * (Q.card * K) := by
    rw [← Finset.sum_filter]
    simp
  calc
    _ ≤ _ := Finset.card_le_card hs
    _ ≤ ∑ c ∈ openCenters F Q,
        (((supportsAt d F Q c).filter (fun H => u ∈ H.val)).image (fun H => (c, H))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ c ∈ openCenters F Q,
        ((if u ∈ fillerNeighbors (F c) then Q.card * K else 0) + K) :=
      Finset.sum_le_sum fun c hc => Finset.card_image_le.trans (hp c hc)
    _ = ((openCenters F Q).filter (fun c => u ∈ fillerNeighbors (F c))).card * (Q.card * K) +
        (openCenters F Q).card * K := by
      rw [Finset.sum_add_distrib, hsum]
      simp
    _ ≤ FillerSparsity.degree F u * (Q.card * K) + (openCenters F Q).card * K :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ (anchor_count_le_degree F Q u)) _
    _ = _ := by rw [open_card]; ring

noncomputable def candidateRate (d : ℕ) (H0 R M : ℝ) : ℝ :=
  H0 * M ^ d / ((d : ℝ) * R * beta S * (Fintype.card S).choose d)

noncomputable def tripleConstant (d : ℕ) (H0 M : ℝ) : ℝ :=
  36 * H0 * M ^ d * d.choose 3 / d

theorem candidateRate_nonneg (d : ℕ) {H0 R M : ℝ}
    (hH0 : 0 ≤ H0) (hR : 0 ≤ R) (hM : 0 ≤ M) :
    0 ≤ candidateRate (S := S) d H0 R M := by
  unfold candidateRate beta
  positivity

theorem triple_mass_le (d : ℕ) (hd : 3 ≤ d) (hm : d ≤ Fintype.card S)
    {H0 R M : ℝ} (hH0 : 0 ≤ H0) (hR : 0 < R) (hM : 0 ≤ M) :
    candidateRate (S := S) d H0 R M * (Fintype.card S - 3).choose (d - 3) ≤
      tripleConstant d H0 M / (R * Fintype.card S) := by
  have hm₃ : (3 : ℝ) ≤ Fintype.card S := by exact_mod_cast hd.trans hm
  have hm₀ : (0 : ℝ) < Fintype.card S := by linarith
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc₂ : (0 : ℝ) < (Fintype.card S).choose 2 := by
    exact_mod_cast Nat.choose_pos (show 2 ≤ Fintype.card S by omega)
  have hcd : (0 : ℝ) < (Fintype.card S).choose d := by exact_mod_cast Nat.choose_pos hm
  have hid :
      ((Fintype.card S).choose d : ℝ) * (d.choose 3 : ℝ) =
        ((Fintype.card S).choose 3 : ℝ) *
          ((Fintype.card S - 3).choose (d - 3) : ℝ) := by
    exact_mod_cast (Nat.choose_mul (n := Fintype.card S) hd)
  have hrec :
      ((Fintype.card S).choose 3 : ℝ) * 3 =
        ((Fintype.card S).choose 2 : ℝ) * ((Fintype.card S : ℝ) - 2) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq (Fintype.card S) 2)
    simpa only [show (2 + 1 : ℕ) = 3 from rfl, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_sub (show 2 ≤ Fintype.card S by omega)] using h
  have hratio : ((Fintype.card S).choose 2 : ℝ) * Fintype.card S ≤
      9 * ((Fintype.card S).choose 3 : ℝ) := by
    nlinarith [mul_nonneg hc₂.le (show 0 ≤ (Fintype.card S : ℝ) - 3 by linarith)]
  have hprod :
      ((Fintype.card S).choose 2 : ℝ) *
          ((Fintype.card S - 3).choose (d - 3) : ℝ) * Fintype.card S ≤
        9 * ((Fintype.card S).choose d : ℝ) * (d.choose 3 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hratio
      (show (0 : ℝ) ≤ (Fintype.card S - 3).choose (d - 3) by positivity)
    nlinarith
  unfold candidateRate beta tripleConstant
  field_simp
  have h := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 4 * H0 * M ^ d by positivity)
  nlinarith

noncomputable def openedBudget (R : ℝ) : ℝ :=
  4 * Real.exp 1 * R ^ 3 / Fintype.card S + 8 * R * Real.log (Fintype.card S)

theorem opened_le (F : C → Filler S) (R : ℝ) (hR : 0 ≤ R)
    (hm : 1 ≤ Fintype.card S) (hF : FillerSparsity.Good R F)
    (Q : Finset S) (hQ : (Q.card : ℝ) ≤ 2 * R) :
    (FillerSparsity.edgeCount F Q : ℝ) ≤ openedBudget (S := S) R := by
  have hm₀ : (0 : ℝ) < Fintype.card S := by exact_mod_cast (show 0 < Fintype.card S by omega)
  have hlog : 0 ≤ Real.log (Fintype.card S) := Real.log_nonneg (by exact_mod_cast hm)
  have hsq := pow_le_pow_left₀ (show (0 : ℝ) ≤ Q.card by positivity) hQ 2
  have hquad := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hR) hm₀.le) (Real.exp_pos 1).le
  have hlinear := mul_le_mul_of_nonneg_right hQ (show 0 ≤ 4 * Real.log (Fintype.card S) by positivity)
  calc
    _ ≤ Real.exp 1 * (R * (Q.card : ℝ) ^ 2 / Fintype.card S) +
        4 * Q.card * Real.log (Fintype.card S) := hF.2 Q
    _ ≤ 4 * Real.exp 1 * R ^ 3 / Fintype.card S + 8 * R * Real.log (Fintype.card S) := by
      apply add_le_add
      · convert hquad using 1
        ring
      · nlinarith
    _ = _ := rfl

theorem openedBudget_le (R : ℝ) (hR : 0 ≤ R)
    (hm : 0 < (Fintype.card S : ℝ)) (hRm : R ≤ Fintype.card S)
    (hlog : Real.log (Fintype.card S) ≤ R) :
    openedBudget (S := S) R ≤ (4 * Real.exp 1 + 8) * R ^ 2 := by
  have hfrac : R ^ 3 / Fintype.card S ≤ R ^ 2 := by
    rw [div_le_iff₀ hm]
    nlinarith [mul_le_mul_of_nonneg_right hRm (sq_nonneg R)]
  have hfirst := mul_le_mul_of_nonneg_left hfrac (show 0 ≤ 4 * Real.exp 1 by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 8 * R by positivity)
  calc
    _ = 4 * Real.exp 1 * (R ^ 3 / Fintype.card S) + 8 * R * Real.log (Fintype.card S) := by
      unfold openedBudget
      ring
    _ ≤ 4 * Real.exp 1 * R ^ 2 + 8 * R * R := add_le_add hfirst hsecond
    _ = _ := by ring

noncomputable def totalMass (d : ℕ) (H0 R M : ℝ) (F : C → Filler S) (Q : Finset S) : ℝ :=
  candidateRate (S := S) d H0 R M * (region d F Q).card

noncomputable def vertexMass (d : ℕ) (H0 R M : ℝ) (F : C → Filler S) (Q : Finset S) (u : S) : ℝ :=
  candidateRate (S := S) d H0 R M * ((region d F Q).filter (fun x => u ∈ x.2.val)).card

theorem total_mass_le (d : ℕ) (hd : 3 ≤ d) (hm : d ≤ Fintype.card S)
    {H0 R M : ℝ} (hH0 : 0 ≤ H0) (hR : 0 < R) (hM : 0 ≤ M)
    (F : C → Filler S) (hF : FillerSparsity.Good R F)
    (Q : Finset S) (hQ : (Q.card : ℝ) ≤ 2 * R) :
    totalMass d H0 R M F Q ≤ 2 * tripleConstant d H0 M * openedBudget (S := S) R / Fintype.card S := by
  have hm₀ : (0 : ℝ) < Fintype.card S := by exact_mod_cast (show 0 < Fintype.card S by omega)
  have hR₀ : R ≠ 0 := hR.ne'
  have hc := triple_mass_le d hd hm hH0 hR hM
  have hRate := candidateRate_nonneg (S := S) d hH0 hR.le hM
  have hB := opened_le F R hR.le (by omega) hF Q hQ
  have hB₀ : 0 ≤ openedBudget (S := S) R := (Nat.cast_nonneg _).trans hB
  have hcard : ((region d F Q).card : ℝ) ≤
      (FillerSparsity.edgeCount F Q : ℝ) * Q.card *
        (Fintype.card S - 3).choose (d - 3) := by
    exact_mod_cast region_card d hd F Q
  have hproduct : (FillerSparsity.edgeCount F Q : ℝ) * Q.card ≤
      openedBudget (S := S) R * (2 * R) :=
    mul_le_mul hB hQ (Nat.cast_nonneg _) hB₀
  calc
    _ ≤ candidateRate (S := S) d H0 R M *
        ((FillerSparsity.edgeCount F Q : ℝ) * Q.card *
          (Fintype.card S - 3).choose (d - 3)) := mul_le_mul_of_nonneg_left hcard hRate
    _ = ((FillerSparsity.edgeCount F Q : ℝ) * Q.card) *
        (candidateRate (S := S) d H0 R M * (Fintype.card S - 3).choose (d - 3)) := by ring
    _ ≤ ((FillerSparsity.edgeCount F Q : ℝ) * Q.card) *
        (tripleConstant d H0 M / (R * Fintype.card S)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ (openedBudget (S := S) R * (2 * R)) *
        (tripleConstant d H0 M / (R * Fintype.card S)) := by
      apply mul_le_mul_of_nonneg_right hproduct
      unfold tripleConstant
      positivity
    _ = _ := by field_simp

theorem vertex_mass_le (d : ℕ) (hd : 3 ≤ d) (hm : d ≤ Fintype.card S)
    {H0 R M : ℝ} (hH0 : 0 ≤ H0) (hR : 0 < R) (hM : 0 ≤ M)
    (hRm : R ≤ Fintype.card S) (hlog : Real.log (Fintype.card S) ≤ R)
    (F : C → Filler S) (hF : FillerSparsity.Good R F)
    (Q : Finset S) (hQ : (Q.card : ℝ) ≤ 2 * R) (u : S) :
    vertexMass d H0 R M F Q u ≤
      tripleConstant d H0 M * (5 * Real.exp 1 + 16) * R / Fintype.card S := by
  have hm₀ : (0 : ℝ) < Fintype.card S := by exact_mod_cast (show 0 < Fintype.card S by omega)
  have hR₀ : R ≠ 0 := hR.ne'
  have hc := triple_mass_le d hd hm hH0 hR hM
  have hRate := candidateRate_nonneg (S := S) d hH0 hR.le hM
  have hB := (opened_le F R hR.le (by omega) hF Q hQ).trans
    (openedBudget_le R hR.le hm₀ hRm hlog)
  have hdegree : (FillerSparsity.degree F u : ℝ) ≤ (Real.exp 1 / 2 + 4) * R := by
    have h := hF.1 u
    nlinarith
  have hdegree₀ : 0 ≤ (Real.exp 1 / 2 + 4) * R :=
    (Nat.cast_nonneg _).trans hdegree
  have hmul := mul_le_mul hdegree hQ (Nat.cast_nonneg _) hdegree₀
  have hA : (FillerSparsity.degree F u : ℝ) * Q.card + FillerSparsity.edgeCount F Q ≤
      (5 * Real.exp 1 + 16) * R ^ 2 := by nlinarith
  have hcard : (((region d F Q).filter (fun x => u ∈ x.2.val)).card : ℝ) ≤
      ((FillerSparsity.degree F u : ℝ) * Q.card + FillerSparsity.edgeCount F Q) *
        (Fintype.card S - 3).choose (d - 3) := by
    exact_mod_cast region_vertex_card d hd F Q u
  calc
    _ ≤ candidateRate (S := S) d H0 R M *
        (((FillerSparsity.degree F u : ℝ) * Q.card + FillerSparsity.edgeCount F Q) *
          (Fintype.card S - 3).choose (d - 3)) := mul_le_mul_of_nonneg_left hcard hRate
    _ = ((FillerSparsity.degree F u : ℝ) * Q.card + FillerSparsity.edgeCount F Q) *
        (candidateRate (S := S) d H0 R M * (Fintype.card S - 3).choose (d - 3)) := by ring
    _ ≤ ((FillerSparsity.degree F u : ℝ) * Q.card + FillerSparsity.edgeCount F Q) *
        (tripleConstant d H0 M / (R * Fintype.card S)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ ((5 * Real.exp 1 + 16) * R ^ 2) *
        (tripleConstant d H0 M / (R * Fintype.card S)) := by
      apply mul_le_mul_of_nonneg_right hA
      unfold tripleConstant
      positivity
    _ = _ := by field_simp

theorem opened_error (R : ℝ) (hR : R ≠ 0) :
    openedBudget (S := S) R / R ^ 2 =
      4 * Real.exp 1 * R / Fintype.card S + 8 * Real.log (Fintype.card S) / R := by
  unfold openedBudget
  field_simp

end VisibleMass

end SteinerLowerBound
