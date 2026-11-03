module

public import SteinerLowerBound.FiniteProbability
public import SteinerLowerBound.Metric

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace HardDistribution

abbrev Subsets (S : Type*) (d : ℕ) := {H : Finset S // H.card = d}

variable {S : Type*} [Fintype S]

noncomputable def starMass (d : ℕ) (H₀ R : ℝ) (W : S → ℝ) (H : Subsets S d) : ℝ :=
  H₀ / ((d : ℝ) * R * (Fintype.card S).choose d) * ∏ u ∈ H.val, W u

noncomputable def starTotal (d : ℕ) (H₀ R : ℝ) (W : S → ℝ) : ℝ :=
  ∑ H : Subsets S d, starMass d H₀ R W H

theorem starMass_nonneg (d : ℕ) {H₀ R : ℝ} (hH₀ : 0 ≤ H₀) (hR : 0 ≤ R)
    {W : S → ℝ} (hW : ∀ u, 0 ≤ W u) (H : Subsets S d) :
    0 ≤ starMass d H₀ R W H := by
  unfold starMass
  exact mul_nonneg (div_nonneg hH₀ (by positivity))
    (Finset.prod_nonneg fun u _ => hW u)

theorem starMass_le (d : ℕ) {H₀ R M : ℝ} (hH₀ : 0 ≤ H₀) (hR : 0 ≤ R)
    {W : S → ℝ} (hW₀ : ∀ u, 0 ≤ W u) (hWM : ∀ u, W u ≤ M) (H : Subsets S d) :
    starMass d H₀ R W H ≤
      H₀ / ((d : ℝ) * R * (Fintype.card S).choose d) * M ^ d := by
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hH₀ (by positivity))
  calc
    (∏ u ∈ H.val, W u) ≤ ∏ _u ∈ H.val, M :=
      Finset.prod_le_prod₀ (fun u _ => hW₀ u) (fun u _ => hWM u)
    _ = _ := by simp [H.property]

theorem starTotal_le (d : ℕ) (hd : d ≤ Fintype.card S)
    {H₀ R M : ℝ} (hH₀ : 0 ≤ H₀) (hR : 0 < R)
    {W : S → ℝ} (hW₀ : ∀ u, 0 ≤ W u) (hWM : ∀ u, W u ≤ M) :
    starTotal d H₀ R W ≤ H₀ * M ^ d / ((d : ℝ) * R) := by
  have hc : ((Fintype.card S).choose d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hd).ne'
  calc
    _ ≤ ∑ _H : Subsets S d,
        H₀ / ((d : ℝ) * R * (Fintype.card S).choose d) * M ^ d :=
      Finset.sum_le_sum fun H _ => starMass_le d hH₀ hR.le hW₀ hWM H
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, nsmul_eq_mul]
      field_simp

theorem prescribed_count (d : ℕ) (P : Finset S) (hP : P.card ≤ d) :
    (Finset.univ.filter (fun H : Subsets S d => P ⊆ H.val)).card =
      ((Fintype.card S) - P.card).choose (d - P.card) := by
  classical
  let e : {H : Subsets S d // P ⊆ H.val} ≃
      {H // H ∈ ((Finset.univ : Finset S).powersetCard d).filter (P ⊆ ·)} :=
    { toFun := fun H => ⟨H.val.val, by simp [H.val.property, H.property]⟩
      invFun := fun H => ⟨⟨H.val,
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp H.property).1).2⟩,
        (Finset.mem_filter.mp H.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = Fintype.card {H : Subsets S d // P ⊆ H.val} := (Fintype.card_subtype _).symm
    _ = _ := Fintype.card_congr e
    _ = _ := by
      simp only [Fintype.card_coe]
      rw [Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _) hP,
        Finset.card_univ]

theorem prescribed_mass_le (d : ℕ) (P : Finset S) (hP : P.card ≤ d)
    {H₀ R M : ℝ} (hH₀ : 0 ≤ H₀) (hR : 0 ≤ R)
    {W : S → ℝ} (hW₀ : ∀ u, 0 ≤ W u) (hWM : ∀ u, W u ≤ M) :
    (∑ H : Subsets S d, if P ⊆ H.val then starMass d H₀ R W H else 0) ≤
      (((Fintype.card S - P.card).choose (d - P.card) : ℕ) : ℝ) *
        (H₀ / ((d : ℝ) * R * (Fintype.card S).choose d) * M ^ d) := by
  classical
  calc
    _ ≤ ∑ H : Subsets S d, if P ⊆ H.val then
        H₀ / ((d : ℝ) * R * (Fintype.card S).choose d) * M ^ d else 0 := by
      apply Finset.sum_le_sum
      intro H _
      split_ifs
      · exact starMass_le d hH₀ hR hW₀ hWM H
      · rfl
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, prescribed_count d P hP]

abbrev Filler (S : Type*) := Unit ⊕ S ⊕ Subsets S 2
abbrev State (S : Type*) (d : ℕ) := Unit ⊕ S ⊕ Subsets S 2 ⊕ Subsets S d

noncomputable def beta (S : Type*) [Fintype S] : ℝ :=
  1 / (4 * (Fintype.card S).choose 2)

theorem beta_pos (hm : 2 ≤ Fintype.card S) : 0 < beta S := by
  unfold beta
  have : (0 : ℝ) < (Fintype.card S).choose 2 := by exact_mod_cast Nat.choose_pos hm
  positivity

noncomputable def anchorConstant (d : ℕ) (H₀ M : ℝ) : ℝ :=
  4 * H₀ * M ^ d * (d.choose 2) / d

theorem anchor_mass_le (d : ℕ) (hd₂ : 2 ≤ d) (hdm : d ≤ Fintype.card S)
    (e : Subsets S 2) {H₀ R M : ℝ} (hH₀ : 0 ≤ H₀) (hR : 0 < R)
    {W : S → ℝ} (hW₀ : ∀ u, 0 ≤ W u) (hWM : ∀ u, W u ≤ M) :
    (∑ H : Subsets S d, if e.val ⊆ H.val then starMass d H₀ R W H / beta S else 0) ≤
      anchorConstant d H₀ M / R := by
  classical
  have hm₂ := hd₂.trans hdm
  have hc : ((Fintype.card S).choose d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hdm).ne'
  have hc₂ : ((Fintype.card S).choose 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hm₂).ne'
  have hd₀ : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hid :
      ((Fintype.card S).choose d : ℝ) * (d.choose 2 : ℝ) =
        ((Fintype.card S).choose 2 : ℝ) *
          ((Fintype.card S - 2).choose (d - 2) : ℝ) := by
    exact_mod_cast (Nat.choose_mul (n := Fintype.card S) hd₂)
  calc
    _ = (∑ H : Subsets S d, if e.val ⊆ H.val then starMass d H₀ R W H else 0) / beta S := by
      simp [Finset.sum_div, ite_div]
    _ ≤ ((((Fintype.card S - 2).choose (d - 2) : ℕ) : ℝ) *
        (H₀ / ((d : ℝ) * R * (Fintype.card S).choose d) * M ^ d)) / beta S := by
      apply div_le_div_of_nonneg_right _ (beta_pos hm₂).le
      simpa only [e.property] using prescribed_mass_le d e.val (by simpa [e.property])
        hH₀ hR.le hW₀ hWM
    _ = _ := by
      unfold beta anchorConstant
      field_simp
      nlinarith [congrArg (fun z : ℝ => H₀ * M ^ d * z) hid]

noncomputable def potentialLaw (d : ℕ) (H₀ R : ℝ) (W : S → ℝ)
    (e : Subsets S 2) (hd₂ : 2 ≤ d) (hdm : d ≤ Fintype.card S)
    (hH₀ : 0 ≤ H₀) (hR : 0 < R) (hW₀ : ∀ u, 0 ≤ W u)
    (M : ℝ) (hWM : ∀ u, W u ≤ M) (hsmall : anchorConstant d H₀ M / R ≤ 1) :
    Law (Option (Subsets S d)) :=
  Law.withNone
    (fun H => if e.val ⊆ H.val then starMass d H₀ R W H / beta S else 0)
    (fun H => by
      split_ifs
      · exact div_nonneg (starMass_nonneg d hH₀ hR.le hW₀ H) (beta_pos (hd₂.trans hdm)).le
      · rfl)
    ((anchor_mass_le d hd₂ hdm e hH₀ hR hW₀ hWM).trans hsmall)

noncomputable def fillerLaw (hm : 2 ≤ Fintype.card S) : Law (Filler S) where
  mass
    | .inl _ => 1 / 2
    | .inr (.inl _) => 1 / (4 * Fintype.card S)
    | .inr (.inr _) => beta S
  nonneg x := by cases x with
    | inl => norm_num
    | inr x => cases x <;> simp only [beta] <;> positivity
  total := by
    have hm₀ : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card S ≠ 0)
    have hc : ((Fintype.card S).choose 2 : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hm).ne'
    simp only [Fintype.sum_sum_type, Finset.sum_const, Fintype.card_unique,
      Nat.cast_one, one_mul, Finset.card_univ, Fintype.card_finset_len, nsmul_eq_mul, beta]
    field_simp
    ring

noncomputable def staticLaw (d : ℕ) (H₀ R : ℝ) (W : S → ℝ)
    (hm : 2 ≤ Fintype.card S) (hH₀ : 0 ≤ H₀) (hR : 0 ≤ R)
    (hW : ∀ u, 0 ≤ W u) (hstar : starTotal d H₀ R W ≤ 1 / 2) :
    Law (State S d) where
  mass
    | .inl _ => 1 / 2 - starTotal d H₀ R W
    | .inr (.inl _) => 1 / (4 * Fintype.card S)
    | .inr (.inr (.inl _)) => beta S
    | .inr (.inr (.inr H)) => starMass d H₀ R W H
  nonneg x := by
    rcases x with (_ | u | e | H)
    · linarith
    · positivity
    · unfold beta; positivity
    · exact starMass_nonneg d hH₀ hR hW H
  total := by
    have hm₀ : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card S ≠ 0)
    have hc : ((Fintype.card S).choose 2 : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hm).ne'
    simp only [Fintype.sum_sum_type, Finset.sum_const, Fintype.card_unique,
      Nat.cast_one, one_mul, Finset.card_univ, Fintype.card_finset_len, nsmul_eq_mul, beta, starTotal]
    field_simp
    ring

def fillerNeighbors : Filler S → Finset S
  | .inl _ => ∅
  | .inr (.inl u) => {u}
  | .inr (.inr H) => H.val

def neighbors (d : ℕ) : State S d → Finset S
  | .inl _ => ∅
  | .inr (.inl u) => {u}
  | .inr (.inr (.inl H)) => H.val
  | .inr (.inr (.inr H)) => H.val

omit [Fintype S] in
theorem filler_card_le_two (f : Filler S) : (fillerNeighbors f).card ≤ 2 := by
  rcases f with (_ | u | H)
  · simp [fillerNeighbors]
  · simp [fillerNeighbors]
  · simp [fillerNeighbors, H.property]

theorem static_weights_independent_singleton (d : ℕ) (H₀ R : ℝ) (W : S → ℝ)
    (hm : 2 ≤ Fintype.card S) (hH₀ : 0 ≤ H₀) (hR : 0 ≤ R)
    (hW : ∀ u, 0 ≤ W u) (hstar : starTotal d H₀ R W ≤ 1 / 2) (u : S) :
    (staticLaw d H₀ R W hm hH₀ hR hW hstar).mass (.inr (.inl u)) =
      1 / (4 * Fintype.card S) := rfl

theorem static_weights_independent_pair (d : ℕ) (H₀ R : ℝ) (W : S → ℝ)
    (hm : 2 ≤ Fintype.card S) (hH₀ : 0 ≤ H₀) (hR : 0 ≤ R)
    (hW : ∀ u, 0 ≤ W u) (hstar : starTotal d H₀ R W ≤ 1 / 2) (e : Subsets S 2) :
    (staticLaw d H₀ R W hm hH₀ hR hW hstar).mass (.inr (.inr (.inl e))) = beta S := rfl

end HardDistribution

end SteinerLowerBound
