module

public import SteinerLowerBound.Distributions
public import SteinerLowerBound.IndependentTrials

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace FillerSparsity

open HardDistribution

variable {S C : Type*} [Fintype S] [Fintype C]

def isPair : Filler S → Bool
  | .inr (.inr _) => true
  | _ => false

def inside (Q : Finset S) (f : Filler S) : Prop :=
  isPair f = true ∧ fillerNeighbors f ⊆ Q

def contains (u : S) (f : Filler S) : Prop :=
  isPair f = true ∧ u ∈ fillerNeighbors f

noncomputable def edgeCount (F : C → Filler S) (Q : Finset S) : ℕ :=
  IndependentTrials.count (fun _ : C => inside Q) F

noncomputable def degree (F : C → Filler S) (u : S) : ℕ :=
  IndependentTrials.count (fun _ : C => contains u) F

theorem contained_pair_count (Q : Finset S) :
    (Finset.univ.filter (fun H : Subsets S 2 => H.val ⊆ Q)).card = Q.card.choose 2 := by
  classical
  let e : {H : Subsets S 2 // H.val ⊆ Q} ≃ {H // H ∈ Q.powersetCard 2} :=
    { toFun := fun H => ⟨H.val.val, Finset.mem_powersetCard.mpr ⟨H.property, H.val.property⟩⟩
      invFun := fun H => ⟨⟨H.val, (Finset.mem_powersetCard.mp H.property).2⟩,
        (Finset.mem_powersetCard.mp H.property).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = Fintype.card {H : Subsets S 2 // H.val ⊆ Q} := (Fintype.card_subtype _).symm
    _ = _ := Fintype.card_congr e
    _ = _ := by simp only [Fintype.card_coe, Finset.card_powersetCard]

theorem prob_inside (hm : 2 ≤ Fintype.card S) (Q : Finset S) :
    (fillerLaw hm).prob {f | inside Q f} = (Q.card.choose 2 : ℝ) * beta S := by
  classical
  simp only [Law.prob, Set.mem_ofPred_eq, Fintype.sum_sum_type, fillerLaw, inside, isPair,
    Bool.false_eq_true, false_and, ↓reduceIte, Finset.sum_const_zero, zero_add,
    fillerNeighbors, true_and]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, contained_pair_count]

theorem prob_contains (hm : 2 ≤ Fintype.card S) (u : S) :
    (fillerLaw hm).prob {f | contains u f} = ((Fintype.card S - 1 : ℕ) : ℝ) * beta S := by
  classical
  simp only [Law.prob, Set.mem_ofPred_eq, Fintype.sum_sum_type, fillerLaw, contains, isPair,
    Bool.false_eq_true, false_and, ↓reduceIte, Finset.sum_const_zero, zero_add,
    fillerNeighbors, true_and]
  rw [← Finset.sum_filter]
  have hc : (Finset.univ.filter (fun H : Subsets S 2 => u ∈ H.val)).card =
      Fintype.card S - 1 := by
    simpa using prescribed_count 2 {u} (by simp)
  simp only [Finset.sum_const, nsmul_eq_mul, hc]

theorem edge_mean_le (hm : 2 ≤ Fintype.card S) (R : ℝ) (hR : 0 ≤ R)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * R) (Q : Finset S) :
    IndependentTrials.mean (fun _ : C => fillerLaw hm) (fun _ : C => inside Q) ≤
      R * (Q.card : ℝ) ^ 2 / Fintype.card S := by
  have hm' : (2 : ℝ) ≤ Fintype.card S := by exact_mod_cast hm
  have hm₀ : (0 : ℝ) < Fintype.card S := by linarith
  have hm₁ : (0 : ℝ) < (Fintype.card S : ℝ) - 1 := by linarith
  have hQ : (0 : ℝ) ≤ Q.card := Nat.cast_nonneg _
  simp only [IndependentTrials.mean, prob_inside, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, beta]
  rw [hC, Nat.cast_choose_two, Nat.cast_choose_two]
  field_simp
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (Fintype.card S : ℝ) - 2 by linarith)
    (sq_nonneg (Q.card : ℝ))]

theorem degree_mean (hm : 2 ≤ Fintype.card S) (R : ℝ)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * R) (u : S) :
    IndependentTrials.mean (fun _ : C => fillerLaw hm) (fun _ : C => contains u) = R / 2 := by
  have hm' : (2 : ℝ) ≤ Fintype.card S := by exact_mod_cast hm
  have hm₀ : (Fintype.card S : ℝ) ≠ 0 := by linarith
  have hm₁ : (Fintype.card S : ℝ) - 1 ≠ 0 := by linarith
  simp only [IndependentTrials.mean, prob_contains, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, beta]
  rw [hC, Nat.cast_sub (by omega : 1 ≤ Fintype.card S), Nat.cast_one, Nat.cast_choose_two]
  field_simp
  ring

theorem edge_tail (hm : 2 ≤ Fintype.card S) (R : ℝ) (hR : 0 ≤ R)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * R) (Q : Finset S) :
    (Law.pi (fun _ : C => fillerLaw hm)).prob {F |
      Real.exp 1 * (R * (Q.card : ℝ) ^ 2 / Fintype.card S) +
        4 * Q.card * Real.log (Fintype.card S) ≤ (edgeCount F Q : ℝ)} ≤
      Real.exp (-(4 * Q.card * Real.log (Fintype.card S))) :=
  IndependentTrials.tail_mean_bound _ _ _ _ (edge_mean_le hm R hR hC Q)

theorem degree_tail (hm : 2 ≤ Fintype.card S) (R : ℝ)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * R) (u : S) :
    (Law.pi (fun _ : C => fillerLaw hm)).prob {F |
      Real.exp 1 * (R / 2) + 4 * Real.log (Fintype.card S) ≤ (degree F u : ℝ)} ≤
        Real.exp (-(4 * Real.log (Fintype.card S))) := by
  apply IndependentTrials.tail_mean_bound
  exact (degree_mean hm R hC u).le

theorem geometric_positive_le {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) (n : ℕ) :
    (∑ j ∈ Finset.range n, q ^ (j + 1)) ≤ q / (1 - q) := by
  have hs : (∑ j ∈ Finset.range n, q ^ (j + 1)) =
      q * ∑ j ∈ Finset.range n, q ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring
  rw [hs, le_div_iff₀ (sub_pos.mpr hq₁)]
  have hg := congrArg (fun z : ℝ => q * z) (geom_sum_mul_neg q n)
  nlinarith [mul_nonneg hq₀ (pow_nonneg hq₀ n)]

theorem nonempty_subset_sum (a : ℝ) (ha : 0 ≤ a)
    (hq : (Fintype.card S : ℝ) * a < 1) :
    (∑ Q : Finset S, if Q = ∅ then 0 else a ^ Q.card) ≤
      ((Fintype.card S : ℝ) * a) / (1 - (Fintype.card S : ℝ) * a) := by
  classical
  have he : (Finset.univ : Finset (Finset S)) = (Finset.univ : Finset S).powerset := by
    ext Q
    simp
  have hfun (Q : Finset S) :
      (if Q = ∅ then 0 else a ^ Q.card) = if Q.card = 0 then 0 else a ^ Q.card := by
    simp
  simp_rw [hfun]
  rw [he, Finset.sum_powerset_apply_card (fun n => if n = 0 then (0 : ℝ) else a ^ n)]
  simp only [Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, ↓reduceIte, mul_zero, add_zero]
  calc
    _ ≤ ∑ j ∈ Finset.range (Fintype.card S), ((Fintype.card S : ℝ) * a) ^ (j + 1) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
      have hb : ((Fintype.card S).choose (j + 1) : ℝ) ≤
          (Fintype.card S : ℝ) ^ (j + 1) := by
        exact_mod_cast Nat.choose_le_pow (Fintype.card S) (j + 1)
      simpa only [mul_pow] using mul_le_mul_of_nonneg_right hb (pow_nonneg ha (j + 1))
    _ ≤ _ := geometric_positive_le (mul_nonneg (Nat.cast_nonneg _) ha) hq _

def Good (R : ℝ) (F : C → Filler S) : Prop :=
  (∀ u, (degree F u : ℝ) ≤ Real.exp 1 * (R / 2) + 4 * Real.log (Fintype.card S)) ∧
    ∀ Q : Finset S, (edgeCount F Q : ℝ) ≤
      Real.exp 1 * (R * (Q.card : ℝ) ^ 2 / Fintype.card S) +
        4 * Q.card * Real.log (Fintype.card S)

omit [Fintype S] in
theorem pair_card (f : Filler S) (hf : isPair f = true) : (fillerNeighbors f).card = 2 := by
  rcases f with (_ | u | H)
  · simp [isPair] at hf
  · simp [isPair] at hf
  · exact H.property

omit [Fintype S] in
theorem edgeCount_empty (F : C → Filler S) : edgeCount F ∅ = 0 := by
  have h (f : Filler S) : ¬inside ∅ f := by
    rintro ⟨hp, hs⟩
    have hc := pair_card f hp
    have he : fillerNeighbors f = ∅ := Finset.subset_empty.mp hs
    simp [he] at hc
  simp [edgeCount, IndependentTrials.count, h]

theorem good_probability (hm : 2 ≤ Fintype.card S) (R : ℝ) (hR : 0 ≤ R)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * R) :
    1 - 3 / (Fintype.card S : ℝ) ^ 3 ≤
      (Law.pi (fun _ : C => fillerLaw hm)).prob {F | Good R F} := by
  classical
  let μ := Law.pi (fun _ : C => fillerLaw hm)
  let m : ℝ := Fintype.card S
  have hm₂ : (2 : ℝ) ≤ m := by dsimp [m]; exact_mod_cast hm
  have hm₀ : 0 < m := by linarith
  let a := Real.exp (-(4 * Real.log m))
  let q := m * a
  have ha₀ : 0 ≤ a := (Real.exp_pos _).le
  have ha : a = 1 / m ^ 4 := by
    have hp : Real.exp (4 * Real.log m) = m ^ 4 := by
      simpa [Real.exp_log hm₀] using Real.exp_nat_mul (Real.log m) 4
    dsimp [a]
    rw [Real.exp_neg, hp]
    simp only [one_div]
  have hq : q = 1 / m ^ 3 := by
    dsimp [q]
    rw [ha]
    field_simp
  have hq₀ : 0 ≤ q := mul_nonneg hm₀.le ha₀
  have hq₂ : q ≤ 1 / 2 := by
    rw [hq, div_le_iff₀ (pow_pos hm₀ 3)]
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hm₂ 3
    norm_num at hp
    linarith
  have hq₁ : q < 1 := by linarith
  have hgeom : q / (1 - q) ≤ 2 * q := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - q)]
    nlinarith [mul_nonneg hq₀ (show 0 ≤ 1 - 2 * q by linarith)]
  have hd : μ.prob {F | ∃ u : S,
      Real.exp 1 * (R / 2) + 4 * Real.log m < (degree F u : ℝ)} ≤ q := by
    apply (Law.finite_union_bound μ _).trans
    calc
      _ ≤ ∑ _u : S, a := by
        apply Finset.sum_le_sum
        intro u _
        apply (μ.prob_mono ?_).trans (degree_tail hm R hC u)
        intro F hF
        simp only [Set.mem_ofPred_eq] at hF ⊢
        exact hF.le
      _ = q := by simp [q, m]
  have hepoint (Q : Finset S) :
      μ.prob {F | Q ≠ ∅ ∧
        Real.exp 1 * (R * (Q.card : ℝ) ^ 2 / m) + 4 * Q.card * Real.log m <
          (edgeCount F Q : ℝ)} ≤ if Q = ∅ then 0 else a ^ Q.card := by
    by_cases hQ : Q = ∅
    · simp [hQ]
    · simp only [hQ, ↓reduceIte]
      have htail := edge_tail hm R hR hC Q
      have hpow : Real.exp (-(4 * (Q.card : ℝ) * Real.log m)) = a ^ Q.card := by
        rw [show -(4 * (Q.card : ℝ) * Real.log m) =
          (Q.card : ℝ) * (-(4 * Real.log m)) by ring, Real.exp_nat_mul]
      rw [hpow] at htail
      apply (μ.prob_mono ?_).trans htail
      intro F hF
      simp only [Set.mem_ofPred_eq] at hF ⊢
      exact hF.2.le
  have he : μ.prob {F | ∃ Q : Finset S, Q ≠ ∅ ∧
      Real.exp 1 * (R * (Q.card : ℝ) ^ 2 / m) + 4 * Q.card * Real.log m <
        (edgeCount F Q : ℝ)} ≤ 2 * q := by
    exact ((Law.finite_union_bound μ _).trans
      (Finset.sum_le_sum (fun Q _ => hepoint Q))).trans
        ((nonempty_subset_sum a ha₀ hq₁).trans hgeom)
  have hbad : {F : C → Filler S | ¬Good R F} ⊆
      {F | ∃ u : S, Real.exp 1 * (R / 2) + 4 * Real.log m < (degree F u : ℝ)} ∪
      {F | ∃ Q : Finset S, Q ≠ ∅ ∧
        Real.exp 1 * (R * (Q.card : ℝ) ^ 2 / m) + 4 * Q.card * Real.log m <
          (edgeCount F Q : ℝ)} := by
    intro F hF
    by_cases hdeg : ∀ u, (degree F u : ℝ) ≤ Real.exp 1 * (R / 2) + 4 * Real.log m
    · right
      have hsets : ¬∀ Q : Finset S, (edgeCount F Q : ℝ) ≤
          Real.exp 1 * (R * (Q.card : ℝ) ^ 2 / m) + 4 * Q.card * Real.log m := by
        intro hs
        exact hF ⟨hdeg, hs⟩
      push Not at hsets
      obtain ⟨Q, hQ⟩ := hsets
      refine ⟨Q, ?_, hQ⟩
      intro hzero
      subst Q
      simp [edgeCount_empty] at hQ
    · left
      push Not at hdeg
      exact hdeg
  have hb : μ.prob {F | ¬Good R F} ≤ 3 * q :=
    ((μ.prob_mono hbad).trans (μ.prob_union_le _ _)).trans (by linarith [add_le_add hd he])
  have hcompl : μ.prob {F | ¬Good R F} = 1 - μ.prob {F | Good R F} :=
    μ.prob_compl {F | Good R F}
  rw [hq] at hb
  rw [hcompl] at hb
  change 1 - 3 / m ^ 3 ≤ μ.prob {F | Good R F}
  dsimp [m] at *
  simp only [div_eq_mul_inv, one_mul] at hb ⊢
  linarith

end FillerSparsity

end SteinerLowerBound
