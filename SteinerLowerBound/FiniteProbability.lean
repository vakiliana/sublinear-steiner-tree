module

public import Mathlib

@[expose] public section

/-!
# Finite probability

All random objects in the hard distribution, including bounded-query
transcripts, have finite sample spaces. Probabilities are real finite sums.
`Close` is the event characterization of an upper bound on total variation.
-/

namespace SteinerLowerBound

open scoped BigOperators Classical

structure Law (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

namespace Law

variable {Ω Γ Δ : Type*} [Fintype Ω] [Fintype Γ] [Fintype Δ]

def expect (μ : Law Ω) (f : Ω → ℝ) : ℝ := ∑ ω, μ.mass ω * f ω

noncomputable def prob (μ : Law Ω) (E : Set Ω) : ℝ := by
  classical
  exact ∑ ω, if ω ∈ E then μ.mass ω else 0

@[simp]
theorem prob_univ (μ : Law Ω) : μ.prob Set.univ = 1 := by
  simp [prob, μ.total]

@[simp]
theorem prob_empty (μ : Law Ω) : μ.prob ∅ = 0 := by
  simp [prob]

theorem prob_nonneg (μ : Law Ω) (E : Set Ω) : 0 ≤ μ.prob E := by
  classical
  exact Finset.sum_nonneg fun ω _ => by
    split_ifs <;> simp_all [nonneg]

theorem prob_mono (μ : Law Ω) {E F : Set Ω} (h : E ⊆ F) :
    μ.prob E ≤ μ.prob F := by
  classical
  unfold prob
  exact Finset.sum_le_sum fun ω _ => by
    split_ifs <;> simp_all [nonneg]
    exact False.elim (‹ω ∉ F› (h ‹ω ∈ E›))

theorem prob_le_one (μ : Law Ω) (E : Set Ω) : μ.prob E ≤ 1 := by
  simpa using μ.prob_mono (Set.subset_univ E)

theorem prob_compl (μ : Law Ω) (E : Set Ω) : μ.prob Eᶜ = 1 - μ.prob E := by
  classical
  have : μ.prob E + μ.prob Eᶜ = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib, ← μ.total]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : ω ∈ E <;> simp [h]
  linarith

theorem prob_union_le (μ : Law Ω) (E F : Set Ω) :
    μ.prob (E ∪ F) ≤ μ.prob E + μ.prob F := by
  classical
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hE : ω ∈ E <;> by_cases hF : ω ∈ F <;>
    simp [hE, hF, μ.nonneg ω]

@[simp]
theorem expect_const (μ : Law Ω) (a : ℝ) : μ.expect (fun _ => a) = a := by
  simp [expect, ← Finset.sum_mul, μ.total]

theorem expect_add (μ : Law Ω) (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω + g ω) = μ.expect f + μ.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (μ : Law Ω) (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω - g ω) = μ.expect f - μ.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul_const (μ : Law Ω) (f : Ω → ℝ) (a : ℝ) :
    μ.expect (fun ω => f ω * a) = μ.expect f * a := by
  simp [expect, mul_assoc, Finset.sum_mul]

theorem expect_const_mul (μ : Law Ω) (a : ℝ) (f : Ω → ℝ) :
    μ.expect (fun ω => a * f ω) = a * μ.expect f := by
  simpa only [mul_comm] using μ.expect_mul_const f a

theorem expect_mono (μ : Law Ω) {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    μ.expect f ≤ μ.expect g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω)

theorem expect_nonneg (μ : Law Ω) {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ μ.expect f := by
  simpa using μ.expect_mono h

theorem expect_mono_support (μ : Law Ω) {f g : Ω → ℝ}
    (h : ∀ ω, 0 < μ.mass ω → f ω ≤ g ω) : μ.expect f ≤ μ.expect g := by
  apply Finset.sum_le_sum
  intro ω _
  by_cases hω : 0 < μ.mass ω
  · exact mul_le_mul_of_nonneg_left (h ω hω) (μ.nonneg ω)
  · have hz : μ.mass ω = 0 := le_antisymm (le_of_not_gt hω) (μ.nonneg ω)
    simp [hz]

theorem prob_mono_support (μ : Law Ω) {E F : Set Ω}
    (h : ∀ ω, 0 < μ.mass ω → ω ∈ E → ω ∈ F) : μ.prob E ≤ μ.prob F := by
  classical
  unfold prob
  apply Finset.sum_le_sum
  intro ω _
  by_cases hω : 0 < μ.mass ω
  · by_cases hE : ω ∈ E
    · simp [hE, h ω hω hE]
    · by_cases hF : ω ∈ F <;> simp [hE, hF, μ.nonneg ω]
  · have hz : μ.mass ω = 0 := le_antisymm (le_of_not_gt hω) (μ.nonneg ω)
    simp [hz]

theorem markov_mul (μ : Law Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) (a : ℝ) :
    a * μ.prob {ω | a ≤ f ω} ≤ μ.expect f := by
  classical
  unfold prob expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : a ≤ f ω
  · simp only [Set.mem_ofPred_eq, h, ↓reduceIte]
    nlinarith [μ.nonneg ω]
  · simp only [Set.mem_ofPred_eq, h, ↓reduceIte, mul_zero]
    exact mul_nonneg (μ.nonneg ω) (hf ω)

theorem markov (μ : Law Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω)
    {a : ℝ} (ha : 0 < a) :
    μ.prob {ω | a ≤ f ω} ≤ μ.expect f / a := by
  rw [le_div_iff₀ ha]
  simpa [mul_comm] using μ.markov_mul hf a

theorem markov_gt (μ : Law Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω)
    {a : ℝ} (ha : 0 < a) :
    μ.prob {ω | a < f ω} ≤ μ.expect f / a := by
  have hs : {ω | a < f ω} ⊆ {ω | a ≤ f ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact le_of_lt hω
  exact (μ.prob_mono hs).trans (μ.markov hf ha)

noncomputable def map (μ : Law Ω) (f : Ω → Γ) : Law Γ := by
  classical
  exact
    { mass := fun γ => ∑ ω, if f ω = γ then μ.mass ω else 0
      nonneg := fun γ => Finset.sum_nonneg fun ω _ => by
        split_ifs <;> simp_all [nonneg]
      total := by
        rw [Finset.sum_comm]
        simpa using μ.total }

theorem prob_map (μ : Law Ω) (f : Ω → Γ) (E : Set Γ) :
    (μ.map f).prob E = μ.prob (f ⁻¹' E) := by
  classical
  simp only [prob, map]
  calc
    _ = ∑ γ, ∑ ω, if f ω = γ ∧ γ ∈ E then μ.mass ω else 0 := by
      apply Finset.sum_congr rfl
      intro γ _
      by_cases h : γ ∈ E <;> simp [h]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω _
      calc
        _ = ∑ γ, if f ω = γ then (if f ω ∈ E then μ.mass ω else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro γ _
          by_cases h : f ω = γ
          · subst γ
            simp
          · simp [h]
        _ = _ := by simp

theorem expect_map (μ : Law Ω) (f : Ω → Γ) (g : Γ → ℝ) :
    (μ.map f).expect g = μ.expect (fun ω => g (f ω)) := by
  classical
  simp only [expect, map, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    _ = ∑ γ, if f ω = γ then μ.mass ω * g (f ω) else 0 := by
      apply Finset.sum_congr rfl
      intro γ _
      by_cases h : f ω = γ
      · subst γ
        simp
      · simp [h]
    _ = _ := by simp

@[simp]
theorem mass_map_inl (μ : Law Ω) (ω : Ω) :
    (μ.map (Sum.inl : Ω → Ω ⊕ Γ)).mass (.inl ω) = μ.mass ω := by
  simp [map]

@[simp]
theorem mass_map_inr (μ : Law Γ) (γ : Γ) :
    (μ.map (Sum.inr : Γ → Ω ⊕ Γ)).mass (.inr γ) = μ.mass γ := by
  simp [map]

@[simp]
theorem mass_map_inl_inr (μ : Law Ω) (γ : Γ) :
    (μ.map (Sum.inl : Ω → Ω ⊕ Γ)).mass (.inr γ) = 0 := by
  simp [map]

@[simp]
theorem mass_map_inr_inl (μ : Law Γ) (ω : Ω) :
    (μ.map (Sum.inr : Γ → Ω ⊕ Γ)).mass (.inl ω) = 0 := by
  simp [map]

def Close (μ ν : Law Ω) (ε : ℝ) : Prop :=
  ∀ E : Set Ω, |μ.prob E - ν.prob E| ≤ ε

theorem close_refl (μ : Law Ω) : Close μ μ 0 := by
  intro E
  simp

theorem Close.symm {μ ν : Law Ω} {ε : ℝ} (h : Close μ ν ε) : Close ν μ ε := by
  intro E
  simpa [abs_sub_comm] using h E

theorem Close.mono {μ ν : Law Ω} {ε δ : ℝ} (h : Close μ ν ε) (hεδ : ε ≤ δ) :
    Close μ ν δ := fun E => (h E).trans hεδ

theorem Close.trans {μ ν ρ : Law Ω} {ε δ : ℝ}
    (h₁ : Close μ ν ε) (h₂ : Close ν ρ δ) : Close μ ρ (ε + δ) := by
  intro E
  calc
    |μ.prob E - ρ.prob E| ≤ |μ.prob E - ν.prob E| + |ν.prob E - ρ.prob E| :=
      abs_sub_le _ _ _
    _ ≤ ε + δ := add_le_add (h₁ E) (h₂ E)

theorem Close.map {μ ν : Law Ω} {ε : ℝ} (h : Close μ ν ε) (f : Ω → Γ) :
    Close (μ.map f) (ν.map f) ε := by
  intro E
  simpa only [prob_map] using h (f ⁻¹' E)

theorem close_one (μ ν : Law Ω) : Close μ ν 1 := by
  intro E
  rw [abs_le]
  constructor <;> linarith [μ.prob_nonneg E, ν.prob_nonneg E, μ.prob_le_one E, ν.prob_le_one E]

theorem abs_expect_le (μ : Law Ω) (f : Ω → ℝ) :
    |μ.expect f| ≤ μ.expect (fun ω => |f ω|) := by
  unfold expect
  calc
    _ ≤ ∑ ω, |μ.mass ω * f ω| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [abs_mul, abs_of_nonneg (μ.nonneg ω)]

theorem le_cam {μ ν : Law Ω} {ε : ℝ} (h : Close μ ν ε) (yes : Set Ω) :
    (μ.prob yes + ν.prob yesᶜ) / 2 ≤ (1 + ε) / 2 := by
  rw [prob_compl]
  have := (abs_le.mp (h yes)).2
  linarith

theorem close_maps (μ : Law Ω) (f g : Ω → Γ) :
    Close (μ.map f) (μ.map g) (μ.prob {ω | f ω ≠ g ω}) := by
  classical
  intro E
  rw [prob_map, prob_map]
  simp only [prob, Set.mem_preimage, Set.mem_ofPred_eq]
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro ω _
  by_cases hfg : f ω = g ω
  · simp [hfg]
  · by_cases hf : f ω ∈ E <;> by_cases hg : g ω ∈ E <;>
      simp [hfg, hf, hg, abs_of_nonneg (μ.nonneg ω), μ.nonneg ω]

noncomputable def iid (μ : Law Ω) (U : Type*) [Fintype U] : Law (U → Ω) where
  mass w := ∏ u, μ.mass (w u)
  nonneg w := Finset.prod_nonneg fun u _ => μ.nonneg (w u)
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp [μ.total]

theorem expect_iid_product (μ : Law Ω) {U : Type*} [Fintype U] (f : U → Ω → ℝ) :
    (μ.iid U).expect (fun w => ∏ u, f u (w u)) = ∏ u, μ.expect (f u) := by
  classical
  simp only [expect, iid]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun u ω => μ.mass ω * f u ω).symm

noncomputable def pi {U : Type*} [Fintype U] (μ : U → Law Ω) : Law (U → Ω) where
  mass w := ∏ u, (μ u).mass (w u)
  nonneg w := Finset.prod_nonneg fun u _ => (μ u).nonneg (w u)
  total := by
    rw [← Fintype.prod_sum]
    simp only [(μ _).total, Finset.prod_const_one]

noncomputable def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : Law Ω where
  mass _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

noncomputable def withNone (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (htotal : ∑ ω, p ω ≤ 1) : Law (Option Ω) where
  mass
    | none => 1 - ∑ ω, p ω
    | some ω => p ω
  nonneg
    | none => sub_nonneg.mpr htotal
    | some ω => hp ω
  total := by simp

noncomputable def pure (ω : Ω) : Law Ω where
  mass x := if x = ω then 1 else 0
  nonneg x := by split_ifs <;> norm_num
  total := by simp

noncomputable def bind (μ : Law Ω) (k : Ω → Law Γ) : Law Γ where
  mass γ := μ.expect (fun ω => (k ω).mass γ)
  nonneg γ := μ.expect_nonneg fun ω => (k ω).nonneg γ
  total := by
    simp only [expect]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (k _).total, mul_one]
    exact μ.total

theorem prob_bind (μ : Law Ω) (k : Ω → Law Γ) (E : Set Γ) :
    (μ.bind k).prob E = μ.expect (fun ω => (k ω).prob E) := by
  classical
  simp only [prob, bind, expect]
  calc
    _ = ∑ γ, ∑ ω, μ.mass ω * (if γ ∈ E then (k ω).mass γ else 0) := by
      apply Finset.sum_congr rfl
      intro γ _
      by_cases h : γ ∈ E <;> simp [h]
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]

theorem expect_bind (μ : Law Ω) (k : Ω → Law Γ) (f : Γ → ℝ) :
    (μ.bind k).expect f = μ.expect (fun ω => (k ω).expect f) := by
  simp only [expect, bind, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem prob_pure (ω : Ω) (E : Set Ω) :
    (pure ω).prob E = if ω ∈ E then 1 else 0 := by
  classical
  simp only [prob, pure]
  calc
    _ = ∑ x, if x = ω then (if ω ∈ E then (1 : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : x = ω <;> simp_all
    _ = _ := by simp

@[simp]
theorem expect_pure (ω : Ω) (f : Ω → ℝ) : (pure ω).expect f = f ω := by
  simp [expect, pure, ite_mul]

noncomputable def mix (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (μ ν : Law Ω) :
    Law Ω where
  mass ω := p * μ.mass ω + (1 - p) * ν.mass ω
  nonneg ω := add_nonneg (mul_nonneg hp₀ (μ.nonneg ω))
    (mul_nonneg (sub_nonneg.mpr hp₁) (ν.nonneg ω))
  total := by
    simp [Finset.sum_add_distrib, ← Finset.mul_sum, μ.total, ν.total]

theorem prob_mix (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (μ ν : Law Ω) (E : Set Ω) :
    (mix p hp₀ hp₁ μ ν).prob E = p * μ.prob E + (1 - p) * ν.prob E := by
  classical
  simp only [prob, mix, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ω ∈ E <;> simp [h]

theorem expect_mix (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (μ ν : Law Ω) (f : Ω → ℝ) :
    (mix p hp₀ hp₁ μ ν).expect f = p * μ.expect f + (1 - p) * ν.expect f := by
  simp only [mix, expect, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

theorem prob_inter_le (μ : Law Ω) (E F : Set Ω) :
    μ.prob (E ∩ F) ≤ μ.prob E :=
  μ.prob_mono Set.inter_subset_left

theorem prob_diff_le (μ : Law Ω) (E F : Set Ω) :
    μ.prob E - μ.prob F ≤ μ.prob (E \ F) := by
  have h := μ.prob_union_le F (E \ F)
  have h' := μ.prob_mono (show E ⊆ F ∪ (E \ F) by intro ω hω; by_cases hF : ω ∈ F <;> simp_all)
  linarith

theorem exchange (μ : Law Ω) (E P : Set Ω) (moves : Ω → Finset Ω)
    (F B : ℝ)
    (hF : ∀ ω ∈ E, F ≤ (moves ω).card)
    (hB : ∀ z, ((Finset.univ.filter fun ω => ω ∈ E ∧ z ∈ moves ω).card : ℝ) ≤ B)
    (hp : ∀ ω ∈ E, ∀ z ∈ moves ω, z ∈ P)
    (hm : ∀ ω ∈ E, ∀ z ∈ moves ω, μ.mass ω = μ.mass z) :
    F * μ.prob E ≤ B * μ.prob P := by
  classical
  have transport :
      (∑ ω, if ω ∈ E then ∑ z ∈ moves ω, μ.mass ω else 0) =
        ∑ z, if z ∈ P then
          μ.mass z * (Finset.univ.filter fun ω => ω ∈ E ∧ z ∈ moves ω).card else 0 := by
    calc
      _ = ∑ ω, ∑ z, if ω ∈ E ∧ z ∈ moves ω then μ.mass z else 0 := by
        apply Finset.sum_congr rfl
        intro ω _
        by_cases hω : ω ∈ E
        · simp only [hω, true_and, ↓reduceIte]
          rw [← Finset.sum_filter]
          have hfilter : Finset.univ.filter (fun z => z ∈ moves ω) = moves ω := by
            ext z
            simp
          rw [hfilter]
          exact Finset.sum_congr rfl (fun z hz => hm ω hω z hz)
        · simp [hω]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : z ∈ P
        · simp only [hz, ↓reduceIte]
          rw [← Finset.sum_filter]
          simp [mul_comm]
        · simp only [hz, ↓reduceIte]
          apply Finset.sum_eq_zero
          intro ω _
          split_ifs with h
          · exact False.elim (hz (hp ω h.1 z h.2))
          · rfl
  calc
    F * μ.prob E ≤ ∑ ω, if ω ∈ E then ∑ z ∈ moves ω, μ.mass ω else 0 := by
      simp only [prob, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro ω _
      by_cases hω : ω ∈ E
      · simp only [hω, ↓reduceIte, Finset.sum_const, nsmul_eq_mul]
        nlinarith [μ.nonneg ω, hF ω hω]
      · simp [hω]
    _ = _ := transport
    _ ≤ B * μ.prob P := by
      simp only [prob, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : z ∈ P
      · simp only [hz, ↓reduceIte]
        nlinarith [μ.nonneg z, hB z]
      · simp [hz]

end Law

end SteinerLowerBound
