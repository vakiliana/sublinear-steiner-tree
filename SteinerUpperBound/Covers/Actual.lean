module

public import SteinerUpperBound.Covers.Product

@[expose] public section

namespace SteinerUpperBound.Covers

open SteinerLowerBound
open scoped Classical BigOperators

noncomputable local instance {V : Type*} (I : Instance V) : DecidableEq (Terminal I) :=
  Classical.decEq _

noncomputable def actualBits {V : Type*} (I : Instance V) (r : ℝ)
    (root : Terminal I) (B ψ : ℕ) : Law (Terminal I → Bool) := by
  letI : Nonempty (Terminal I) := ⟨root⟩
  exact Factory.privateBits (near I r) root B ψ

theorem actual_root_on_support {V : Type*} (I : Instance V) (r : ℝ)
    (root : Terminal I) (B ψ : ℕ) (b : Terminal I → Bool)
    (hb : 0 < (actualBits I r root B ψ).mass b) : b root = true := by
  letI : Nonempty (Terminal I) := ⟨root⟩
  have h := Law.pi_mass_positive (Factory.forcedBitLaw (near I r) root B ψ) b hb root
  cases he : b root <;> simp [Factory.forcedBitLaw, he, Law.pure] at h ⊢

theorem actual_nonempty_on_support {V : Type*} (I : Instance V) (r : ℝ)
    (root : Terminal I) (B ψ : ℕ) (b : Terminal I → Bool)
    (hb : 0 < (actualBits I r root B ψ).mass b) :
    (CategoricalCoupling.selected b).Nonempty :=
  ⟨root, Finset.mem_filter.mpr ⟨Finset.mem_univ _, actual_root_on_support I r root B ψ b hb⟩⟩

theorem actual_cover_and_size {V : Type*} [Fintype V] (I : Instance V)
    (r : ℝ) (hr : 0 < r) (root : Terminal I) (B ψ h : ℕ)
    (hh : I.terminals.card < 2 ^ h) (v : ℝ) :
    (actualBits I r root B ψ).prob
      {b | ¬ IsCover I ((h : ℝ) * r) b ∨
        Real.exp 1 * (1 + (ψ : ℝ) * (1 + 2 * I.mst / r)) + v ≤
          ((CategoricalCoupling.selected b).card : ℝ)} ≤
      (I.terminals.card : ℝ) * Real.exp (-(ψ : ℝ) / 2) + Real.exp (-v) +
        (I.terminals.card : ℝ) * Real.exp (-(B : ℝ) / I.terminals.card) := by
  classical
  letI : Nonempty (Terminal I) := ⟨root⟩
  have hc := Factory.privateBits_close (near I r) (near_refl I hr.le) root B ψ
  have hb := independent_cover_and_size I r hr root ψ h hh v
  have he := (abs_le.mp (hc {b | ¬ IsCover I ((h : ℝ) * r) b ∨
    Real.exp 1 * (1 + (ψ : ℝ) * (1 + 2 * I.mst / r)) + v ≤
      ((CategoricalCoupling.selected b).card : ℝ)})).2
  simp only [Fintype.card_coe] at he
  dsimp only [actualBits]
  linarith

def hopCount (k : ℕ) : ℕ := Nat.log 2 k + 1

theorem hopCount_growth (k : ℕ) : k < 2 ^ hopCount k :=
  Nat.lt_pow_succ_log_self (by decide) k

noncomputable def retentionBudget (k m : ℕ) (β : ℝ) : ℕ :=
  ⌈2 * Real.log (4 * (k : ℝ) * m / β)⌉₊

noncomputable def privateDrawBudget (k m : ℕ) (β : ℝ) : ℕ :=
  ⌈(k : ℝ) * Real.log (4 * (k : ℝ) * m / β)⌉₊

noncomputable def sizeSlack (m : ℕ) (β : ℝ) : ℝ :=
  Real.log (4 * (m : ℝ) / β)

theorem budget_error (k m : ℕ) (hk : 0 < k) (hm : 0 < m) (β : ℝ) (hβ : 0 < β) :
    (k : ℝ) * Real.exp (-(retentionBudget k m β : ℝ) / 2) +
      Real.exp (-sizeSlack m β) +
      (k : ℝ) * Real.exp (-(privateDrawBudget k m β : ℝ) / k) ≤ β / m := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : 0 < 4 * (k : ℝ) * m / β := by positivity
  have hs : 0 < 4 * (m : ℝ) / β := by positivity
  have hψ := Nat.le_ceil (2 * Real.log (4 * (k : ℝ) * m / β))
  have hB := Nat.le_ceil ((k : ℝ) * Real.log (4 * (k : ℝ) * m / β))
  have heψ : Real.exp (-(retentionBudget k m β : ℝ) / 2) ≤
      (4 * (k : ℝ) * m / β)⁻¹ := by
    calc
      _ ≤ Real.exp (-Real.log (4 * (k : ℝ) * m / β)) := by
        apply Real.exp_le_exp.mpr
        dsimp [retentionBudget]
        linarith
      _ = _ := by rw [Real.exp_neg, Real.exp_log hp]
  have heB : Real.exp (-(privateDrawBudget k m β : ℝ) / k) ≤
      (4 * (k : ℝ) * m / β)⁻¹ := by
    calc
      _ ≤ Real.exp (-Real.log (4 * (k : ℝ) * m / β)) := by
        apply Real.exp_le_exp.mpr
        apply (div_le_iff₀ hkR).mpr
        dsimp [privateDrawBudget]
        nlinarith
      _ = _ := by rw [Real.exp_neg, Real.exp_log hp]
  have hev : Real.exp (-sizeSlack m β) = (4 * (m : ℝ) / β)⁻¹ := by
    rw [sizeSlack, Real.exp_neg, Real.exp_log hs]
  calc
    _ ≤ (k : ℝ) * (4 * (k : ℝ) * m / β)⁻¹ + (4 * (m : ℝ) / β)⁻¹ +
        (k : ℝ) * (4 * (k : ℝ) * m / β)⁻¹ := by
      rw [hev]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left heψ hkR.le) le_rfl)
        (mul_le_mul_of_nonneg_left heB hkR.le)
    _ = 3 * β / (4 * m) := by field_simp; ring
    _ ≤ β / m := by
      apply (div_le_div_iff₀ (by positivity : 0 < 4 * (m : ℝ)) hmR).mpr
      nlinarith

theorem actual_cover_and_size_budget {V : Type*} [Fintype V] (I : Instance V)
    (r : ℝ) (hr : 0 < r) (root : Terminal I) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 0 < β) :
    (actualBits I r root (privateDrawBudget I.terminals.card m β)
      (retentionBudget I.terminals.card m β)).prob
      {b | ¬ IsCover I ((hopCount I.terminals.card : ℝ) * r) b ∨
        Real.exp 1 * (1 + (retentionBudget I.terminals.card m β : ℝ) *
          (1 + 2 * I.mst / r)) + sizeSlack m β ≤
            ((CategoricalCoupling.selected b).card : ℝ)} ≤ β / m := by
  apply (actual_cover_and_size I r hr root _ _ _ (hopCount_growth _) _).trans
  exact budget_error I.terminals.card m (Finset.card_pos.mpr ⟨root.val, root.property⟩)
    hm β hβ

theorem actual_all_scales {V S : Type*} [Fintype V] [Fintype S] [Nonempty S]
    (I : Instance V) (r : S → ℝ) (hr : ∀ i, 0 < r i) (root : Terminal I)
    (β : ℝ) (hβ : 0 < β) :
    (Law.pi (fun i : S => actualBits I (r i) root
      (privateDrawBudget I.terminals.card (Fintype.card S) β)
      (retentionBudget I.terminals.card (Fintype.card S) β))).prob
      {b | ∃ i : S, ¬ IsCover I ((hopCount I.terminals.card : ℝ) * r i) (b i) ∨
        Real.exp 1 * (1 + (retentionBudget I.terminals.card (Fintype.card S) β : ℝ) *
          (1 + 2 * I.mst / r i)) + sizeSlack (Fintype.card S) β ≤
            ((CategoricalCoupling.selected (b i)).card : ℝ)} ≤ β := by
  classical
  let μ := fun i : S => actualBits I (r i) root
    (privateDrawBudget I.terminals.card (Fintype.card S) β)
    (retentionBudget I.terminals.card (Fintype.card S) β)
  let P := fun i (b : Terminal I → Bool) =>
    ¬ IsCover I ((hopCount I.terminals.card : ℝ) * r i) b ∨
      Real.exp 1 * (1 + (retentionBudget I.terminals.card (Fintype.card S) β : ℝ) *
        (1 + 2 * I.mst / r i)) + sizeSlack (Fintype.card S) β ≤
          ((CategoricalCoupling.selected b).card : ℝ)
  calc
    _ ≤ ∑ i : S, (Law.pi μ).prob {b | P i (b i)} := Law.finite_union_bound _ _
    _ = ∑ i : S, (μ i).prob {b | P i b} := by
      apply Finset.sum_congr rfl
      intro i _
      exact Law.prob_pi_coordinate μ {b | P i b} i
    _ ≤ ∑ _i : S, β / Fintype.card S := by
      apply Finset.sum_le_sum
      intro i _
      exact actual_cover_and_size_budget I (r i) (hr i) root _ Fintype.card_pos β hβ
    _ = β := by
      have hcard : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

end SteinerUpperBound.Covers
