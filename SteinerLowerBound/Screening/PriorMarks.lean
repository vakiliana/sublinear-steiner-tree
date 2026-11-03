module

public import SteinerLowerBound.Screening.Experiment

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening.Experiment

open HardDistribution

variable {S C W : Type*} [Fintype S] [Fintype C] [Fintype W]

noncomputable def vertexConstant (d : ℕ) (H₀ M : ℝ) : ℝ :=
  24 * H₀ * M ^ d * (d.choose 3) / d

theorem potential_vertex_le (k : Setup S W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) (hm : 4 ≤ Fintype.card S)
    (w : S → W) (e : Subsets S 2) (u : S) (hu : u ∉ e.val) :
    (potentialLaw k.d k.H0 k.R (fun v => k.value (w v)) e
      (by have := k.d_ge_three; omega) k.enough_special
      k.H0_nonneg k.R_pos (fun v => (k.bounded (w v)).1)
      k.M (fun v => (k.bounded (w v)).2) hsmall).prob
        {a | u ∈ a.elim ∅ Subtype.val} ≤
      vertexConstant k.d k.H0 k.M / (k.R * Fintype.card S) := by
  classical
  let m := Fintype.card S
  have hd : (0 : ℝ) < k.d := by exact_mod_cast (by have := k.d_ge_three; omega : 0 < k.d)
  have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm₂ : (0 : ℝ) < (m - 2 : ℕ) := by exact_mod_cast (by omega : 0 < m - 2)
  have hc : (0 : ℝ) < m.choose k.d := by exact_mod_cast Nat.choose_pos k.enough_special
  have hc₃ : (0 : ℝ) < m.choose 3 := by exact_mod_cast Nat.choose_pos (show 3 ≤ m by omega)
  have hM : 0 ≤ k.M := (k.bounded (w u)).1.trans (k.bounded (w u)).2
  have hH₀ := k.H0_nonneg
  have hR := k.R_pos
  have hP : (insert u e.val).card = 3 := by
    rw [Finset.card_insert_of_notMem hu, e.property]
  have hid : (m.choose k.d : ℝ) * (k.d.choose 3 : ℝ) =
      (m.choose 3 : ℝ) * ((m - 3).choose (k.d - 3) : ℝ) := by
    exact_mod_cast (Nat.choose_mul (n := m) k.d_ge_three)
  have hratio : (((m - 3).choose (k.d - 3) : ℕ) : ℝ) / m.choose k.d =
      (k.d.choose 3 : ℝ) / m.choose 3 := by
    apply (div_eq_div_iff hc.ne' hc₃.ne').mpr
    nlinarith [hid]
  have hid₂ : (m.choose 3 : ℝ) * 3 = (m.choose 2 : ℝ) * ((m - 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq m 2
  have hratio₂ : (m.choose 2 : ℝ) / m.choose 3 = 3 / ((m - 2 : ℕ) : ℝ) := by
    apply (div_eq_div_iff hc₃.ne' hm₂.ne').mpr
    nlinarith [hid₂]
  have hprob :
      (potentialLaw k.d k.H0 k.R (fun v => k.value (w v)) e
        (by have := k.d_ge_three; omega) k.enough_special
        k.H0_nonneg k.R_pos (fun v => (k.bounded (w v)).1)
        k.M (fun v => (k.bounded (w v)).2) hsmall).prob
          {a | u ∈ a.elim ∅ Subtype.val} =
      (∑ H : Subsets S k.d, if insert u e.val ⊆ H.val then
        starMass k.d k.H0 k.R (fun v => k.value (w v)) H else 0) / beta S := by
    simp only [potentialLaw, Law.prob, Law.withNone, Fintype.sum_option,
      Set.mem_ofPred_eq, Option.elim_none, Finset.notMem_empty, ↓reduceIte,
      Option.elim_some, zero_add, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro H _
    by_cases he : e.val ⊆ H.val <;> by_cases huH : u ∈ H.val <;>
      simp [Finset.insert_subset_iff, he, huH]
  rw [hprob]
  calc
    _ ≤ (((m - 3).choose (k.d - 3) : ℕ) : ℝ) *
        (k.H0 / ((k.d : ℝ) * k.R * m.choose k.d) * k.M ^ k.d) / beta S := by
      apply div_le_div_of_nonneg_right _ (beta_pos (by omega : 2 ≤ Fintype.card S)).le
      simpa only [hP] using prescribed_mass_le k.d (insert u e.val)
        (by rw [hP]; exact k.d_ge_three) k.H0_nonneg k.R_pos.le
        (fun v => (k.bounded (w v)).1) (fun v => (k.bounded (w v)).2)
    _ = (4 * k.H0 * k.M ^ k.d / ((k.d : ℝ) * k.R)) *
        ((((m - 3).choose (k.d - 3) : ℕ) : ℝ) / m.choose k.d) * (m.choose 2 : ℝ) := by
      unfold beta
      dsimp only [m]
      field_simp
      <;> ring
    _ = (4 * k.H0 * k.M ^ k.d / ((k.d : ℝ) * k.R)) *
        (k.d.choose 3 : ℝ) * ((m.choose 2 : ℝ) / m.choose 3) := by
      rw [hratio]
      ring
    _ = 12 * k.H0 * k.M ^ k.d * (k.d.choose 3 : ℝ) /
        ((k.d : ℝ) * k.R * ((m - 2 : ℕ) : ℝ)) := by
      rw [hratio₂]
      ring
    _ ≤ vertexConstant k.d k.H0 k.M / (k.R * m) := by
      unfold vertexConstant
      have hden : 0 < (k.d : ℝ) * k.R * ((m - 2 : ℕ) : ℝ) := by positivity
      have hnum : 0 ≤ k.H0 * k.M ^ k.d * (k.d.choose 3 : ℝ) := by positivity
      have hbound : (m : ℝ) ≤ 2 * ((m - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : m ≤ 2 * (m - 2))
      rw [div_div]
      apply (div_le_div_iff₀ hden (mul_pos hd (mul_pos hR hm'))).mpr
      nlinarith [mul_nonneg hnum (show 0 ≤ 2 * ((m - 2 : ℕ) : ℝ) - m by linarith)]

theorem kernel_vertex_le (k : Setup S W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) (hm : 4 ≤ Fintype.card S)
    (b : Base S C W) (c : C) (u : S) (hu : u ∉ fillerNeighbors (b.2 c)) :
    (kernel k hsmall b c).prob {a | u ∈ a.elim ∅ Subtype.val} ≤
      vertexConstant k.d k.H0 k.M / (k.R * Fintype.card S) := by
  classical
  have hM : 0 ≤ k.M := (k.bounded (b.1 u)).1.trans (k.bounded (b.1 u)).2
  have hH₀ := k.H0_nonneg
  have hR := k.R_pos
  have hn : 0 ≤ vertexConstant k.d k.H0 k.M / (k.R * Fintype.card S) := by
    unfold vertexConstant
    positivity
  rcases hf : b.2 c with (_ | v | e)
  · simp [kernel, MetricComparison.markLaw, hf, Law.prob_pure, hn]
  · simp [kernel, MetricComparison.markLaw, hf, Law.prob_pure, hn]
  · have hu' : u ∉ e.val := by simpa only [hf, fillerNeighbors] using hu
    simpa only [kernel, MetricComparison.markLaw, hf] using
      potential_vertex_le k hsmall hm b.1 e u hu'

end Screening.Experiment

end SteinerLowerBound
