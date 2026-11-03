module

public import SteinerLowerBound.MetricComparison.StarBounds

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Law

theorem mass_le_prob {W : Type*} [Fintype W] (μ : Law W) (w : W) (E : Set W)
    (hw : w ∈ E) : μ.mass w ≤ μ.prob E := by
  have h := μ.prob_mono (Set.singleton_subset_iff.mpr hw)
  simpa only [prob, Set.mem_singleton_iff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using h

end Law

namespace MetricComparison

open HardDistribution

variable {S : Type*} [Fintype S]

theorem beta_formula : beta S =
    1 / (2 * (Fintype.card S : ℝ) * ((Fintype.card S : ℝ) - 1)) := by
  unfold beta
  rw [Nat.cast_choose_two]
  congr 1
  ring

theorem beta_bounds (hm : 2 ≤ Fintype.card S) :
    1 / (2 * (Fintype.card S : ℝ) ^ 2) ≤ beta S ∧
      beta S ≤ 1 / (Fintype.card S : ℝ) ^ 2 := by
  have hm' : (2 : ℝ) ≤ Fintype.card S := by exact_mod_cast hm
  have hm₀ : (0 : ℝ) < Fintype.card S := by linarith
  have hm₁ : (0 : ℝ) < (Fintype.card S : ℝ) - 1 := by linarith
  rw [beta_formula]
  constructor <;> apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr <;>
    nlinarith [sq_nonneg ((Fintype.card S : ℝ) - 2)]

theorem filler_hit_probability (hm : 2 ≤ Fintype.card S) (u : S) :
    (fillerLaw hm).prob {f | u ∈ fillerNeighbors f} =
      3 / (4 * Fintype.card S) := by
  classical
  have hm' : (2 : ℝ) ≤ Fintype.card S := by exact_mod_cast hm
  have hm₀ : (Fintype.card S : ℝ) ≠ 0 := by linarith
  have hm₁ : (Fintype.card S : ℝ) - 1 ≠ 0 := by linarith
  have hc : (Finset.univ.filter (fun H : Subsets S 2 => u ∈ H.val)).card =
      Fintype.card S - 1 := by
    simpa using prescribed_count 2 {u} (by simp)
  have hsum : (∑ H : Subsets S 2, if u ∈ H.val then beta S else 0) =
      ((Fintype.card S - 1 : ℕ) : ℝ) * beta S := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, hc]
  have hexp : (fillerLaw hm).prob {f | u ∈ fillerNeighbors f} =
      1 / (4 * Fintype.card S) +
        ∑ H : Subsets S 2, if u ∈ H.val then beta S else 0 := by
    simp only [Law.prob, fillerLaw, Fintype.sum_sum_type, Set.mem_ofPred_eq,
      fillerNeighbors, Finset.notMem_empty, ↓reduceIte, Finset.sum_const_zero,
      Fintype.sum_unique, zero_add, Finset.mem_singleton, Finset.sum_ite_eq,
      Finset.mem_univ]
    congr 1
    apply Finset.sum_congr rfl
    intro H _
    by_cases hu : u ∈ H.val <;> simp only [hu, ↓reduceIte]
  rw [hexp, hsum]
  simp only [Nat.cast_sub (by omega : 1 ≤ Fintype.card S), Nat.cast_one, beta_formula]
  field_simp [hm₀, hm₁]
  <;> ring

theorem filler_evidence_nonneg (hm : 2 ≤ Fintype.card S) (h : History S) :
    0 ≤ fillerEvidence hm h := (fillerLaw hm).prob_nonneg _

theorem filler_evidence_le_one (hm : 2 ≤ Fintype.card S) (h : History S) :
    fillerEvidence hm h ≤ 1 := (fillerLaw hm).prob_le_one _

theorem filler_evidence_zero_lower (hm : 2 ≤ Fintype.card S) (h : History S)
    (hp : h.positive.card = 0) : 1 / 2 ≤ fillerEvidence hm h := by
  classical
  have he : h.positive = ∅ := Finset.card_eq_zero.mp hp
  have hh : h.compatible (fillerNeighbors (.inl () : Filler S)) := by
    simp [History.compatible, he, fillerNeighbors]
  exact (fillerLaw hm).mass_le_prob (.inl ()) _ hh

theorem filler_evidence_one_bounds (hm : 2 ≤ Fintype.card S)
    (h : History S) (hv : h.Valid) (hp : h.positive.card = 1) :
    1 / (4 * Fintype.card S) ≤ fillerEvidence hm h ∧
      fillerEvidence hm h ≤ 1 / Fintype.card S := by
  classical
  obtain ⟨u, hP⟩ := Finset.card_eq_one.mp hp
  have hh : h.compatible (fillerNeighbors (.inr (.inl u) : Filler S)) := by
    simpa only [History.compatible, fillerNeighbors, hP, Finset.Subset.refl, true_and] using hv.1
  refine ⟨(fillerLaw hm).mass_le_prob (.inr (.inl u)) _ hh, ?_⟩
  have hmono : fillerEvidence hm h ≤ (fillerLaw hm).prob {f | u ∈ fillerNeighbors f} := by
    apply (fillerLaw hm).prob_mono
    intro f hf
    exact hf.1 (by simp [hP])
  rw [filler_hit_probability hm u] at hmono
  have hm₀ : (0 : ℝ) < Fintype.card S := by exact_mod_cast (show 0 < Fintype.card S by omega)
  apply hmono.trans
  apply (div_le_div_iff₀ (by positivity) hm₀).mpr
  nlinarith

theorem filler_evidence_two (hm : 2 ≤ Fintype.card S)
    (h : History S) (hv : h.Valid) (hp : h.positive.card = 2) :
    fillerEvidence hm h = beta S := by
  classical
  let e : Subsets S 2 := ⟨h.positive, hp⟩
  have he : {f : Filler S | h.compatible (fillerNeighbors f)} = {.inr (.inr e)} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hf
      have heq : h.positive = fillerNeighbors f :=
        Finset.eq_of_subset_of_card_le hf.1 (by rw [hp]; exact filler_card_le_two f)
      exact (fillerNeighbors_eq_pair f e).mp heq.symm
    · intro hf
      subst f
      exact ⟨Finset.Subset.refl _, hv.1⟩
  unfold fillerEvidence
  rw [he]
  simp only [Law.prob, Set.mem_singleton_iff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rfl

theorem filler_evidence_many (hm : 2 ≤ Fintype.card S)
    (h : History S) (hp : 3 ≤ h.positive.card) : fillerEvidence hm h = 0 := by
  have he : {f : Filler S | h.compatible (fillerNeighbors f)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hc := (Finset.card_le_card hf.1).trans (filler_card_le_two f)
    omega
  simp [fillerEvidence, he]

theorem filler_evidence_pos (hm : 2 ≤ Fintype.card S)
    (h : History S) (hv : h.Valid) (hp : h.positive.card ≤ 2) :
    0 < fillerEvidence hm h := by
  have hm₀ : (0 : ℝ) < Fintype.card S := by exact_mod_cast (show 0 < Fintype.card S by omega)
  by_cases h₀ : h.positive.card = 0
  · exact lt_of_lt_of_le (by norm_num) (filler_evidence_zero_lower hm h h₀)
  by_cases h₁ : h.positive.card = 1
  · exact lt_of_lt_of_le (by positivity) (filler_evidence_one_bounds hm h hv h₁).1
  · rw [filler_evidence_two hm h hv (by omega)]
    exact beta_pos hm

theorem filler_rate_bounds (hm : 2 ≤ Fintype.card S)
    (h : History S) (hv : h.Valid) (u : S) (hf : h.Fresh u)
    (hp : h.positive.card ≤ 1) :
    1 / (4 * Fintype.card S) ≤
        fillerEvidence hm (h.update u true) / fillerEvidence hm h ∧
      fillerEvidence hm (h.update u true) / fillerEvidence hm h ≤
        4 / Fintype.card S := by
  classical
  have hm' : (2 : ℝ) ≤ Fintype.card S := by exact_mod_cast hm
  have hm₀ : (0 : ℝ) < Fintype.card S := by linarith
  have hv' := h.update_valid u true hv hf
  have hpc : (h.update u true).positive.card = h.positive.card + 1 := by
    simp only [History.update, ↓reduceIte, Finset.card_insert_of_notMem hf.1]
  have hpos := filler_evidence_pos hm h hv (by omega)
  by_cases hp₀ : h.positive.card = 0
  · have hpl := filler_evidence_zero_lower hm h hp₀
    have hpu := filler_evidence_le_one hm h
    have hn := filler_evidence_one_bounds hm (h.update u true) hv' (by omega)
    constructor
    · apply (le_div_iff₀ hpos).mpr
      apply le_trans _ hn.1
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    · apply (div_le_iff₀ hpos).mpr
      apply hn.2.trans
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff₀ hm₀ hm₀).mpr
      nlinarith
  · have hp₁ : h.positive.card = 1 := by omega
    have hh := filler_evidence_one_bounds hm h hv hp₁
    rw [filler_evidence_two hm (h.update u true) hv' (by omega)]
    obtain ⟨hβl, hβu⟩ := beta_bounds (S := S) hm
    constructor
    · apply (le_div_iff₀ hpos).mpr
      apply le_trans _ hβl
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hb := (le_div_iff₀ hm₀).mp hh.2
      nlinarith
    · apply (div_le_iff₀ hpos).mpr
      apply hβu.trans
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff₀ (by positivity) hm₀).mpr
      have hb := (div_le_iff₀ (by positivity : 0 < 4 * (Fintype.card S : ℝ))).mp hh.1
      nlinarith

end MetricComparison

end SteinerLowerBound
