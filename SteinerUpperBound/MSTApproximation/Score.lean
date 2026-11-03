module

public import SteinerUpperBound.MSTApproximation.Components
public import SteinerUpperBound.ScoreSampling
public import SteinerUpperBound.EstimationAlgebra

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry
open scoped Classical BigOperators

variable {V : Type*} [Fintype V]

noncomputable abbrev pointPart (I : Instance V) (S : Finset V) (a : ℝ)
    (x : ↥S) : ↥(componentsOn I S a) :=
  ⟨componentOn I S a x, componentOn_mem_componentsOn I S a x.property⟩

theorem pointPart_surjective (I : Instance V) (S : Finset V) (a : ℝ) :
    Function.Surjective (pointPart I S a) := by
  intro C
  obtain ⟨x, hx⟩ := componentsOn_nonempty I S a C.property
  refine ⟨⟨x, componentsOn_subset I S a C.property hx⟩, ?_⟩
  exact Subtype.ext (componentOn_eq_of_mem I S a C.property hx)

theorem pointPart_size (I : Instance V) (S : Finset V) (a : ℝ) (C : ↥(componentsOn I S a)) :
    SavingScores.partSize (pointPart I S a) C = C.val.card := by
  classical
  letI : DecidablePred (fun x : ↥S => pointPart I S a x = C) :=
    fun _ => Classical.propDecidable _
  unfold SavingScores.partSize SavingScores.fiber
  apply Finset.card_bij (fun (x : ↥S) _ => x.val)
  · intro x hx
    have he := congrArg Subtype.val (Finset.mem_filter.mp hx).2
    rw [← he]
    exact componentOn_self I S a x.property
  · intro x hx y hy he
    exact Subtype.ext he
  · intro y hy
    refine ⟨⟨y, componentsOn_subset I S a C.property hy⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Subtype.ext (componentOn_eq_of_mem I S a C.property hy)⟩

noncomputable def smallComponents (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ) :
    Finset (Finset V) := (componentsOn I S a).filter (fun C => C.card ≤ B)

noncomputable def largeComponents (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ) :
    Finset (Finset V) := (componentsOn I S a).filter (fun C => B < C.card)

noncomputable def pointScore (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ) (x : ↥S) : ℝ :=
  if (componentOn I S a x).card ≤ B then 1 / ((componentOn I S a x).card : ℝ) else 0

noncomputable def scoreMean (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ) : ℝ :=
  ((smallComponents I S a B).card : ℝ) / S.card

theorem pointScore_bounds (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ) (x : ↥S) :
    0 ≤ pointScore I S a B x ∧ pointScore I S a B x ≤ 1 := by
  have hr := SavingScores.reciprocal_bounds (pointPart I S a) (pointPart_surjective I S a)
    (pointPart I S a x)
  rw [pointPart_size] at hr
  by_cases h : (componentOn I S a x).card ≤ B
  · simpa only [pointScore, h, ↓reduceIte] using hr
  · simp [pointScore, h]

theorem pointScore_mean (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ) [Nonempty ↥S] :
    (Law.uniform ↥S).expect (pointScore I S a B) = scoreMean I S a B := by
  have h := SavingScores.uniform_part_mean (pointPart I S a) (pointPart_surjective I S a)
    (fun C => if C.val.card ≤ B then (1 : ℝ) else 0)
  have hf : (fun x : ↥S => (if (pointPart I S a x).val.card ≤ B then (1 : ℝ) else 0) /
      (SavingScores.partSize (pointPart I S a) (pointPart I S a x) : ℝ)) =
      pointScore I S a B := by
    funext x
    rw [pointPart_size]
    by_cases h : (componentOn I S a x).card ≤ B <;> simp [pointScore, h]
  rw [hf] at h
  have hs : (∑ C : ↥(componentsOn I S a), if C.val.card ≤ B then (1 : ℝ) else 0) =
      ((smallComponents I S a B).card : ℝ) := by
    rw [Finset.sum_coe_sort (componentsOn I S a)
      (fun C : Finset V => if C.card ≤ B then (1 : ℝ) else 0), ← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, smallComponents]
  rw [hs] at h
  simpa only [scoreMean, Nat.card_eq_fintype_card, Fintype.card_coe] using h

theorem scoreMean_bounds (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ) (hS : S.Nonempty) :
    0 ≤ scoreMean I S a B ∧ scoreMean I S a B ≤ 1 := by
  letI : Nonempty ↥S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  rw [← pointScore_mean]
  exact ScoreSampling.mean_bounds _ _ (fun x => (pointScore_bounds I S a B x).1)
    (fun x => (pointScore_bounds I S a B x).2)

theorem component_card_sum (I : Instance V) (S : Finset V) (a : ℝ) :
    (∑ C ∈ componentsOn I S a, C.card) = S.card := by
  have h := SavingScores.sum_partSize (pointPart I S a)
  simp_rw [pointPart_size] at h
  simpa only [Finset.sum_coe_sort, Nat.card_eq_fintype_card, Fintype.card_coe] using h

theorem large_components_count (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ) :
    (B + 1) * (largeComponents I S a B).card ≤ S.card := by
  calc
    _ = ∑ _C ∈ largeComponents I S a B, (B + 1) := by simp [Nat.mul_comm]
    _ ≤ ∑ C ∈ largeComponents I S a B, C.card :=
      Finset.sum_le_sum (fun C hC => (Finset.mem_filter.mp hC).2)
    _ ≤ ∑ C ∈ componentsOn I S a, C.card :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = _ := component_card_sum I S a

theorem large_components_div_bound (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ) :
    ((largeComponents I S a B).card : ℝ) ≤ (S.card : ℝ) / (B + 1) := by
  have hn : ((B : ℝ) + 1) * ((largeComponents I S a B).card : ℝ) ≤ S.card := by
    exact_mod_cast large_components_count I S a B
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < B + 1)).mpr (by nlinarith)

theorem componentCount_split (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ) :
    componentCount I S a = (smallComponents I S a B).card + (largeComponents I S a B).card := by
  have h := Finset.sum_filter_add_sum_filter_not (componentsOn I S a)
    (fun C => C.card ≤ B) (fun _ => (1 : ℕ))
  simpa [componentCount, smallComponents, largeComponents, not_le] using h.symm

theorem lowerCount_component_bounds (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ)
    (hS : S.Nonempty) (gminus empirical xi : ℝ) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hcal : (1 - xi) * (S.card : ℝ) ≤ gminus) (hcal1 : gminus ≤ S.card)
    (he : |empirical - scoreMean I S a B| ≤ xi) :
    0 ≤ Estimation.lowerCount gminus empirical xi ∧
      Estimation.lowerCount gminus empirical xi ≤ (smallComponents I S a B).card ∧
      (componentCount I S a : ℝ) - Estimation.lowerCount gminus empirical xi ≤
        (S.card : ℝ) / (B + 1) + 3 * xi * S.card := by
  have hm := scoreMean_bounds I S a B hS
  have hg : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hmean : (S.card : ℝ) * scoreMean I S a B = (smallComponents I S a B).card := by
    unfold scoreMean
    field_simp
  obtain ⟨hz, hzs, hgap⟩ := Estimation.lowerCount_bounds (S.card : ℝ)
    gminus (scoreMean I S a B) empirical xi hg.le hxi hxi1 hm.1 hm.2 hcal hcal1 he
  rw [hmean] at hzs hgap
  have hsplit : (componentCount I S a : ℝ) =
      ((smallComponents I S a B).card : ℝ) + (largeComponents I S a B).card := by
    exact_mod_cast componentCount_split I S a B
  exact ⟨hz, hzs, by linarith [large_components_div_bound I S a B]⟩

theorem iid_score_deviation (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ)
    [Nonempty ↥S] (samples : ℕ) (hn : 0 < samples) (xi beta : ℝ) (hxi : 0 < xi)
    (hbudget : 1 ≤ beta * ((samples : ℝ) * xi ^ 2)) :
    (Covers.FiniteSampling.tape (Law.uniform ↥S) samples).prob
      {w | xi < |ScoreSampling.empirical (pointScore I S a B) samples w - scoreMean I S a B|} ≤
        beta := by
  rw [← pointScore_mean]
  exact ScoreSampling.empirical_deviation_of_budget _ _
    (fun x => (pointScore_bounds I S a B x).1) (fun x => (pointScore_bounds I S a B x).2)
    samples hn xi beta hxi hbudget

end SteinerUpperBound.MSTApproximation
