module

public import SteinerUpperBound.EstimatorParameters.Allowances

@[expose] public section

namespace SteinerUpperBound.EstimatorParameters

open SteinerLowerBound
open scoped Classical BigOperators

noncomputable local instance {V : Type*} (I : Instance V) : DecidableEq (Covers.Terminal I) :=
  Classical.decEq _

def CoverBad {V : Type*} [Fintype V] (I : Instance V) (n : ℕ) (rho : ℝ)
    (b : Covers.Terminal I → Bool) : Prop :=
  ¬ Covers.IsCover I rho b ∨
    Real.exp 1 * (1 + (coverTrials n : ℝ) *
      (1 + 2 * Covers.hopCount I.terminals.card * I.mst / rho)) + coverSlack n ≤
        ((CategoricalCoupling.selected b).card : ℝ)

theorem simultaneous_cover_failure {V S : Type*} [Fintype V] [Fintype S]
    (I : Instance V) (n : ℕ) (hkn : I.terminals.card ≤ n)
    (rho : S → ℝ) (hr : ∀ i, 0 < rho i) (root : Covers.Terminal I)
    (hcount : Fintype.card S ≤ heightBudget n) :
    (Law.pi (fun i : S => Covers.actualBits I (rho i / Covers.hopCount I.terminals.card) root
      (privateCap n I.terminals.card) (coverTrials n))).prob
      {b | ∃ i : S, CoverBad I n (rho i) (b i)} ≤ 1 / 4000000 := by
  classical
  let mu := fun i : S => Covers.actualBits I (rho i / Covers.hopCount I.terminals.card) root
    (privateCap n I.terminals.card) (coverTrials n)
  let P := fun i (b : Covers.Terminal I → Bool) => CoverBad I n (rho i) b
  calc
    _ ≤ ∑ i : S, (Law.pi mu).prob {b | P i (b i)} := Law.finite_union_bound _ _
    _ = ∑ i : S, (mu i).prob {b | P i b} := by
      apply Finset.sum_congr rfl
      intro i _
      exact Law.prob_pi_coordinate mu {b | P i b} i
    _ ≤ ∑ _i : S, beta n / 4 := by
      apply Finset.sum_le_sum
      intro i _
      exact actual_cover_failure I n hkn (rho i) (hr i) root
    _ = ((Fintype.card S : ℝ) * beta n) / 4 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have h := beta_union n (Fintype.card S) hcount
      linarith

theorem good_cover_size {V : Type*} [Fintype V] (I : Instance V) (n : ℕ)
    (hkn : I.terminals.card ≤ n) (rho : ℝ) (hr : 0 < rho) (b : Covers.Terminal I → Bool)
    (hgood : ¬ CoverBad I n rho b) :
    Covers.IsCover I rho b ∧ ((CategoricalCoupling.selected b).card : ℝ) ≤
      Hc n + 6 * coverTrials n * hopBudget n * I.mst / rho := by
  have hcover : Covers.IsCover I rho b := by
    unfold CoverBad at hgood
    tauto
  have hsize : ((CategoricalCoupling.selected b).card : ℝ) <
      Real.exp 1 * (1 + (coverTrials n : ℝ) *
        (1 + 2 * Covers.hopCount I.terminals.card * I.mst / rho)) + coverSlack n := by
    unfold CoverBad at hgood
    exact lt_of_not_ge (by tauto)
  have hlin := MSTApproximation.factory_size_bound I _ rho (coverSlack n) (coverTrials n)
    (Covers.hopCount I.terminals.card) hr hsize.le
  have hhop : (Covers.hopCount I.terminals.card : ℝ) ≤ hopBudget n := by
    exact_mod_cast hopBudget_bounds n I.terminals.card hkn
  have hm := mul_le_mul_of_nonneg_left hhop
    (show 0 ≤ 6 * (coverTrials n : ℝ) * I.mst / rho by positivity [I.mst_nonneg])
  have he : (Hc n : ℝ) = 3 * (1 + (coverTrials n : ℝ)) + coverSlack n := by
    unfold Hc
    push_cast
    ring
  refine ⟨hcover, ?_⟩
  rw [he]
  have hmono : 6 * (coverTrials n : ℝ) * Covers.hopCount I.terminals.card * I.mst / rho ≤
      6 * (coverTrials n : ℝ) * hopBudget n * I.mst / rho := by
    convert hm using 1 <;> ring
  exact hlin.trans (add_le_add le_rfl hmono)

end SteinerUpperBound.EstimatorParameters
