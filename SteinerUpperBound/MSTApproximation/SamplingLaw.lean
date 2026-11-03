module

public import SteinerUpperBound.MSTApproximation.Score
public import SteinerUpperBound.Covers.Calibration

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry
open scoped Classical BigOperators

variable {V U : Type*} [Fintype V] [Fintype U]

noncomputable def scoreOn (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ) (x : V) : ℝ :=
  if hx : x ∈ S then pointScore I S a B ⟨x, hx⟩ else 0

theorem scoreOn_mem (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ) {x : V} (hx : x ∈ S) :
    scoreOn I S a B x = pointScore I S a B ⟨x, hx⟩ := by simp [scoreOn, hx]

theorem scoreOn_bounds (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ) (x : V) :
    0 ≤ scoreOn I S a B x ∧ scoreOn I S a B x ≤ 1 := by
  by_cases hx : x ∈ S
  · rw [scoreOn_mem I S a B hx]
    exact pointScore_bounds I S a B ⟨x, hx⟩
  · simp [scoreOn, hx]

theorem sum_scoreOn (I : Instance V) (S : Finset V) (a : ℝ) (B : ℕ) :
    (∑ x ∈ S, scoreOn I S a B x) = ((smallComponents I S a B).card : ℝ) := by
  classical
  by_cases hS : S.Nonempty
  · letI : Nonempty ↥S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
    have hmean := pointScore_mean I S a B
    rw [SavingScores.uniform_expect, Nat.card_eq_fintype_card, Fintype.card_coe] at hmean
    have hs : (∑ x : ↥S, pointScore I S a B x) = ∑ x ∈ S, scoreOn I S a B x := by
      calc
        _ = ∑ x : ↥S, scoreOn I S a B x.val :=
          Finset.sum_congr rfl (fun x _ => (scoreOn_mem I S a B x.property).symm)
        _ = _ := Finset.sum_coe_sort S (scoreOn I S a B)
    rw [hs] at hmean
    unfold scoreMean at hmean
    exact (div_left_inj' (show (S.card : ℝ) ≠ 0 by exact_mod_cast (Finset.card_pos.mpr hS).ne')).mp hmean
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [smallComponents, componentsOn]

noncomputable def selectedPoints (e : U → V) (b : U → Bool) : Finset V :=
  (Covers.Rejection.retained b).image e

theorem selectedPoints_card (e : U → V) (he : Function.Injective e) (b : U → Bool) :
    (selectedPoints e b).card = (Covers.Rejection.retained b).card :=
  Finset.card_image_of_injective _ he

theorem uniformRetained_expect [Nonempty U] (b : U → Bool)
    (hb : (Covers.Rejection.retained b).Nonempty) (f : U → ℝ) :
    (Covers.Rejection.uniformRetained b hb).expect f =
      (∑ x ∈ Covers.Rejection.retained b, f x) / ((Covers.Rejection.retained b).card : ℝ) := by
  unfold Law.expect Covers.Rejection.uniformRetained
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  change ((Covers.Rejection.retained b).card : ℝ)⁻¹ * _ = _
  have he : Finset.univ.filter (fun x => b x = true) = Covers.Rejection.retained b := by
    ext x
    simp [Covers.Rejection.retained, CategoricalCoupling.selected]
  rw [he]
  ring

theorem retained_score_mean [Nonempty U] (I : Instance V) (e : U → V) (he : Function.Injective e)
    (b : U → Bool) (hb : (Covers.Rejection.retained b).Nonempty) (a : ℝ) (B : ℕ) :
    (Covers.Rejection.uniformRetained b hb).expect
      (fun x => scoreOn I (selectedPoints e b) a B (e x)) =
        scoreMean I (selectedPoints e b) a B := by
  rw [uniformRetained_expect]
  have hs : (∑ x ∈ Covers.Rejection.retained b, scoreOn I (selectedPoints e b) a B (e x)) =
      ∑ y ∈ selectedPoints e b, scoreOn I (selectedPoints e b) a B y := by
    unfold selectedPoints
    rw [Finset.sum_image]
    exact fun x hx y hy hxy => he hxy
  rw [hs, sum_scoreOn]
  unfold scoreMean
  rw [selectedPoints_card e he]

theorem retained_iid_score_deviation [Nonempty U] (I : Instance V) (e : U → V)
    (he : Function.Injective e) (b : U → Bool) (hb : (Covers.Rejection.retained b).Nonempty)
    (a : ℝ) (B samples : ℕ) (hn : 0 < samples) (xi beta : ℝ) (hxi : 0 < xi)
    (hbudget : 1 ≤ beta * ((samples : ℝ) * xi ^ 2)) :
    (Covers.FiniteSampling.tape (Covers.Rejection.uniformRetained b hb) samples).prob
      {w | xi < |ScoreSampling.empirical
        (fun x => scoreOn I (selectedPoints e b) a B (e x)) samples w -
          scoreMean I (selectedPoints e b) a B|} ≤ beta := by
  rw [← retained_score_mean I e he b hb a B]
  exact ScoreSampling.empirical_deviation_of_budget _ _
    (fun x => (scoreOn_bounds I _ a B (e x)).1)
    (fun x => (scoreOn_bounds I _ a B (e x)).2) samples hn xi beta hxi hbudget

end SteinerUpperBound.MSTApproximation
