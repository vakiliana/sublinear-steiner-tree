module

public import SteinerUpperBound.Matching.Padded.TerminalBounds

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E] [Nonempty V]
    (P : Parameters S)

theorem Oracle.bucket_expectation (A : Account S) (z : ℝ) (hz : 0 ≤ z) :
    (Law.uniform V).expect (fun v =>
      (Oracle.vertex S P v).expectedCost (Command.bucketCharge A) A.rate) ≤
      2 * Parameters.bucketCoefficient S P *
          ((8 * z + 10) * ((1 + 2 * G.callBudget) * (∑ v, A.W v) / Fintype.card V) +
            (∑ v, A.W v) * ((Fintype.card E : ℝ) ^ 2 / P.rankCard +
              Fintype.card V * (P.rankExponent + 2) * Real.exp (-z))) +
        Parameters.bucketCoefficient S P * A.Cstar *
          (((P.rankExponent : ℝ) + 1) *
              (1 + (4 * Fintype.card E : ℝ) * G.callBudget / Fintype.card V) +
            ((P.rankExponent : ℝ) + 1) * Fintype.card V *
              ((Fintype.card E : ℝ) ^ 2 / P.rankCard)) +
        A.Cstar * ((1 + (4 * Fintype.card E : ℝ) * G.callBudget / Fintype.card V) +
          Fintype.card V * ((Fintype.card E : ℝ) ^ 2 / P.rankCard)) := by
  have hL : (0 : ℝ) ≤ Parameters.bucketCoefficient S P := Nat.cast_nonneg _
  have hH : (0 : ℝ) ≤ (P.rankExponent : ℝ) + 1 := by positivity
  have hC : 0 ≤ 8 * z + 10 := by linarith
  have hφ := (Law.uniform V).expect_mono (fun v => Oracle.boundary_moment S P A v z hz)
  rw [Law.expect_add, Law.expect_const_mul, Law.expect_const] at hφ
  have hφ' := hφ.trans (add_le_add
    (mul_le_mul_of_nonneg_left (expected_good_densityRequests S P A) hC) (le_refl _))
  have hlevel := (Law.uniform V).expect_mono (fun v => Oracle.level_moment S P v)
  rw [Law.expect_add, Law.expect_const_mul, Law.expect_const] at hlevel
  have hlevel' := hlevel.trans (add_le_add
    (mul_le_mul_of_nonneg_left (expected_good_totalRequests S P) hH) (le_refl _))
  have hprep := (Law.uniform V).expect_mono (fun v => Oracle.prepared_moment S P v)
  rw [Law.expect_add, Law.expect_const] at hprep
  have hprep' := hprep.trans (add_le_add (expected_good_totalRequests S P) (le_refl _))
  have hwork := (Law.uniform V).expect_mono (fun v => Oracle.bucket_moments S P A v)
  rw [Law.expect_add, Law.expect_add, Law.expect_const_mul, Law.expect_const_mul,
    Law.expect_const_mul] at hwork
  exact hwork.trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hφ' (mul_nonneg (by norm_num) hL))
      (mul_le_mul_of_nonneg_left hlevel' (mul_nonneg hL A.Cstar_nonneg)))
    (mul_le_mul_of_nonneg_left hprep' A.Cstar_nonneg))

end SteinerUpperBound.Matching.Padded
