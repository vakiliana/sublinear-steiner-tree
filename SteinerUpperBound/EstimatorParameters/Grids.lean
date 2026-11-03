module

public import SteinerUpperBound.EstimatorParameters.Logarithms

@[expose] public section

namespace SteinerUpperBound.EstimatorParameters

open scoped Classical
open MSTApproximation

def fineBlock : ℕ := 1000000000000000

theorem fine_doubling : (2 : ℝ) ≤ MSTApproximation.fineRatio nu ^ fineBlock := by
  have h := one_add_mul_le_pow (a := (1 / 1000000000000000 : ℝ)) (by norm_num) fineBlock
  conv_lhs at h => norm_num [fineBlock]
  rw [show (1 + 1 / 1000000000000000 : ℝ) = MSTApproximation.fineRatio nu by
    norm_num [MSTApproximation.fineRatio, nu, nuQ, cQ]] at h
  exact h

noncomputable def coarseConstants : GridConstants Structural.omega zeta :=
  ⟨100, 60, coarse_doubling, by norm_num [zeta, zetaQ, cQ]⟩

noncomputable def fineConstants : GridConstants (MSTApproximation.fineRatio nu) zeta :=
  ⟨fineBlock, 60, fine_doubling, by norm_num [zeta, zetaQ, cQ]⟩

def coarseFuel (k : ℕ) : ℕ := 100 * (61 + Nat.log2 (k + 1))
def fineFuel (k : ℕ) : ℕ := fineBlock * (61 + Nat.log2 (k + 1))

theorem coarseFuel_eq (k : ℕ) : coarseFuel k = coarseConstants.budget k := by
  change 100 * (61 + Nat.log2 (k + 1)) = 100 * (60 + Nat.log2 (k + 1) + 1)
  omega

theorem fineFuel_eq (k : ℕ) : fineFuel k = fineConstants.budget k := by
  change fineBlock * (61 + Nat.log2 (k + 1)) = fineBlock * (60 + Nat.log2 (k + 1) + 1)
  congr 1
  omega

def thetaQ (j : Fin FinitePhase.count) : ℚ := 1 + (1 / 100) * j.val / 1000000

theorem thetaQ_cast (j : Fin FinitePhase.count) : (thetaQ j : ℝ) = FinitePhase.theta j := by
  norm_num [thetaQ, FinitePhase.theta, FinitePhase.count, Structural.omega]

/-- This loop compares rational public data; its selected height is the first crossing. -/
def firstAboveQ (q x : ℚ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 => if 4 < x then 0 else 1 + firstAboveQ q (x * q) fuel

theorem firstAboveQ_cast (q x : ℚ) (fuel : ℕ) :
    firstAboveQ q x fuel = MSTApproximation.firstAbove (q : ℝ) (x : ℝ) fuel := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih =>
    by_cases hx : 4 < x
    · have hxr : (4 : ℝ) < (x : ℝ) := by exact_mod_cast hx
      simp [firstAboveQ, MSTApproximation.firstAbove, hx, hxr]
    · have hxr : ¬ (4 : ℝ) < (x : ℝ) := by exact_mod_cast hx
      simpa only [firstAboveQ, MSTApproximation.firstAbove, hx, hxr, ite_false, Rat.cast_mul] using
        congrArg (fun n => 1 + n) (ih (x * q))

theorem firstAboveQ_le (q x : ℚ) (fuel : ℕ) : firstAboveQ q x fuel ≤ fuel := by
  rw [firstAboveQ_cast]
  exact MSTApproximation.firstAbove_le _ _ _

def coarseHeight (k : ℕ) (j : Fin FinitePhase.count) : ℕ :=
  firstAboveQ coarseRatioQ (zetaQ * thetaQ j / (4 * k)) (coarseFuel k)

def fineHeight (k : ℕ) : ℕ :=
  firstAboveQ fineRatioQ (zetaQ / (4 * k)) (fineFuel k)

def heightTotal (k : ℕ) (j : Fin FinitePhase.count) : ℕ := coarseHeight k j + fineHeight k + 2
def heightFactor : ℕ := 61 * (100 + fineBlock) + 2
def heightBudget (n : ℕ) : ℕ := heightFactor * ell n

theorem fuel_bounds (n k : ℕ) (hkn : k ≤ n) :
    coarseFuel k + 1 ≤ (6101 : ℕ) * ell n ∧
      fineFuel k + 1 ≤ (61 * fineBlock + 1) * ell n := by
  have hl := log2_mono (show k + 1 ≤ n + 2 by omega)
  have he := ell_ge_one n
  unfold coarseFuel fineFuel ell at *
  constructor <;> nlinarith

theorem heightTotal_bound (n k : ℕ) (j : Fin FinitePhase.count) (hkn : k ≤ n) :
    heightTotal k j ≤ heightBudget n := by
  have hc := firstAboveQ_le coarseRatioQ (zetaQ * thetaQ j / (4 * k)) (coarseFuel k)
  have hf := firstAboveQ_le fineRatioQ (zetaQ / (4 * k)) (fineFuel k)
  have hb := fuel_bounds n k hkn
  unfold heightTotal coarseHeight fineHeight heightBudget heightFactor
  nlinarith [hb.1, hb.2]

noncomputable abbrev coarseGrid (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R)
    (j : Fin FinitePhase.count) : Grid :=
  MSTApproximation.generate k Structural.omega zeta (FinitePhase.theta j) R (coarseFuel k) hk
    (by norm_num [Structural.omega]) (by norm_num [zeta, zetaQ, cQ])
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (FinitePhase.theta_lower j)) hR

noncomputable abbrev fineGrid (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R) : Grid :=
  MSTApproximation.generate k (MSTApproximation.fineRatio nu) zeta 1 R (fineFuel k) hk
    (by norm_num [MSTApproximation.fineRatio, nu, nuQ, cQ])
    (by norm_num [zeta, zetaQ, cQ]) (by norm_num) hR

theorem coarseGrid_height (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R) (j : Fin FinitePhase.count) :
    (coarseGrid k hk R hR j).intervals = coarseHeight k j := by
  have h := firstAboveQ_cast coarseRatioQ (zetaQ * thetaQ j / (4 * k)) (coarseFuel k)
  have hx : ((zetaQ * thetaQ j / (4 * k) : ℚ) : ℝ) =
      relativeStart k zeta (FinitePhase.theta j) := by
    simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, thetaQ_cast,
      relativeStart, zeta]
  simpa only [coarseHeight, ratio_casts.1, hx] using h.symm

theorem fineGrid_height (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R) :
    (fineGrid k hk R hR).intervals = fineHeight k := by
  have h := firstAboveQ_cast fineRatioQ (zetaQ / (4 * k)) (fineFuel k)
  have hx : ((zetaQ / (4 * k) : ℚ) : ℝ) = relativeStart k zeta 1 := by
    simp [relativeStart, Rat.cast_div, Rat.cast_mul, zeta]
  simpa only [fineHeight, ratio_casts.2.1, hx] using h.symm

theorem grids_count (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) (R : ℝ) (hR : 0 < R)
    (j : Fin FinitePhase.count) :
    (coarseGrid k hk R hR j).intervals + 1 + ((fineGrid k hk R hR).intervals + 1) ≤
      heightFactor * (1 + Nat.log2 (n + 2)) := by
  rw [coarseGrid_height, fineGrid_height]
  have h := heightTotal_bound n k j hkn
  unfold heightTotal heightBudget ell at h
  omega

theorem coarseGrid_phase_scale (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R)
    (j : Fin FinitePhase.count) (i : ℕ) :
    (coarseGrid k hk R hR j).scale i = FinitePhase.scale ((zeta * R / k) / 4) j i := by
  exact MSTApproximation.generated_scale k Structural.omega zeta (FinitePhase.theta j) R
    (coarseFuel k) hk (by norm_num [Structural.omega])
      (by norm_num [zeta, zetaQ, cQ])
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (FinitePhase.theta_lower j)) hR i

theorem coarseGrid_endpoints (k : ℕ) (hk : 2 ≤ k) (R : ℝ) (hR : 0 < R) (j : Fin FinitePhase.count) :
    let g := coarseGrid k (by omega) R hR j
    g.first < (zeta * R / k) / 2 ∧ 4 * R < g.scale g.intervals ∧ g.scale g.intervals ≤ 4 * g.q * R := by
  have h := generated_endpoints k Structural.omega zeta (FinitePhase.theta j) R hk
    (by norm_num [Structural.omega]) (by norm_num [Structural.omega])
    (by norm_num [zeta, zetaQ, cQ]) (by norm_num [zeta, zetaQ, cQ])
    (FinitePhase.theta_lower j) (FinitePhase.theta_lt_omega j) hR coarseConstants
  rw [← coarseFuel_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem fineGrid_endpoints (k : ℕ) (hk : 2 ≤ k) (R : ℝ) (hR : 0 < R) :
    let g := fineGrid k (by omega) R hR
    g.first < (zeta * R / k) / 2 ∧ 4 * R < g.scale g.intervals ∧ g.scale g.intervals ≤ 4 * g.q * R := by
  have h := generated_endpoints k (MSTApproximation.fineRatio nu) zeta 1 R hk
    (by norm_num [MSTApproximation.fineRatio, nu, nuQ, cQ])
    (by norm_num [MSTApproximation.fineRatio, nu, nuQ, cQ])
    (by norm_num [zeta, zetaQ, cQ]) (by norm_num [zeta, zetaQ, cQ]) le_rfl
    (by norm_num [MSTApproximation.fineRatio, nu, nuQ, cQ]) hR fineConstants
  rw [← fineFuel_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end SteinerUpperBound.EstimatorParameters
