module

public import SteinerUpperBound.EstimatorBootstrap
public import SteinerUpperBound.EstimatorClocks.Resources

/-!
# Unconditional bootstrap work

`preparedBudget n count W D` includes charged public setup, the inverse label array,
the random phase, both first-crossing grids and all radius rows, cache initialization,
and `32*(W+D+1)` for the actually capped factory. The frontend is unrestricted.
`prepared_expected_work` needs only `count≤n` and the positive runtime radius.

`program_expected_work` holds for arbitrary metric replies, including the branch
with nonpositive observed radius. It pays `3*count+5+4*preparedBudget`: the root row,
normalization tick, and the actual flooring simulation. `Code.accounted` bounds
simulated metric queries by ordinary work. No accuracy or cover event is used.

`preparedBudget_polylog` bounds startup by
`preparedFactor*(n+1)*ell n^2`, retaining the exact `32*(W+D+1)` term.
The factory-clock specializations give explicit `(n+1)*t n*ell n^(d+2)` bounds.
Their account hypotheses are inequalities between public natural numbers, not
performance hypotheses about the frontend.
-/

@[expose] public section

namespace SteinerUpperBound.EstimatorBootstrap

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

def gridBudget (n count : ℕ) : ℕ :=
  64 * (count + 1 + coarseFuel count + fineFuel count + ell n +
    heightBudget n ^ 2 + heightBudget n)

/-- Includes actual setup, inverse labels, phase draw, grid/radius arrays,
initial cache, and the unconditional capped factory work. -/
def preparedBudget (n count W D : ℕ) : ℕ :=
  Setup.setupFactor * ell n + n + 4 * count + 13 +
    gridBudget n count + count * heightBudget n + 32 * (W + D + 1)

def preparedFactor : ℕ :=
  Setup.setupFactor + 64 * (heightFactor ^ 2 + heightFactor + 6104 + 61 * fineBlock) +
    heightFactor + 100

private theorem tick_work {M Q R : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (ticks : ℕ) :
    (Code.tick ticks p).evaluate m bits (fun o => (o.work : ℝ)) =
      ((ticks + 1 : ℕ) : ℝ) + p.evaluate m bits (fun o => (o.work : ℝ)) := by
  simp only [Code.evaluate, Outcome.add, Nat.cast_add, Code.evaluate_add, Code.evaluate_const]

private theorem expected_metric_le_work {M Q R : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) :
    p.evaluate m bits (fun o => (o.metricQueries : ℝ)) ≤
      p.evaluate m bits (fun o => (o.work : ℝ)) := by
  rw [← Code.compile_expect, ← Code.compile_expect]
  apply (p.compile m).law.expect_mono
  intro seed
  dsimp only
  have h := (Code.accounted m bits p seed).1
  exact_mod_cast (show (((p.compile m).tree seed).output bits).metricQueries ≤
      (((p.compile m).tree seed).output bits).work by omega)

theorem grids_work_le (n count : ℕ) (hcount : 0 < count) (hcn : count ≤ n)
    (R : ℝ) (hR : 0 < R) (phase : Fin FinitePhase.count) :
    (RuntimeGrids.result count hcount R hR phase).work ≤ gridBudget n count := by
  have hw := RuntimeGrids.work count hcount R hR phase
  have hh := RuntimeGrids.length_bound n count hcount hcn R hR phase
  change (coarseGrid count hcount R hR phase).intervals +
    (fineGrid count hcount R hR).intervals + 2 ≤ heightBudget n at hh
  have hlog : Nat.log2 count ≤ ell n := by
    have h := log2_mono (show count ≤ n + 2 by omega)
    unfold ell
    omega
  apply hw.trans
  unfold gridBudget
  gcongr

variable {n k : ℕ}

theorem atTables_expected_work (p : PublicParameters) (label : Vector (Fin n) (k + 1))
    (root : Fin (k + 1)) (W D : ℕ) (frontend : Frontend n k)
    (inverse : Vector (Fin (k + 1)) n) (tables : Tables) (m : Sym2 (Fin n) → ℝ) :
    (atTables p label root W D frontend inverse tables).evaluate m Code.emptyBits (fun o => (o.work : ℝ)) ≤
      ((k + 1) * (tables.coarse.intervals + tables.fine.intervals + 2) + 6 +
        32 * (W + D + 1) : ℕ) := by
  have h := FactoryExecution.program_expected_work
    (RuntimeWorld.configuration p label tables) (LabelledFactory.initialCache root) W D
    (frontend p inverse tables (LabelledFactory.initialCache root)) m
  rw [atTables, tick_work, Code.evaluate_map]
  simp only [Outcome.map]
  push_cast at h ⊢
  linarith

/-- Abstracting the result keeps dependent radius-vector indices out of kernel reduction. -/
private theorem tables_work_of_evaluates (p : PublicParameters) (label : Vector (Fin n) (k + 1))
    (root : Fin (k + 1)) (W D : ℕ) (frontend : Frontend n k)
    (inverse : Vector (Fin (k + 1)) n) (grids : Code (Sym2 (Fin n)) Empty Tables)
    (out : Outcome Tables) (m : Sym2 (Fin n) → ℝ)
    (he : Code.Evaluates m Code.emptyBits grids out)
    (hg : out.work ≤ gridBudget n (k + 1))
    (hh : out.value.coarse.intervals + out.value.fine.intervals + 2 ≤ heightBudget n) :
    (Code.tick 4 (grids.bind (atTables p label root W D frontend inverse))).evaluate m Code.emptyBits
      (fun o => (o.work : ℝ)) ≤
        (5 + gridBudget n (k + 1) + (k + 1) * heightBudget n + 6 + 32 * (W + D + 1) : ℕ) := by
  have ht := atTables_expected_work p label root W D frontend inverse out.value m
  have hc : (k + 1) * (out.value.coarse.intervals + out.value.fine.intervals + 2) ≤
      (k + 1) * heightBudget n := Nat.mul_le_mul_left _ hh
  have hgR : (out.work : ℝ) ≤ gridBudget n (k + 1) := by exact_mod_cast hg
  have ht' : (atTables p label root W D frontend inverse out.value).evaluate m Code.emptyBits
      (fun o => (o.work : ℝ)) ≤
      ((k + 1) * heightBudget n + 6 + 32 * (W + D + 1) : ℕ) :=
    ht.trans (by exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right hc 6) (32 * (W + D + 1)))
  rw [tick_work, Code.evaluate_work_bind, he]
  have hsum := add_le_add (show (5 : ℝ) ≤ 5 from le_rfl) (add_le_add hgR ht')
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd, add_assoc] using hsum

theorem atPhase_expected_work (p : PublicParameters) (label : Vector (Fin n) (k + 1))
    (root : Fin (k + 1)) (W D : ℕ) (frontend : Frontend n k)
    (inverse : Vector (Fin (k + 1)) n) (R : ℝ) (hR : 0 < R)
    (phase : Fin FinitePhase.count) (hkn : k + 1 ≤ n) (m : Sym2 (Fin n) → ℝ) :
    (atPhase p label root W D frontend inverse R hR phase).evaluate m Code.emptyBits
      (fun o => (o.work : ℝ)) ≤
        (5 + gridBudget n (k + 1) + (k + 1) * heightBudget n + 6 + 32 * (W + D + 1) : ℕ) := by
  exact tables_work_of_evaluates p label root W D frontend inverse
    (RuntimeGrids.program (k + 1) (by omega) R hR phase) (RuntimeGrids.result (k + 1) (by omega) R hR phase) m
    (RuntimeGrids.program_evaluates m Code.emptyBits (k + 1) (by omega) R hR phase)
    (grids_work_le n (k + 1) (by omega) hkn R hR phase)
    (RuntimeGrids.length_bound n (k + 1) (by omega) hkn R hR phase)

theorem prepared_expected_work (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (W D : ℕ) (frontend : Frontend n k) (R : ℝ) (hR : 0 < R) (hkn : k + 1 ≤ n)
    (m : Sym2 (Fin n) → ℝ) :
    (prepared label root W D frontend R hR).evaluate m Code.emptyBits (fun o => (o.work : ℝ)) ≤
      (preparedBudget n (k + 1) W D : ℕ) := by
  have hs : ((Setup.setupPlan n (k + 1)).work : ℝ) ≤ (Setup.setupFactor * ell n : ℕ) := by
    exact_mod_cast (Setup.setupPlan_work_le n (k + 1)).trans (Setup.workBudget_polylog n)
  have hi : ((PublicTerminals.inverseResult label root).work : ℝ) ≤ (n + 4 * (k + 1) + 1 : ℕ) := by
    exact_mod_cast PublicTerminals.inverse_work label root
  have hp := (Law.uniform (Fin FinitePhase.count)).expect_mono (fun phase =>
    atPhase_expected_work (parameters n (k + 1)) label root W D frontend
      (PublicTerminals.inverseResult label root).value R hR phase hkn m)
  simp only [Law.expect_const] at hp
  rw [prepared, Code.evaluate_work_bind, setupProgram_evaluates,
    Code.evaluate_work_bind, PublicTerminals.inverse_evaluates]
  change ((Setup.setupPlan n (k + 1)).work : ℝ) +
    (((PublicTerminals.inverseResult label root).work : ℝ) +
      (Law.uniform (Fin FinitePhase.count)).expect (fun phase =>
        (atPhase (parameters n (k + 1)) label root W D frontend
          (PublicTerminals.inverseResult label root).value R hR phase).evaluate m Code.emptyBits
            (fun o => ((1 + o.work : ℕ) : ℝ)))) ≤ _
  simp only [Nat.cast_add, Nat.cast_one, Code.evaluate_add, Code.evaluate_const,
    Law.expect_add, Law.expect_const]
  unfold preparedBudget
  push_cast at hs hi hp ⊢
  linarith

theorem prepared_expected_work_of_injective (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (root : Fin (k + 1))
    (W D : ℕ) (frontend : Frontend n k) (R : ℝ) (hR : 0 < R) (m : Sym2 (Fin n) → ℝ) :
    (prepared label root W D frontend R hR).evaluate m Code.emptyBits (fun o => (o.work : ℝ)) ≤
      (preparedBudget n (k + 1) W D : ℕ) :=
  prepared_expected_work label root W D frontend R hR (PublicTerminals.length_le label hinj) m

/-- Work is bounded even for arbitrary metric answers and the nonpositive-radius branch.
No coverage, statistical event, or frontend performance assumption is used. -/
theorem program_expected_work (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (W D : ℕ) (frontend : Frontend n k) (hkn : k + 1 ≤ n) (m : Sym2 (Fin n) → ℝ) :
    (program label root W D frontend).evaluate m Code.emptyBits (fun o => (o.work : ℝ)) ≤
      (3 * (k + 1) + 5 + 4 * preparedBudget n (k + 1) W D : ℕ) := by
  let R := rowValue m (label.get root) label.toList 0
  let lam := floorScale label.toList.length R
  let next : Code (Sym2 (Fin n)) Empty ℝ :=
    if hR : 0 < R then prepared label root W D frontend R hR else .pure 0
  let flooredWeight := fun q => floorResponse lam q (m q)
  have hw : next.evaluate flooredWeight Code.emptyBits (fun o => (o.work : ℝ)) ≤
      (preparedBudget n (k + 1) W D : ℕ) := by
    dsimp only [next]
    split_ifs with hR
    · exact prepared_expected_work label root W D frontend R hR hkn flooredWeight
    · simp only [Code.evaluate, Outcome.pure, Nat.cast_zero]
      exact Nat.cast_nonneg _
  have hm := expected_metric_le_work flooredWeight Code.emptyBits next
  have hf : (next.mapMetric (floorResponse lam) 2).evaluate m Code.emptyBits (fun o => (o.work : ℝ)) ≤
      4 * (preparedBudget n (k + 1) W D : ℕ) := by
    rw [Code.mapMetric_work]
    change next.evaluate flooredWeight Code.emptyBits (fun o => (o.work : ℝ)) +
      (3 : ℝ) * next.evaluate flooredWeight Code.emptyBits (fun o => (o.metricQueries : ℝ)) ≤ _
    linarith
  rw [program, EstimatorParameters.normalize, Code.evaluate_work_bind, rootRow_evaluates]
  change ((3 * label.toList.length + 1 : ℕ) : ℝ) +
    (Code.tick 3 (next.mapMetric (floorResponse lam) 2)).evaluate m Code.emptyBits
      (fun o => (o.work : ℝ)) ≤ _
  rw [tick_work]
  simp only [Vector.length_toList, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  linarith

theorem program_expected_work_of_injective (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (root : Fin (k + 1))
    (W D : ℕ) (frontend : Frontend n k) (m : Sym2 (Fin n) → ℝ) :
    (program label root W D frontend).evaluate m Code.emptyBits (fun o => (o.work : ℝ)) ≤
      (3 * (k + 1) + 5 + 4 * preparedBudget n (k + 1) W D : ℕ) :=
  program_expected_work label root W D frontend (PublicTerminals.length_le label hinj) m

theorem preparedBudget_polylog (n count W D : ℕ) (hcn : count ≤ n) :
    preparedBudget n count W D ≤
      preparedFactor * (n + 1) * ell n ^ 2 + 32 * (W + D + 1) := by
  let X := (n + 1) * ell n ^ 2
  have he := ell_ge_one n
  have he2 : ell n ≤ ell n ^ 2 := by nlinarith
  have hNX : n + 1 ≤ X := by
    calc
      n + 1 = (n + 1) * 1 := by omega
      _ ≤ X := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (pow_pos (ell_pos n) 2))
  have hSqX : ell n ^ 2 ≤ X := by
    calc
      ell n ^ 2 = 1 * ell n ^ 2 := by omega
      _ ≤ X := Nat.mul_le_mul_right _ (by omega)
  have hEX := he2.trans hSqX
  have hcX : count + 1 ≤ X := (show count + 1 ≤ n + 1 by omega).trans hNX
  have hf := fuel_bounds n count hcn
  have hfuels : coarseFuel count + fineFuel count ≤ (6102 + 61 * fineBlock) * X := by
    have hsmall : coarseFuel count + fineFuel count ≤ (6102 + 61 * fineBlock) * ell n := by
      nlinarith [hf.1, hf.2]
    exact hsmall.trans (Nat.mul_le_mul_left _ hEX)
  have hH : heightBudget n ≤ heightFactor * X := Nat.mul_le_mul_left _ hEX
  have hHsq : heightBudget n ^ 2 ≤ heightFactor ^ 2 * X := by
    simpa only [heightBudget, mul_pow] using Nat.mul_le_mul_left (heightFactor ^ 2) hSqX
  have hcache : count * heightBudget n ≤ heightFactor * X := by
    calc
      count * heightBudget n = heightFactor * (count * ell n) := by unfold heightBudget; ring
      _ ≤ heightFactor * ((n + 1) * ell n ^ 2) := by gcongr; omega
      _ = _ := rfl
  have hgrid : gridBudget n count ≤
      64 * (heightFactor ^ 2 + heightFactor + 6104 + 61 * fineBlock) * X := by
    unfold gridBudget
    calc
      _ ≤ 64 * ((heightFactor ^ 2 + heightFactor + 6104 + 61 * fineBlock) * X) := by
        apply Nat.mul_le_mul_left
        nlinarith
      _ = _ := by ring
  have hsetup : Setup.setupFactor * ell n ≤ Setup.setupFactor * X := Nat.mul_le_mul_left _ hEX
  have hinverse : n + 4 * count + 13 ≤ 13 * X := by
    have hsmall : n + 4 * count + 13 ≤ 13 * (n + 1) := by omega
    exact hsmall.trans (Nat.mul_le_mul_left _ hNX)
  calc
    preparedBudget n count W D =
        Setup.setupFactor * ell n + (n + 4 * count + 13) + gridBudget n count +
          count * heightBudget n + 32 * (W + D + 1) := by unfold preparedBudget; ring
    _ ≤ Setup.setupFactor * X + 13 * X +
        64 * (heightFactor ^ 2 + heightFactor + 6104 + 61 * fineBlock) * X +
          heightFactor * X + 32 * (W + D + 1) :=
      Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hsetup hinverse) hgrid) hcache) _
    _ ≤ preparedFactor * X + 32 * (W + D + 1) := by unfold preparedFactor; nlinarith
    _ = _ := by dsimp [X]; ring

theorem preparedBudget_factory_polylog (n count K d workAccount positiveAccount : ℕ) (hcn : count ≤ n)
    (hw : workAccount ≤ K * (n + 1) * t n * ell n ^ d)
    (hp : positiveAccount ≤ K * t n * ell n ^ d) :
    preparedBudget n count (EstimatorClocks.factory count workAccount positiveAccount).clock.workBudget
        (EstimatorClocks.factory count workAccount positiveAccount).clock.disclosureBudget ≤
      (preparedFactor + 25600000 * (K + 1)) * (n + 1) * t n * ell n ^ (d + 2) := by
  let X := (n + 1) * t n * ell n ^ (d + 2)
  have ht : 1 ≤ t n := t_pos n
  have hO : preparedFactor * (n + 1) * ell n ^ 2 ≤ preparedFactor * X := by
    calc
      _ = preparedFactor * (n + 1) * 1 * ell n ^ 2 := by ring
      _ ≤ preparedFactor * (n + 1) * t n * ell n ^ (d + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ ht) (ell_power_le n 2 (d + 2) (by omega))
      _ = _ := by dsimp [X]; ring
  have hF := EstimatorClocks.factory_budget_polylog n count K d workAccount positiveAccount hcn hw hp
  have hF' : (EstimatorClocks.factory count workAccount positiveAccount).clock.workBudget +
        (EstimatorClocks.factory count workAccount positiveAccount).clock.disclosureBudget + 1 ≤
      800000 * (K + 1) * X := by
    calc
      _ ≤ 800000 * (K + 1) * (n + 1) * t n * ell n ^ d := hF
      _ ≤ 800000 * (K + 1) * (n + 1) * t n * ell n ^ (d + 2) :=
        Nat.mul_le_mul_left _ (ell_power_le n d (d + 2) (by omega))
      _ = _ := by dsimp [X]; ring
  calc
    _ ≤ preparedFactor * (n + 1) * ell n ^ 2 +
        32 * ((EstimatorClocks.factory count workAccount positiveAccount).clock.workBudget +
          (EstimatorClocks.factory count workAccount positiveAccount).clock.disclosureBudget + 1) :=
      preparedBudget_polylog n count _ _ hcn
    _ ≤ preparedFactor * X + 32 * (800000 * (K + 1) * X) :=
      Nat.add_le_add hO (Nat.mul_le_mul_left _ hF')
    _ = _ := by dsimp [X]; ring

theorem program_expected_work_factory_polylog (label : Vector (Fin n) (k + 1))
    (root : Fin (k + 1)) (frontend : Frontend n k) (hkn : k + 1 ≤ n)
    (K d workAccount positiveAccount : ℕ)
    (hw : workAccount ≤ K * (n + 1) * t n * ell n ^ d)
    (hp : positiveAccount ≤ K * t n * ell n ^ d) (m : Sym2 (Fin n) → ℝ) :
    (program label root
      (EstimatorClocks.factory (k + 1) workAccount positiveAccount).clock.workBudget
      (EstimatorClocks.factory (k + 1) workAccount positiveAccount).clock.disclosureBudget frontend).evaluate
        m Code.emptyBits (fun o => (o.work : ℝ)) ≤
      ((4 * (preparedFactor + 25600000 * (K + 1)) + 5) * (n + 1) * t n * ell n ^ (d + 2) : ℕ) := by
  have h := program_expected_work label root
    (EstimatorClocks.factory (k + 1) workAccount positiveAccount).clock.workBudget
    (EstimatorClocks.factory (k + 1) workAccount positiveAccount).clock.disclosureBudget frontend hkn m
  have hb := preparedBudget_factory_polylog n (k + 1) K d workAccount positiveAccount hkn hw hp
  let X := (n + 1) * t n * ell n ^ (d + 2)
  have hnX : n + 1 ≤ X := by
    calc
      n + 1 = (n + 1) * 1 * 1 := by ring
      _ ≤ X := Nat.mul_le_mul (Nat.mul_le_mul_left _ (show 1 ≤ t n from t_pos n))
        (Nat.succ_le_of_lt (pow_pos (ell_pos n) (d + 2)))
  have hr : 3 * (k + 1) + 5 ≤ 5 * X := by omega
  have hbound :
      3 * (k + 1) + 5 + 4 *
        preparedBudget n (k + 1)
          (EstimatorClocks.factory (k + 1) workAccount positiveAccount).clock.workBudget
          (EstimatorClocks.factory (k + 1) workAccount positiveAccount).clock.disclosureBudget ≤
      (4 * (preparedFactor + 25600000 * (K + 1)) + 5) *
        (n + 1) * t n * ell n ^ (d + 2) := by
    have hb' : preparedBudget n (k + 1)
        (EstimatorClocks.factory (k + 1) workAccount positiveAccount).clock.workBudget
        (EstimatorClocks.factory (k + 1) workAccount positiveAccount).clock.disclosureBudget ≤
      (preparedFactor + 25600000 * (K + 1)) * X := by simpa only [X, Nat.mul_assoc] using hb
    calc
      _ ≤ 5 * X + 4 * ((preparedFactor + 25600000 * (K + 1)) * X) := by omega
      _ = _ := by dsimp [X]; ring
  exact h.trans (by exact_mod_cast hbound)

end SteinerUpperBound.EstimatorBootstrap
