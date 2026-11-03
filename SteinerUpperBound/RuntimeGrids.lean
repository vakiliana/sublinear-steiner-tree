module

public import SteinerUpperBound.RuntimeScales
public import SteinerUpperBound.EstimatorParameters.Setup.IntegerLoops
public import SteinerUpperBound.MSTApproximation.GridProgram

@[expose] public section

noncomputable section

namespace SteinerUpperBound.RuntimeGrids

open QueryProgram MSTApproximation EstimatorParameters
open scoped Classical

variable {M Q : Type*}

structure Tables where
  coarse : Grid
  fine : Grid
  hop : ℕ
  radii : Vector ℝ (coarse.intervals + fine.intervals + 2)

def configuration (coarse fine : Grid) (hop : ℕ) : RuntimeScales.Config :=
  ⟨coarse.intervals + 1, coarse.first, coarse.q, fine.first, fine.q,
    deltaCoarse, deltaFine, hop⟩

def rho (t : Tables) (i : Fin (t.coarse.intervals + t.fine.intervals + 2)) : ℝ :=
  if i.val < t.coarse.intervals + 1 then deltaCoarse * t.coarse.scale i.val
  else deltaFine * t.fine.scale (i.val - (t.coarse.intervals + 1))

theorem configuration_radius (coarse fine : Grid) (hop i : ℕ) :
    RuntimeScales.radius (configuration coarse fine hop) i =
      (if i < coarse.intervals + 1 then deltaCoarse * coarse.scale i
        else deltaFine * fine.scale (i - (coarse.intervals + 1))) / hop := by
  by_cases h : i < coarse.intervals + 1 <;>
    simp [RuntimeScales.radius, configuration, Grid.scale, h, mul_assoc]

def hopProgram (k : ℕ) : Code M Q ℕ :=
  (Setup.logCode k).bind (fun j => .tick 0 (.pure (j + 1)))

def hopResult (k : ℕ) : Outcome ℕ :=
  ⟨Covers.hopCount k, 6 * Nat.log2 k + 5, 0, 0, 0⟩

theorem hop_evaluates (m : M → ℝ) (bits : Q → Bool) (k : ℕ) :
    Code.Evaluates m bits (hopProgram k) (hopResult k) := by
  intro F
  rw [hopProgram, Code.evaluate_bind, Setup.logCode_evaluates]
  simp only [Code.evaluate, Outcome.combine, Outcome.add, Outcome.pure, hopResult,
    Covers.hopCount, Nat.log2_eq_log_two]

def coarseProgram (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R)
    (phase : Fin FinitePhase.count) : Code M Q Grid :=
  gridProgram k Structural.omega zeta (FinitePhase.theta phase) R (coarseFuel k) hk
    (by norm_num [Structural.omega]) (by norm_num [zeta, zetaQ, cQ])
    (lt_of_lt_of_le zero_lt_one (FinitePhase.theta_lower phase)) hR

def fineProgram (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R) : Code M Q Grid :=
  gridProgram k (fineRatio nu) zeta 1 R (fineFuel k) hk
    (by norm_num [fineRatio, nu, nuQ, cQ]) (by norm_num [zeta, zetaQ, cQ]) (by norm_num) hR

def coarseResult (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R)
    (phase : Fin FinitePhase.count) : Outcome Grid :=
  ⟨coarseGrid k hk R hR phase,
    k + 11 + (indexResult Structural.omega (relativeStart k zeta (FinitePhase.theta phase))
      (coarseFuel k)).work, 0, 0, 0⟩

def fineResult (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R) : Outcome Grid :=
  ⟨fineGrid k hk R hR,
    k + 11 + (indexResult (fineRatio nu) (relativeStart k zeta 1) (fineFuel k)).work, 0, 0, 0⟩

theorem coarse_evaluates (m : M → ℝ) (bits : Q → Bool) (k : ℕ) (hk : 0 < k)
    (R : ℝ) (hR : 0 < R) (phase : Fin FinitePhase.count) :
    Code.Evaluates m bits (coarseProgram k hk R hR phase) (coarseResult k hk R hR phase) :=
  gridProgram_evaluates m bits _ _ _ _ _ _ _ _ _ _ _

theorem fine_evaluates (m : M → ℝ) (bits : Q → Bool) (k : ℕ) (hk : 0 < k)
    (R : ℝ) (hR : 0 < R) :
    Code.Evaluates m bits (fineProgram k hk R hR) (fineResult k hk R hR) :=
  gridProgram_evaluates m bits _ _ _ _ _ _ _ _ _ _ _

def program (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R)
    (phase : Fin FinitePhase.count) : Code M Q Tables :=
  (coarseProgram k hk R hR phase).bind (fun coarse =>
    (fineProgram k hk R hR).bind (fun fine =>
      (hopProgram k).bind (fun hop =>
        (RuntimeScales.program (configuration coarse fine hop)
          (coarse.intervals + fine.intervals + 2)).map (fun radii => ⟨coarse, fine, hop, radii⟩))))

def result (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R)
    (phase : Fin FinitePhase.count) : Outcome Tables :=
  let c := coarseResult k hk R hR phase
  let f := fineResult k hk R hR
  let h := hopResult k
  c.combine (f.combine (h.combine
    ((RuntimeScales.result (configuration c.value f.value h.value)
      (c.value.intervals + f.value.intervals + 2)).map (fun radii => ⟨c.value, f.value, h.value, radii⟩))))

theorem program_evaluates (m : M → ℝ) (bits : Q → Bool) (k : ℕ) (hk : 0 < k)
    (R : ℝ) (hR : 0 < R) (phase : Fin FinitePhase.count) :
    Code.Evaluates m bits (program k hk R hR phase) (result k hk R hR phase) := by
  intro F
  simp only [program, Code.evaluate_bind]
  rw [coarse_evaluates, fine_evaluates, hop_evaluates,
    Code.evaluate_map, RuntimeScales.program_evaluates]
  rfl

theorem get_radii (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R)
    (phase : Fin FinitePhase.count)
    (i : Fin ((result k hk R hR phase).value.coarse.intervals +
      (result k hk R hR phase).value.fine.intervals + 2)) :
    (result k hk R hR phase).value.radii.get i =
      rho (result k hk R hR phase).value i / Covers.hopCount k := by
  change Fin ((coarseGrid k hk R hR phase).intervals +
    (fineGrid k hk R hR).intervals + 2) at i
  dsimp only [result, coarseResult, fineResult, hopResult, Outcome.combine, Outcome.map]
  rw [RuntimeScales.get_result]
  exact configuration_radius _ _ _ _

theorem rho_pos (t : Tables) (i : Fin (t.coarse.intervals + t.fine.intervals + 2)) :
    0 < rho t i := by
  unfold rho
  split_ifs
  · exact mul_pos metric_scale_constants.1 (t.coarse.scale_pos _)
  · exact mul_pos metric_scale_constants.2.2.1 (t.fine.scale_pos _)

theorem length_bound (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (R : ℝ) (hR : 0 < R) (phase : Fin FinitePhase.count) :
    (result k hk R hR phase).value.coarse.intervals +
      (result k hk R hR phase).value.fine.intervals + 2 ≤ heightBudget n := by
  change (coarseGrid k hk R hR phase).intervals + (fineGrid k hk R hR).intervals + 2 ≤ _
  rw [coarseGrid_height, fineGrid_height]
  exact heightTotal_bound n k phase hkn

theorem counters (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R)
    (phase : Fin FinitePhase.count) :
    (result k hk R hR phase).metricQueries = 0 ∧
      (result k hk R hR phase).retentionQueries = 0 ∧
      (result k hk R hR phase).positiveReplies = 0 := by
  have h := RuntimeScales.counters
    (configuration (coarseGrid k hk R hR phase) (fineGrid k hk R hR) (Covers.hopCount k))
    ((coarseGrid k hk R hR phase).intervals + (fineGrid k hk R hR).intervals + 2)
  simpa only [result, coarseResult, fineResult, hopResult, Outcome.combine, Outcome.map,
    Nat.zero_add] using h

theorem work (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R)
    (phase : Fin FinitePhase.count) :
    let length := (coarseGrid k hk R hR phase).intervals + (fineGrid k hk R hR).intervals + 2
    (result k hk R hR phase).work ≤
      64 * (k + 1 + coarseFuel k + fineFuel k + Nat.log2 k + length ^ 2 + length) := by
  dsimp only
  have hc := indexResult_resources Structural.omega (relativeStart k zeta (FinitePhase.theta phase))
    (coarseFuel k)
  have hf := indexResult_resources (fineRatio nu) (relativeStart k zeta 1) (fineFuel k)
  have hr := RuntimeScales.work
    (configuration (coarseGrid k hk R hR phase) (fineGrid k hk R hR) (Covers.hopCount k))
    ((coarseGrid k hk R hR phase).intervals + (fineGrid k hk R hR).intervals + 2)
  dsimp only [result, coarseResult, fineResult, hopResult, Outcome.combine, Outcome.map]
  nlinarith

end SteinerUpperBound.RuntimeGrids
