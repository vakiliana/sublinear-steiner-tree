module

public import SteinerUpperBound.ConcreteEstimator
public import SteinerUpperBound.ConcreteEstimator.Step.Resources
public import SteinerUpperBound.EstimatorFrontend.Resources

/-!
# Unconditional resources of the fully concrete frontend

`frontendFactor K = EstimatorFrontend.Resources.polylogFactor (2*K+1) 25`
is a fixed executable natural constant, independent of `n` and `d`.
For literal raw saving accounts `AW=K*(n+1)*t n*ell n^d` and
`AP=K*t n*ell n^d`, the actual frontend has expected ordinary work at most
`frontendFactor K*(n+1)*t n*ell n^(d+140)` and positive replies at most
`frontendFactor K*t n*ell n^(d+140)`.

The real per-step `scaleProgram` costs `2*i+3`. `Step.saving_resources` includes
this cost, the nine-operation clock selector, and sixteen-operation flattening.
`scale_overhead_absorbed` bounds the scale cost by the original stage clock;
the analytic doubled account `2*AW+1` therefore suffices. The runtime still uses
the original raw accounts: no constructor or runtime budget is changed.

`frontend_expected` is uniform over correct incoming caches under fixed metric
bits and fine-root truths. `frontend_expected_on_support` derives the initial cache
and root truths from actual factory support. `frontend_mixed_expected` uses exactly
the law with `RuntimeWorld.configuration (parameters n (k+1)) label tables` and
`LabelledFactory.initialCache root`. It assumes only valid enumeration, inverse-left,
and public table-height bounds: no performance, cover, phase, calibration, or
accuracy event is supplied.
-/

@[expose] public section

namespace SteinerUpperBound.ConcreteEstimator

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

def frontendFactor (K : ℕ) : ℕ :=
  EstimatorFrontend.Resources.polylogFactor (2 * K + 1) 25

theorem scale_overhead_absorbed (n AW AP : ℕ) :
    (EstimatorClocks.stage n AW AP).workBudget + 25 + 2 * heightBudget n + 3 ≤
      (EstimatorClocks.stage n (2 * AW + 1) AP).workBudget + 25 := by
  have hbase : 2 * heightBudget n + 3 ≤ EstimatorClocks.amplification * (heightBudget n + 1) := by
    unfold EstimatorClocks.amplification
    omega
  have hmul : EstimatorClocks.amplification * (heightBudget n + 1) ≤
      EstimatorClocks.amplification * (heightBudget n + 1) * (AW + 1) := by
    have h := Nat.mul_le_mul_left (EstimatorClocks.amplification * (heightBudget n + 1))
      (show 1 ≤ AW + 1 by omega)
    simpa only [mul_one] using h
  have hs : 2 * heightBudget n + 3 ≤ (EstimatorClocks.stage n AW AP).workBudget := by
    simpa only [EstimatorClocks.stage, EstimatorClocks.byHeight] using hbase.trans hmul
  have hd : (EstimatorClocks.stage n (2 * AW + 1) AP).workBudget =
      2 * (EstimatorClocks.stage n AW AP).workBudget := by
    simp only [EstimatorClocks.stage, EstimatorClocks.byHeight]
    ring
  rw [hd]
  omega

private theorem doubled_accounts (n K d : ℕ) :
    2 * (K * (n + 1) * t n * ell n ^ d) + 1 ≤
        (2 * K + 1) * (n + 1) * t n * ell n ^ d ∧
      K * t n * ell n ^ d ≤ (2 * K + 1) * t n * ell n ^ d := by
  have hx : 1 ≤ (n + 1) * t n * ell n ^ d := Nat.succ_le_of_lt
    (mul_pos (mul_pos (by omega) (t_pos n)) (pow_pos (ell_pos n) d))
  constructor
  · nlinarith
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (show K ≤ 2 * K + 1 by omega))

theorem frontend_degree_le (d : ℕ) :
    EstimatorFrontend.Resources.polylogDegree d ≤ d + 140 := by
  unfold EstimatorFrontend.Resources.polylogDegree
  exact max_le (by omega) (by omega)

theorem frontend_clocked_budget (n K d : ℕ) :
    EstimatorFrontend.Resources.workBudget n
        ((EstimatorClocks.stage n (2 * (K * (n + 1) * t n * ell n ^ d) + 1)
          (K * t n * ell n ^ d)).workBudget + 25) ≤
        frontendFactor K * (n + 1) * t n * ell n ^ (d + 140) ∧
      EstimatorFrontend.Resources.positiveBudget n
        ((EstimatorClocks.stage n (2 * (K * (n + 1) * t n * ell n ^ d) + 1)
          (K * t n * ell n ^ d)).disclosureBudget + 1) ≤
        frontendFactor K * t n * ell n ^ (d + 140) := by
  obtain ⟨hw, hp⟩ := doubled_accounts n K d
  have h := EstimatorFrontend.Resources.clocked_budgets_polylog n (2 * K + 1) d
    (2 * (K * (n + 1) * t n * ell n ^ d) + 1) (K * t n * ell n ^ d) 25 hw hp
  constructor
  · apply h.1.trans
    exact Nat.mul_le_mul_left _ (ell_power_le n _ _ (frontend_degree_le d))
  · apply h.2.trans
    exact Nat.mul_le_mul_left _ (ell_power_le n _ _ (frontend_degree_le d))

variable {n k : ℕ}

noncomputable local instance concreteResourcesVertexDecEq : DecidableEq (Fin n) := Classical.decEq _
noncomputable local instance concreteResourcesLabelDecEq : DecidableEq (Fin (k + 1)) := Classical.decEq _
noncomputable local instance concreteResourcesCoordinateDecEq (tables : Tables) :
    DecidableEq (RuntimeWorld.Coordinate tables k) := Classical.decEq _

private theorem frontend_expected_of_step (I : Instance (Fin n))
    (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get) (root : Fin (k + 1))
    (tables : Tables) (inverse : Vector (Fin (k + 1)) n) (K d : ℕ)
    (bits : RuntimeWorld.Coordinate tables k → Bool)
    (hcoarse : tables.coarse.intervals + 1 ≤ heightBudget n)
    (hfine : tables.fine.intervals ≤ heightBudget n)
    (hroot : ∀ i < tables.fine.intervals,
      bits (RuntimeWorld.fineKey tables inverse i (label.get root)) = true)
    (hs : EstimatorFrontend.Resources.SavingResources I bits
      (step label root (parameters n (k + 1)) inverse tables
        (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d))
      ((EstimatorClocks.stage n (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d)).workBudget +
        25 + 2 * heightBudget n + 3)
      ((EstimatorClocks.stage n (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d)).disclosureBudget + 1))
    (cache : Cache (RuntimeWorld.Coordinate tables k)) (hc : Cache.Correct bits cache) :
    (frontend label root (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d)
      (parameters n (k + 1)) inverse tables cache).evaluate I.weight bits (fun o => (o.work : ℝ)) ≤
        (frontendFactor K * (n + 1) * t n * ell n ^ (d + 140) : ℕ) ∧
      (frontend label root (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d)
        (parameters n (k + 1)) inverse tables cache).evaluate I.weight bits
          (fun o => (o.positiveReplies : ℝ)) ≤
        (frontendFactor K * t n * ell n ^ (d + 140) : ℕ) := by
  have hstep : EstimatorFrontend.Resources.SavingResources I bits
      (step label root (parameters n (k + 1)) inverse tables
        (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d))
      ((EstimatorClocks.stage n (2 * (K * (n + 1) * t n * ell n ^ d) + 1)
        (K * t n * ell n ^ d)).workBudget + 25)
      ((EstimatorClocks.stage n (2 * (K * (n + 1) * t n * ell n ^ d) + 1)
        (K * t n * ell n ^ d)).disclosureBudget + 1) := by
    refine ⟨?_, hs.positive, hs.cache⟩
    intro i c hc
    exact (hs.work i c hc).trans (by
      exact_mod_cast scale_overhead_absorbed n (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d))
  have h := EstimatorFrontend.Resources.program_expected I bits label hinj root inverse
    (step label root (parameters n (k + 1)) inverse tables
      (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d)) _ _ hstep hcoarse hfine hroot cache hc
  have hb := frontend_clocked_budget n K d
  exact ⟨h.1.trans (by exact_mod_cast hb.1), h.2.trans (by exact_mod_cast hb.2)⟩

private theorem frontend_mixed_of_step (I : Instance (Fin n))
    (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get) (root : Fin (k + 1))
    (tables : Tables) (inverse : Vector (Fin (k + 1)) n)
    (hleft : ∀ j, inverse.get (label.get j) = j) (K d : ℕ)
    (hcoarse : tables.coarse.intervals + 1 ≤ heightBudget n)
    (hfine : tables.fine.intervals ≤ heightBudget n)
    (hs : ∀ bits, 0 <
      (Covers.OracleProgram.bits (RuntimeWorld.configuration (parameters n (k + 1)) label tables)
        I.weight (LabelledFactory.initialCache root)).mass bits →
      EstimatorFrontend.Resources.SavingResources I bits
        (step label root (parameters n (k + 1)) inverse tables
          (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d))
        ((EstimatorClocks.stage n (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d)).workBudget +
          25 + 2 * heightBudget n + 3)
        ((EstimatorClocks.stage n (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d)).disclosureBudget + 1)) :
    (Covers.OracleProgram.bits (RuntimeWorld.configuration (parameters n (k + 1)) label tables)
      I.weight (LabelledFactory.initialCache root)).expect (fun bits =>
        (frontend label root (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d)
          (parameters n (k + 1)) inverse tables (LabelledFactory.initialCache root)).evaluate
            I.weight bits (fun o => (o.work : ℝ))) ≤
        (frontendFactor K * (n + 1) * t n * ell n ^ (d + 140) : ℕ) ∧
      (Covers.OracleProgram.bits (RuntimeWorld.configuration (parameters n (k + 1)) label tables)
        I.weight (LabelledFactory.initialCache root)).expect (fun bits =>
          (frontend label root (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d)
            (parameters n (k + 1)) inverse tables (LabelledFactory.initialCache root)).evaluate
              I.weight bits (fun o => (o.positiveReplies : ℝ))) ≤
        (frontendFactor K * t n * ell n ^ (d + 140) : ℕ) := by
  let mu := Covers.OracleProgram.bits (RuntimeWorld.configuration (parameters n (k + 1)) label tables)
    I.weight (LabelledFactory.initialCache root)
  have hpoint bits (hb : 0 < mu.mass bits) :=
    frontend_expected_of_step I label hinj root tables inverse K d bits hcoarse hfine
      (fun i _ => RuntimeWorld.fine_root (parameters n (k + 1)) label tables inverse hleft root I.weight bits hb i)
      (hs bits hb) (LabelledFactory.initialCache root)
      (RuntimeWorld.cache_on_support (parameters n (k + 1)) label tables root I.weight bits hb)
  exact ⟨(mu.expect_mono_support (fun bits hb => (hpoint bits hb).1)).trans_eq (Law.expect_const _ _),
    (mu.expect_mono_support (fun bits hb => (hpoint bits hb).2)).trans_eq (Law.expect_const _ _)⟩

theorem step_resources_public (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (root : Fin (k + 1)) (tables : Tables) (inverse : Vector (Fin (k + 1)) n)
    (AW AP : ℕ) (hheight : tables.coarse.intervals + 1 ≤ heightBudget n)
    (bits : RuntimeWorld.Coordinate tables k → Bool) :
    EstimatorFrontend.Resources.SavingResources I bits
      (step label root (parameters n (k + 1)) inverse tables AW AP)
      ((EstimatorClocks.stage n AW AP).workBudget + 25 + 2 * heightBudget n + 3)
      ((EstimatorClocks.stage n AW AP).disclosureBudget + 1) := by
  have hTnative : @Finset.image (Fin (k + 1)) (Fin n) (instDecidableEqFin n)
      label.get Finset.univ = I.terminals := by
    ext x
    simpa only [Finset.mem_image, Finset.mem_univ, true_and] using Finset.ext_iff.mp hT x
  simpa only [Step.workBound_public, Step.positiveBound_public] using
    Step.saving_resources I bits label root (parameters n (k + 1)) inverse AW AP hinj hTnative hheight

/-- Fixed-oracle accounts for the fully actual concrete frontend, uniform over
every correct incoming cache. No saving-performance or cover event is assumed. -/
theorem frontend_expected (I : Instance (Fin n))
    (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get)
    (hT : Finset.univ.image label.get = I.terminals) (root : Fin (k + 1))
    (tables : Tables) (inverse : Vector (Fin (k + 1)) n) (K d : ℕ)
    (bits : RuntimeWorld.Coordinate tables k → Bool)
    (hcoarse : tables.coarse.intervals + 1 ≤ heightBudget n)
    (hfine : tables.fine.intervals ≤ heightBudget n)
    (hroot : ∀ i < tables.fine.intervals,
      bits (RuntimeWorld.fineKey tables inverse i (label.get root)) = true)
    (cache : Cache (RuntimeWorld.Coordinate tables k)) (hc : Cache.Correct bits cache) :
    (frontend label root (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d)
      (parameters n (k + 1)) inverse tables cache).evaluate I.weight bits (fun o => (o.work : ℝ)) ≤
        (frontendFactor K * (n + 1) * t n * ell n ^ (d + 140) : ℕ) ∧
      (frontend label root (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d)
        (parameters n (k + 1)) inverse tables cache).evaluate I.weight bits
          (fun o => (o.positiveReplies : ℝ)) ≤
        (frontendFactor K * t n * ell n ^ (d + 140) : ℕ) :=
  frontend_expected_of_step I label hinj root tables inverse K d bits hcoarse hfine hroot
    (step_resources_public I label hinj hT root tables inverse _ _ hcoarse bits) cache hc

theorem frontend_expected_on_support (I : Instance (Fin n))
    (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get)
    (hT : Finset.univ.image label.get = I.terminals) (root : Fin (k + 1))
    (tables : Tables) (inverse : Vector (Fin (k + 1)) n)
    (hleft : ∀ j, inverse.get (label.get j) = j) (K d : ℕ)
    (hcoarse : tables.coarse.intervals + 1 ≤ heightBudget n)
    (hfine : tables.fine.intervals ≤ heightBudget n)
    (bits : RuntimeWorld.Coordinate tables k → Bool)
    (hb : 0 < (Covers.OracleProgram.bits
      (RuntimeWorld.configuration (parameters n (k + 1)) label tables) I.weight
        (LabelledFactory.initialCache root)).mass bits) :
    (frontend label root (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d)
      (parameters n (k + 1)) inverse tables (LabelledFactory.initialCache root)).evaluate
        I.weight bits (fun o => (o.work : ℝ)) ≤
        (frontendFactor K * (n + 1) * t n * ell n ^ (d + 140) : ℕ) ∧
      (frontend label root (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d)
        (parameters n (k + 1)) inverse tables (LabelledFactory.initialCache root)).evaluate
          I.weight bits (fun o => (o.positiveReplies : ℝ)) ≤
        (frontendFactor K * t n * ell n ^ (d + 140) : ℕ) :=
  frontend_expected I label hinj hT root tables inverse K d bits hcoarse hfine
    (fun i _ => RuntimeWorld.fine_root (parameters n (k + 1)) label tables inverse hleft root I.weight bits hb i)
    (LabelledFactory.initialCache root)
    (RuntimeWorld.cache_on_support (parameters n (k + 1)) label tables root I.weight bits hb)

/-- Unconditional accounts under the actual cached factory law. Cache consistency
and root truths are needed only on its positive support and are proved internally. -/
theorem frontend_mixed_expected (I : Instance (Fin n))
    (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get)
    (hT : Finset.univ.image label.get = I.terminals) (root : Fin (k + 1))
    (tables : Tables) (inverse : Vector (Fin (k + 1)) n)
    (hleft : ∀ j, inverse.get (label.get j) = j) (K d : ℕ)
    (hcoarse : tables.coarse.intervals + 1 ≤ heightBudget n)
    (hfine : tables.fine.intervals ≤ heightBudget n) :
    (Covers.OracleProgram.bits (RuntimeWorld.configuration (parameters n (k + 1)) label tables)
      I.weight (LabelledFactory.initialCache root)).expect (fun bits =>
        (frontend label root (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d)
          (parameters n (k + 1)) inverse tables (LabelledFactory.initialCache root)).evaluate
            I.weight bits (fun o => (o.work : ℝ))) ≤
        (frontendFactor K * (n + 1) * t n * ell n ^ (d + 140) : ℕ) ∧
      (Covers.OracleProgram.bits (RuntimeWorld.configuration (parameters n (k + 1)) label tables)
        I.weight (LabelledFactory.initialCache root)).expect (fun bits =>
          (frontend label root (K * (n + 1) * t n * ell n ^ d) (K * t n * ell n ^ d)
            (parameters n (k + 1)) inverse tables (LabelledFactory.initialCache root)).evaluate
              I.weight bits (fun o => (o.positiveReplies : ℝ))) ≤
        (frontendFactor K * t n * ell n ^ (d + 140) : ℕ) :=
  frontend_mixed_of_step I label hinj root tables inverse hleft K d hcoarse hfine
    (fun bits _ => step_resources_public I label hinj hT root tables inverse _ _ hcoarse bits)

end SteinerUpperBound.ConcreteEstimator
