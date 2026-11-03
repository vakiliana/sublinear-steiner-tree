module

public import SteinerUpperBound.MSTApproximation.Success
public import SteinerUpperBound.MSTApproximation.FrontendResources

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound QueryProgram
open scoped Classical

variable {V Q : Type*} [Fintype V] {k : ℕ}

noncomputable def allowance (g : Grid) (nu slack : ℝ) (psi hop budget : ℕ) : ℝ :=
  massAllowance g (fineDelta nu) (3 * (1 + (psi : ℝ)) + slack) psi hop budget

structure Tuning where
  cutoff : ℕ
  accuracy : ℝ
  samples : ℕ
  proposals : ℕ

noncomputable def tune (terminals : ℕ) (g : Grid) (nu beta slack : ℝ) (psi hop budget : ℕ) : Tuning :=
  let A := allowance g nu slack psi hop budget
  let xi := scoreAccuracy A nu
  let s := scoreSamples beta xi
  ⟨componentBudget A nu, xi, s, proposalBudget terminals s beta xi⟩

theorem tuning_bounds (terminals : ℕ) (g : Grid) (nu beta slack : ℝ) (psi hop budget : ℕ)
    (hk : 0 < terminals) (hn : 0 < nu) (hn1 : nu ≤ 1) (hb : 0 < beta) (hs : 0 ≤ slack) :
    let A := allowance g nu slack psi hop budget
    let t := tune terminals g nu beta slack psi hop budget
    1 ≤ A ∧ 0 < t.accuracy ∧ t.accuracy ≤ 1 ∧ t.accuracy ≤ nu / (100 * A) ∧
      100 * A / nu ≤ (t.cutoff : ℝ) ∧ 0 < t.samples ∧
      256 ≤ beta * ((t.samples : ℝ) * t.accuracy ^ 2) ∧
      Real.exp (-(t.proposals : ℝ) / terminals) ≤ beta * t.accuracy / (16 * t.samples) := by
  let A := allowance g nu slack psi hop budget
  have hA : 1 ≤ A := massAllowance_ge_one g _ _ _ _ _
    (by unfold fineDelta; positivity)
    (by nlinarith [show (0 : ℝ) ≤ psi from Nat.cast_nonneg psi])
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hxi := scoreAccuracy_bounds A nu hA hn hn1
  have hsample := scoreSamples_budget beta (scoreAccuracy A nu) hb hxi.1
  exact ⟨hA, hxi.1, hxi.2, le_rfl, componentBudget_bound A nu,
    hsample.1, hsample.2, proposalBudget_bound terminals _ hk hsample.1 beta _ hb hxi.1⟩

noncomputable def configuredFrontend (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (nu beta slack : ℝ) (psi hop budget : ℕ)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q) : Code (Sym2 V) Q (IntervalAnswer Q) :=
  let t := tune (k + 1) g nu beta slack psi hop budget
  .tick (t.cutoff + t.samples + t.proposals + 32)
    (frontend e key g nu t.accuracy t.cutoff t.proposals t.samples l root cache)

theorem configuredFrontend_law (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (nu beta slack : ℝ) (psi hop budget : ℕ)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q) (F : IntervalAnswer Q → ℝ) :
    let t := tune (k + 1) g nu beta slack psi hop budget
    (configuredFrontend e key g nu beta slack psi hop budget l root cache).evaluate w b (fun o => F o.value) =
      (frontend e key g nu t.accuracy t.cutoff t.proposals t.samples l root cache).evaluate w b
        (fun o => F o.value) := by
  rfl

theorem configuredFrontend_failure (I : Instance V) (b : Q → Bool)
    (e : Fin (k + 1) → V) (hinj : Function.Injective e) (key : ℕ → V → Q)
    (g : Grid) (nu beta R slack : ℝ) (psi hop budget : ℕ)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct b cache) (henum : Finset.univ.image e = l.toFinset) (hT : l.toFinset = I.terminals)
    (hroot : ∀ i < g.intervals, b (key i (e root)) = true)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hb : 0 < beta) (hb1 : beta ≤ 1) (hslack : 0 ≤ slack)
    (hq : g.q = fineRatio nu) (hn : g.intervals ≤ budget)
    (hR : 0 ≤ R) (hRL : R ≤ I.mst) (hcap : g.scale g.intervals ≤ 4 * g.q * R)
    (hcover : ∀ i < g.intervals, Covers.Geometry.CoverOn I I.terminals
      (ComponentExplore.retained b (key i) l.toFinset) (fineDelta nu * g.scale i))
    (hsize : ∀ i < g.intervals,
      ((ComponentExplore.retained b (key i) l.toFinset).card : ℝ) ≤
        Real.exp 1 * (1 + (psi : ℝ) *
          (1 + 2 * hop * I.mst / (fineDelta nu * g.scale i))) + slack)
    (hfirst : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, x ≠ y → g.first ≤ I.distance x y)
    (hlast : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, I.distance x y ≤ g.scale g.intervals) :
    Code.probability I.weight b (configuredFrontend e key g nu beta slack psi hop budget l root cache)
      {o | ¬ CorrectInterval I nu o.value} ≤ (g.intervals : ℝ) * beta := by
  let t := tune (k + 1) g nu beta slack psi hop budget
  obtain ⟨_, hx, hx1, hxA, hB, hs, hsamples, hrow⟩ :=
    tuning_bounds (k + 1) g nu beta slack psi hop budget (by omega) hnu hnu1 hb hslack
  have hr : Real.exp (-(t.proposals : ℝ) / (k + 1)) ≤ beta * t.accuracy / (16 * t.samples) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hrow
  have hprob : Code.probability I.weight b
      (configuredFrontend e key g nu beta slack psi hop budget l root cache)
      {o | ¬ CorrectInterval I nu o.value} =
      Code.probability I.weight b
        (frontend e key g nu t.accuracy t.cutoff t.proposals t.samples l root cache)
        {o | ¬ CorrectInterval I nu o.value} := by rfl
  rw [hprob]
  exact frontend_interval_failure I b e hinj key g nu t.accuracy beta R slack
    t.cutoff t.proposals t.samples psi hop budget l root cache hc henum hT hroot hnu hnu1 hx hx1 hb hb1
    hslack hq hn hR hRL hcap hcover hsize hfirst hlast hxA hB hs hsamples hr

theorem configuredFrontend_expected_resources (I : Instance V) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (nu beta slack : ℝ) (psi hop budget : ℕ)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct b cache) (he : Finset.univ.image e = l.toFinset)
    (hr : ∀ i < g.intervals, b (key i (e root)) = true) :
    let t := tune (k + 1) g nu beta slack psi hop budget
    (configuredFrontend e key g nu beta slack psi hop budget l root cache).evaluate I.weight b
        (fun o => (o.work : ℝ)) ≤
          t.cutoff + t.samples + t.proposals + 33 +
            (loopBudget l.length t.cutoff t.proposals t.samples (List.range g.intervals) + 11 : ℝ) ∧
      (configuredFrontend e key g nu beta slack psi hop budget l root cache).evaluate I.weight b
        (fun o => (o.positiveReplies : ℝ)) ≤ (t.cutoff + 1) * t.samples * g.intervals := by
  dsimp only
  let t := tune (k + 1) g nu beta slack psi hop budget
  have h := frontend_expected_resources I b e key g nu t.accuracy t.cutoff t.proposals t.samples l root cache hc he hr
  constructor
  · rw [configuredFrontend, evaluate_tick_work]
    have heq : ((t.cutoff + t.samples + t.proposals + 32 + 1 : ℕ) : ℝ) =
        t.cutoff + t.samples + t.proposals + 33 := by push_cast; ring
    rw [heq]
    exact add_le_add le_rfl h.1
  · rw [configuredFrontend, evaluate_tick_positive]
    exact h.2

noncomputable def configuredPreprocessor (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (nu zeta R beta slack : ℝ) (psi hop : ℕ) (c : GridConstants (fineRatio nu) zeta)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hnu : 0 < nu) (hz : 0 < zeta) (hR : 0 < R) : Code (Sym2 V) Q (PreprocessorAnswer Q) :=
  (gridProgram (k + 1) (fineRatio nu) zeta 1 R (c.budget (k + 1)) (by omega)
    (by unfold fineRatio; linarith) hz (by norm_num) hR).bind (fun g =>
      (configuredFrontend e key g nu beta slack psi hop (c.budget (k + 1)) l root cache).map
        (fun r => ⟨g, r⟩))

theorem configuredPreprocessor_law (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (nu zeta R beta slack : ℝ) (psi hop : ℕ) (c : GridConstants (fineRatio nu) zeta)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hnu : 0 < nu) (hz : 0 < zeta) (hR : 0 < R) (F : PreprocessorAnswer Q → ℝ) :
    let g := generate (k + 1) (fineRatio nu) zeta 1 R (c.budget (k + 1)) (by omega)
      (by unfold fineRatio; linarith) hz (by norm_num) hR
    (configuredPreprocessor e key nu zeta R beta slack psi hop c l root cache hnu hz hR).evaluate
      w b (fun o => F o.value) =
        (configuredFrontend e key g nu beta slack psi hop (c.budget (k + 1)) l root cache).evaluate
          w b (fun o => F ⟨g, o.value⟩) := by
  dsimp only
  rw [configuredPreprocessor, Code.evaluate_bind, gridProgram_evaluates, Code.evaluate_map]
  rfl

end SteinerUpperBound.MSTApproximation
