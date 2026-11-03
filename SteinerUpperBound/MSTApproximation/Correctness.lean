module

public import SteinerUpperBound.MSTApproximation.Frontend
public import SteinerUpperBound.MSTApproximation.GridProgram
public import SteinerUpperBound.MSTApproximation.ScaleResources

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry QueryProgram
open scoped Classical BigOperators
open Covers.Rejection Covers.FiniteSampling

variable {V Q : Type*} [Fintype V] {k : ℕ}

noncomputable def answerTrace (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (nu xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (rows : Fin (List.range g.intervals).length → Fin samples → Fin C → Fin (k + 1)) : IntervalAnswer Q :=
  finish (k + 1) g nu (frontendTrace w b e key g xi B C samples l root
    (List.range g.intervals) (initialState cache) rows)

theorem frontend_law (I : Instance V) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (nu xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct b cache) (he : Finset.univ.image e = l.toFinset)
    (hr : ∀ i < g.intervals, b (key i (e root)) = true) (F : IntervalAnswer Q → ℝ) :
    (frontend e key g nu xi B C samples l root cache).evaluate I.weight b (fun o => F o.value) =
      (tape (poolLaw C samples) (List.range g.intervals).length).expect
        (fun rows => F (answerTrace I.weight b e key g nu xi B C samples l root cache rows)) := by
  rw [frontend, Code.evaluate_bind]
  have hfun : (fun o : Outcome (FrontendState Q) =>
      (Code.tick 10 (.pure (finish (k + 1) g nu o.value))).evaluate I.weight b
        (fun r => F (o.combine r).value)) =
      (fun o => F (finish (k + 1) g nu o.value)) := by funext o; rfl
  rw [hfun]
  exact frontendLoop_law I b e key g xi B C samples l root (List.range g.intervals)
    (initialState cache) hc he (fun i hi => hr i (List.mem_range.mp hi))
    (fun s => F (finish (k + 1) g nu s))

theorem answerTrace_value (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (nu xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (rows : Fin (List.range g.intervals).length → Fin samples → Fin C → Fin (k + 1)) :
    let r := answerTrace w b e key g nu xi B C samples l root cache rows
    r.value = estimate (k + 1) g (fun i => (r.readings i).gminus) (fun i => (r.readings i).empirical) xi := by
  have h := frontendTrace_correction w b e key g xi B C samples l root (List.range g.intervals)
    (initialState cache) List.nodup_range rows
  simp only [List.toFinset_range, show (initialState cache).correction = 0 from rfl, zero_add] at h
  dsimp only [answerTrace, finish, estimate]
  rw [h]
  rfl

theorem answerTrace_correct (I : Instance V) (b : Q → Bool)
    (e : Fin (k + 1) → V) (hinj : Function.Injective e) (key : ℕ → V → Q)
    (g : Grid) (nu xi R slack : ℝ) (B C samples psi hop budget : ℕ)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (rows : Fin (List.range g.intervals).length → Fin samples → Fin C → Fin (k + 1))
    (henum : Finset.univ.image e = l.toFinset) (hT : l.toFinset = I.terminals)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hxi : 0 ≤ xi) (hslack : 0 ≤ slack)
    (hq : g.q = fineRatio nu) (hn : g.intervals ≤ budget)
    (hR : 0 ≤ R) (hRL : R ≤ I.mst) (hcap : g.scale g.intervals ≤ 4 * g.q * R)
    (hcover : ∀ i < g.intervals, CoverOn I I.terminals
      (ComponentExplore.retained b (key i) l.toFinset) (fineDelta nu * g.scale i))
    (hsize : ∀ i < g.intervals,
      ((ComponentExplore.retained b (key i) l.toFinset).card : ℝ) ≤
        Real.exp 1 * (1 + (psi : ℝ) *
          (1 + 2 * hop * I.mst / (fineDelta nu * g.scale i))) + slack)
    (hfirst : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, x ≠ y → g.first ≤ I.distance x y)
    (hlast : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, I.distance x y ≤ g.scale g.intervals)
    (hxiA : xi ≤ nu / (100 *
      massAllowance g (fineDelta nu) (3 * (1 + (psi : ℝ)) + slack) psi hop budget))
    (hB : 100 * massAllowance g (fineDelta nu) (3 * (1 + (psi : ℝ)) + slack) psi hop budget / nu ≤ (B : ℝ))
    (hcal : ∀ i < g.intervals, (1 - xi) *
      ((ComponentExplore.retained b (key i) l.toFinset).card : ℝ) ≤
        ((answerTrace I.weight b e key g nu xi B C samples l root cache rows).readings i).gminus)
    (hcal1 : ∀ i < g.intervals,
      ((answerTrace I.weight b e key g nu xi B C samples l root cache rows).readings i).gminus ≤
        (ComponentExplore.retained b (key i) l.toFinset).card)
    (hemp : ∀ i < g.intervals,
      |((answerTrace I.weight b e key g nu xi B C samples l root cache rows).readings i).empirical -
        scoreMean I (ComponentExplore.retained b (key i) l.toFinset) (g.scale i) B| ≤ xi) :
    let r := answerTrace I.weight b e key g nu xi B C samples l root cache rows
    I.mst / (1 + nu) ≤ r.lower ∧ r.lower ≤ I.mst ∧ I.mst ≤ r.upper ∧ r.upper ≤ (1 + nu) * I.mst := by
  let r := answerTrace I.weight b e key g nu xi B C samples l root cache rows
  have hcard : I.terminals.card = k + 1 := by
    rw [← hT, ← henum, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hTnonempty : I.terminals.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  have hsub : ∀ i < g.intervals, ComponentExplore.retained b (key i) l.toFinset ⊆ I.terminals := by
    intro i hi
    exact (Finset.filter_subset _ _).trans_eq hT
  have hm := interval_correct_of_factory_sizes I g (fun i => ComponentExplore.retained b (key i) l.toFinset)
    nu xi R slack B psi hop budget (fun i => (r.readings i).gminus) (fun i => (r.readings i).empirical)
    hnu hnu1 hxi hslack hq hTnonempty hn hR hRL hcap hsub hcover hsize hfirst hlast hxiA hB hcal hcal1 hemp
  have hv := answerTrace_value I.weight b e key g nu xi B C samples l root cache rows
  rw [← hcard] at hv
  change I.mst / (1 + nu) ≤ lowerEndpoint nu r.value ∧ lowerEndpoint nu r.value ≤ I.mst ∧
    I.mst ≤ upperEndpoint nu r.value ∧ upperEndpoint nu r.value ≤ (1 + nu) * I.mst
  rw [hv]
  exact hm

structure PreprocessorAnswer (Q : Type*) where
  grid : Grid
  interval : IntervalAnswer Q

noncomputable def preprocessor (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (nu zeta R xi : ℝ) (fuel B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hnu : 0 < nu) (hz : 0 < zeta) (hR : 0 < R) : Code (Sym2 V) Q (PreprocessorAnswer Q) :=
  (gridProgram (k + 1) (fineRatio nu) zeta 1 R fuel (by omega)
    (by unfold fineRatio; linarith) hz (by norm_num) hR).bind (fun g =>
      (frontend e key g nu xi B C samples l root cache).map (fun r => ⟨g, r⟩))

theorem preprocessor_law (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (nu zeta R xi : ℝ) (fuel B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hnu : 0 < nu) (hz : 0 < zeta) (hR : 0 < R) (F : PreprocessorAnswer Q → ℝ) :
    let g := generate (k + 1) (fineRatio nu) zeta 1 R fuel (by omega)
      (by unfold fineRatio; linarith) hz (by norm_num) hR
    (preprocessor e key nu zeta R xi fuel B C samples l root cache hnu hz hR).evaluate
      w b (fun o => F o.value) =
        (frontend e key g nu xi B C samples l root cache).evaluate w b (fun o => F ⟨g, o.value⟩) := by
  dsimp only
  rw [preprocessor, Code.evaluate_bind, gridProgram_evaluates]
  rw [Code.evaluate_map]
  rfl

end SteinerUpperBound.MSTApproximation
