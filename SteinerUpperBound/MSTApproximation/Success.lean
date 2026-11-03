module

public import SteinerUpperBound.MSTApproximation.FrontendProbability
public import SteinerUpperBound.MSTApproximation.Parameters

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry QueryProgram
open scoped Classical BigOperators
open Covers.Rejection Covers.FiniteSampling

variable {V Q : Type*} [Fintype V] {k : ℕ}

def CorrectInterval (I : Instance V) (nu : ℝ) (r : IntervalAnswer Q) : Prop :=
  I.mst / (1 + nu) ≤ r.lower ∧ r.lower ≤ I.mst ∧ I.mst ≤ r.upper ∧ r.upper ≤ (1 + nu) * I.mst

theorem frontend_probability (I : Instance V) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (nu xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct b cache) (he : Finset.univ.image e = l.toFinset)
    (hr : ∀ i < g.intervals, b (key i (e root)) = true) (E : Set (IntervalAnswer Q)) :
    Code.probability I.weight b (frontend e key g nu xi B C samples l root cache) {o | o.value ∈ E} =
      (tape (poolLaw C samples) (List.range g.intervals).length).prob
        {rows | answerTrace I.weight b e key g nu xi B C samples l root cache rows ∈ E} := by
  classical
  let F : IntervalAnswer Q → ℝ := fun r => if r ∈ E then 1 else 0
  have hlaw := frontend_law I b e key g nu xi B C samples l root cache hc he hr F
  unfold Code.probability
  calc
    _ = (frontend e key g nu xi B C samples l root cache).evaluate I.weight b (fun o => F o.value) := by
      apply congrArg ((frontend e key g nu xi B C samples l root cache).evaluate I.weight b)
      funext o
      by_cases h : o.value ∈ E <;> simp [F, h]
    _ = _ := hlaw
    _ = _ := by
      rw [Law.prob_eq_expect]
      apply congrArg (tape (poolLaw C samples) (List.range g.intervals).length).expect
      funext rows
      by_cases h : answerTrace I.weight b e key g nu xi B C samples l root cache rows ∈ E <;> simp [F, h]

theorem frontend_interval_failure (I : Instance V) (b : Q → Bool)
    (e : Fin (k + 1) → V) (hinj : Function.Injective e) (key : ℕ → V → Q)
    (g : Grid) (nu xi beta R slack : ℝ) (B C samples psi hop budget : ℕ)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct b cache) (henum : Finset.univ.image e = l.toFinset) (hT : l.toFinset = I.terminals)
    (hroot : ∀ i < g.intervals, b (key i (e root)) = true)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hb : 0 < beta) (hb1 : beta ≤ 1) (hslack : 0 ≤ slack)
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
    (hs : 0 < samples) (hsamples : 256 ≤ beta * ((samples : ℝ) * xi ^ 2))
    (hrow : Real.exp (-(C : ℝ) / (k + 1)) ≤ beta * xi / (16 * samples)) :
    Code.probability I.weight b (frontend e key g nu xi B C samples l root cache)
      {o | ¬ CorrectInterval I nu o.value} ≤ (g.intervals : ℝ) * beta := by
  classical
  have hprob : Code.probability I.weight b (frontend e key g nu xi B C samples l root cache)
      {o | ¬ CorrectInterval I nu o.value} =
      (tape (poolLaw C samples) (List.range g.intervals).length).prob
        {rows | ¬ CorrectInterval I nu (answerTrace I.weight b e key g nu xi B C samples l root cache rows)} := by
    simpa only [Set.mem_ofPred_eq] using
      frontend_probability I b e key g nu xi B C samples l root cache hc henum hroot
        {r | ¬ CorrectInterval I nu r}
  rw [hprob]
  have hbad := goodSteps_failure I b e hinj key g xi beta B C samples l root
    (List.range g.intervals) (initialState cache) hc henum
    (fun i hi => hroot i (List.mem_range.mp hi)) hs hxi hxi1 hb hb1 hsamples hrow
  have hsub : {rows | ¬ CorrectInterval I nu
      (answerTrace I.weight b e key g nu xi B C samples l root cache rows)} ⊆
      {rows | ¬ GoodSteps I b e key g xi B C samples l root (List.range g.intervals)
        (initialState cache) rows} := by
    intro rows hnot
    by_contra hfalse
    have hgood : GoodSteps I b e key g xi B C samples l root (List.range g.intervals)
        (initialState cache) rows := by simpa only [Set.mem_ofPred_eq, not_not] using hfalse
    have hread := (goodSteps_readings I b e key g xi B C samples l root
      (List.range g.intervals) (initialState cache) List.nodup_range rfl rows hgood).2
    have hcal (i : ℕ) (hi : i < g.intervals) :
        (1 - xi) * ((ComponentExplore.retained b (key i) l.toFinset).card : ℝ) ≤
          ((answerTrace I.weight b e key g nu xi B C samples l root cache rows).readings i).gminus :=
      (hread i (List.mem_range.mpr hi)).2.1
    have hcal1 (i : ℕ) (hi : i < g.intervals) :
        ((answerTrace I.weight b e key g nu xi B C samples l root cache rows).readings i).gminus ≤
          (ComponentExplore.retained b (key i) l.toFinset).card :=
      (hread i (List.mem_range.mpr hi)).2.2.1
    have hemp (i : ℕ) (hi : i < g.intervals) :
        |((answerTrace I.weight b e key g nu xi B C samples l root cache rows).readings i).empirical -
          scoreMean I (ComponentExplore.retained b (key i) l.toFinset) (g.scale i) B| ≤ xi :=
      (hread i (List.mem_range.mpr hi)).2.2.2
    exact hnot (answerTrace_correct I b e hinj key g nu xi R slack B C samples psi hop budget l root cache rows
      henum hT hnu hnu1 hxi.le hslack hq hn hR hRL hcap hcover hsize hfirst hlast hxiA hB hcal hcal1 hemp)
  exact ((tape (poolLaw C samples) (List.range g.intervals).length).prob_mono hsub).trans
    (by simpa only [List.length_range] using hbad)

end SteinerUpperBound.MSTApproximation
