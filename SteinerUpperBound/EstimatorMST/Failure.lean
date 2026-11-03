module

public import SteinerUpperBound.EstimatorMST.Program

@[expose] public section

namespace SteinerUpperBound.EstimatorMST

open SteinerLowerBound Covers.Geometry QueryProgram
open scoped Classical BigOperators
open Covers.Rejection Covers.FiniteSampling

variable {V Q : Type*} [Fintype V] {k : ℕ}

omit [Fintype V] in
theorem enumeration_card (e : Fin (k + 1) → V) (hinj : Function.Injective e)
    (l : List V) (he : Finset.univ.image e = l.toFinset) (I : Instance V) (hT : l.toFinset = I.terminals) :
    I.terminals.card = k + 1 := by
  rw [← hT, ← he, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- Actual integer fine-stage accuracy on the concrete retained-cover/size event.
No scalar tuning or accurate-MST-estimate certificate is an input. -/
theorem interval_failure (I : Instance V) (bits : Q → Bool) (n : ℕ)
    (e : Fin (k + 1) → V) (hinj : Function.Injective e) (key : ℕ → V → Q)
    (g : MSTApproximation.Grid) (R : ℝ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct bits cache) (he : Finset.univ.image e = l.toFinset) (hT : l.toFinset = I.terminals)
    (_hkn : k + 1 ≤ n) (hr : ∀ i < g.intervals, bits (key i (e root)) = true)
    (hq : g.q = MSTApproximation.fineRatio EstimatorParameters.nu)
    (hh : g.intervals ≤ EstimatorParameters.heightBudget n)
    (hR : 0 ≤ R) (hRL : R ≤ I.mst) (hcap : g.scale g.intervals ≤ 4 * g.q * R)
    (hcover : ∀ i < g.intervals, CoverOn I I.terminals
      (ComponentExplore.retained bits (key i) l.toFinset) (EstimatorParameters.deltaFine * g.scale i))
    (hsize : ∀ i < g.intervals,
      ((ComponentExplore.retained bits (key i) l.toFinset).card : ℝ) ≤
        EstimatorParameters.Hc n + 6 * EstimatorParameters.coverTrials n * EstimatorParameters.hopBudget n *
          I.mst / (EstimatorParameters.deltaFine * g.scale i))
    (hfirst : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, x ≠ y → g.first ≤ I.distance x y)
    (hlast : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, I.distance x y ≤ g.scale g.intervals) :
    Code.probability I.weight bits (program n e key g l root cache)
      {o | ¬ MSTApproximation.CorrectInterval I EstimatorParameters.nu o.value} ≤
        (g.intervals : ℝ) * EstimatorParameters.beta n := by
  classical
  let N := fun i => ComponentExplore.retained bits (key i) l.toFinset
  have hcard := enumeration_card e hinj l he I hT
  have hTpos : I.terminals.Nonempty := Finset.card_pos.mp (by omega)
  have hN : ∀ i < g.intervals, N i ⊆ I.terminals := by
    intro i hi x hx
    rw [← hT]
    exact (Finset.mem_filter.mp hx).1
  have hmass := EstimatorParameters.fine_mass_bound I g N n R hq hR hRL hh hcap hsize
  have hA : (1 : ℝ) ≤ EstimatorParameters.AM n := by exact_mod_cast EstimatorParameters.AM_pos n
  obtain ⟨hx, hx1, hxA, hB, hs, hsamples, hrow⟩ := public_tuning n (k + 1) (by omega)
  have hb := EstimatorParameters.beta_bounds n
  have hnu : 0 < EstimatorParameters.nu := by
    norm_num [EstimatorParameters.nu, EstimatorParameters.nuQ, EstimatorParameters.cQ]
  have hnu1 : EstimatorParameters.nu ≤ 1 := by
    norm_num [EstimatorParameters.nu, EstimatorParameters.nuQ, EstimatorParameters.cQ]
  have hrow' : Real.exp (-(proposals n (k + 1) : ℝ) / (k + 1)) ≤
      EstimatorParameters.beta n * accuracy n / (16 * samples n) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hrow
  have hgoodBad := MSTApproximation.goodSteps_failure I bits e hinj key g (accuracy n) (EstimatorParameters.beta n)
    (EstimatorParameters.BM n) (proposals n (k + 1)) (samples n) l root
    (List.range g.intervals) (MSTApproximation.initialState cache) hc he
    (fun i hi => hr i (List.mem_range.mp hi)) hs hx hx1 hb.1 (hb.2.1.trans (by norm_num))
    hsamples.le hrow'
  have hprob : Code.probability I.weight bits (program n e key g l root cache)
      {o | ¬ MSTApproximation.CorrectInterval I EstimatorParameters.nu o.value} =
      (tape (poolLaw (proposals n (k + 1)) (samples n)) (List.range g.intervals).length).prob
        {rows | ¬ MSTApproximation.CorrectInterval I EstimatorParameters.nu
          (MSTApproximation.answerTrace I.weight bits e key g EstimatorParameters.nu (accuracy n)
            (EstimatorParameters.BM n) (proposals n (k + 1)) (samples n) l root cache rows)} := by
    simpa only [Set.mem_ofPred_eq] using program_probability I bits n e key g l root cache hc he hr
      {r | ¬ MSTApproximation.CorrectInterval I EstimatorParameters.nu r}
  rw [hprob]
  have hsub : {rows | ¬ MSTApproximation.CorrectInterval I EstimatorParameters.nu
      (MSTApproximation.answerTrace I.weight bits e key g EstimatorParameters.nu (accuracy n)
        (EstimatorParameters.BM n) (proposals n (k + 1)) (samples n) l root cache rows)} ⊆
      {rows | ¬ MSTApproximation.GoodSteps I bits e key g (accuracy n) (EstimatorParameters.BM n)
        (proposals n (k + 1)) (samples n) l root (List.range g.intervals)
          (MSTApproximation.initialState cache) rows} := by
    intro rows hnot
    by_contra hfalse
    have hgood : MSTApproximation.GoodSteps I bits e key g (accuracy n) (EstimatorParameters.BM n)
        (proposals n (k + 1)) (samples n) l root (List.range g.intervals)
          (MSTApproximation.initialState cache) rows := by
      simpa only [Set.mem_ofPred_eq, not_not] using hfalse
    have hread := (MSTApproximation.goodSteps_readings I bits e key g (accuracy n) (EstimatorParameters.BM n)
      (proposals n (k + 1)) (samples n) l root (List.range g.intervals)
      (MSTApproximation.initialState cache) List.nodup_range rfl rows hgood).2
    let r := MSTApproximation.answerTrace I.weight bits e key g EstimatorParameters.nu (accuracy n)
      (EstimatorParameters.BM n) (proposals n (k + 1)) (samples n) l root cache rows
    have hcal : ∀ i < g.intervals, (1 - accuracy n) * ((N i).card : ℝ) ≤ (r.readings i).gminus :=
      fun i hi => (hread i (List.mem_range.mpr hi)).2.1
    have hcal1 : ∀ i < g.intervals, (r.readings i).gminus ≤ (N i).card :=
      fun i hi => (hread i (List.mem_range.mpr hi)).2.2.1
    have hemp : ∀ i < g.intervals,
        |(r.readings i).empirical - MSTApproximation.scoreMean I (N i) (g.scale i) (EstimatorParameters.BM n)| ≤
          accuracy n :=
      fun i hi => (hread i (List.mem_range.mpr hi)).2.2.2
    have hcov : ∀ i < g.intervals, CoverOn I I.terminals (N i)
        (MSTApproximation.fineDelta EstimatorParameters.nu * g.scale i) := by
      simpa only [EstimatorParameters.ratio_casts.2.2.1] using hcover
    have hm := MSTApproximation.interval_correct I g N EstimatorParameters.nu (EstimatorParameters.AM n)
      (accuracy n) (EstimatorParameters.BM n) (fun i => (r.readings i).gminus)
      (fun i => (r.readings i).empirical) hnu hnu1 hA hx.le hxA.le hB.symm.le hq hTpos hN hcov
      hfirst hlast hmass hcal hcal1 hemp
    have hv := MSTApproximation.answerTrace_value I.weight bits e key g EstimatorParameters.nu (accuracy n)
      (EstimatorParameters.BM n) (proposals n (k + 1)) (samples n) l root cache rows
    have hv' : r.value = MSTApproximation.estimate I.terminals.card g
        (fun i => (r.readings i).gminus) (fun i => (r.readings i).empirical) (accuracy n) :=
      hv.trans (congrArg (fun count => MSTApproximation.estimate count g
        (fun i => (r.readings i).gminus) (fun i => (r.readings i).empirical) (accuracy n)) hcard.symm)
    apply hnot
    change I.mst / (1 + EstimatorParameters.nu) ≤ MSTApproximation.lowerEndpoint EstimatorParameters.nu r.value ∧
      MSTApproximation.lowerEndpoint EstimatorParameters.nu r.value ≤ I.mst ∧
      I.mst ≤ MSTApproximation.upperEndpoint EstimatorParameters.nu r.value ∧
      MSTApproximation.upperEndpoint EstimatorParameters.nu r.value ≤ (1 + EstimatorParameters.nu) * I.mst
    rw [hv']
    exact hm
  exact ((tape (poolLaw (proposals n (k + 1)) (samples n)) (List.range g.intervals).length).prob_mono hsub).trans
    (by simpa only [List.length_range] using hgoodBad)

theorem interval_failure_factory_size (I : Instance V) (bits : Q → Bool) (n : ℕ)
    (e : Fin (k + 1) → V) (hinj : Function.Injective e) (key : ℕ → V → Q)
    (g : MSTApproximation.Grid) (R : ℝ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct bits cache) (he : Finset.univ.image e = l.toFinset) (hT : l.toFinset = I.terminals)
    (hkn : k + 1 ≤ n) (hr : ∀ i < g.intervals, bits (key i (e root)) = true)
    (hq : g.q = MSTApproximation.fineRatio EstimatorParameters.nu)
    (hh : g.intervals ≤ EstimatorParameters.heightBudget n)
    (hR : 0 ≤ R) (hRL : R ≤ I.mst) (hcap : g.scale g.intervals ≤ 4 * g.q * R)
    (hcover : ∀ i < g.intervals, CoverOn I I.terminals
      (ComponentExplore.retained bits (key i) l.toFinset) (EstimatorParameters.deltaFine * g.scale i))
    (hsize : ∀ i < g.intervals,
      ((ComponentExplore.retained bits (key i) l.toFinset).card : ℝ) ≤
        Real.exp 1 * (1 + (EstimatorParameters.coverTrials n : ℝ) *
          (1 + 2 * EstimatorParameters.hopBudget n * I.mst / (EstimatorParameters.deltaFine * g.scale i))) +
          EstimatorParameters.coverSlack n)
    (hfirst : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, x ≠ y → g.first ≤ I.distance x y)
    (hlast : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, I.distance x y ≤ g.scale g.intervals) :
    Code.probability I.weight bits (program n e key g l root cache)
      {o | ¬ MSTApproximation.CorrectInterval I EstimatorParameters.nu o.value} ≤
        (g.intervals : ℝ) * EstimatorParameters.beta n := by
  have hlinear i hi := MSTApproximation.factory_size_bound I _ _
    (EstimatorParameters.coverSlack n) (EstimatorParameters.coverTrials n) (EstimatorParameters.hopBudget n)
    (mul_pos (by norm_num [EstimatorParameters.deltaFine, EstimatorParameters.deltaFineQ,
      EstimatorParameters.nuQ, EstimatorParameters.cQ]) (g.scale_pos i)) (hsize i hi)
  have hH : (EstimatorParameters.Hc n : ℝ) =
      3 * (1 + (EstimatorParameters.coverTrials n : ℝ)) + EstimatorParameters.coverSlack n := by
    unfold EstimatorParameters.Hc
    push_cast
    ring
  exact interval_failure I bits n e hinj key g R l root cache hc he hT hkn hr hq hh hR hRL hcap hcover
    (fun i hi => by simpa only [hH] using hlinear i hi) hfirst hlast

end SteinerUpperBound.EstimatorMST
