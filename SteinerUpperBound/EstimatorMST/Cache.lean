module

public import SteinerUpperBound.EstimatorMST.Program

@[expose] public section

namespace SteinerUpperBound.EstimatorMST

open SteinerLowerBound Covers.Geometry QueryProgram
open scoped Classical BigOperators
open Covers.Rejection Covers.FiniteSampling

variable {V Q : Type*} [Fintype V] {k : ℕ}

theorem trace_cache (I : Instance V) (bits : Q → Bool) (n : ℕ)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q) (g : MSTApproximation.Grid)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct bits cache) (he : Finset.univ.image e = l.toFinset)
    (hr : ∀ i < g.intervals, bits (key i (e root)) = true)
    (rows : Fin (List.range g.intervals).length →
      Fin (samples n) → Fin (proposals n (k + 1)) → Fin (k + 1)) :
    Cache.Correct bits (MSTApproximation.answerTrace I.weight bits e key g EstimatorParameters.nu (accuracy n)
      (EstimatorParameters.BM n) (proposals n (k + 1)) (samples n) l root cache rows).cache :=
  MSTApproximation.frontendTrace_cache I bits e key g (accuracy n) (EstimatorParameters.BM n)
    (proposals n (k + 1)) (samples n) l root (List.range g.intervals)
    (MSTApproximation.initialState cache) hc he (fun i hi => hr i (List.mem_range.mp hi)) rows

theorem cache_failure_zero (I : Instance V) (bits : Q → Bool) (n : ℕ)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q) (g : MSTApproximation.Grid)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct bits cache) (he : Finset.univ.image e = l.toFinset)
    (hr : ∀ i < g.intervals, bits (key i (e root)) = true) :
    Code.probability I.weight bits (program n e key g l root cache)
      {o | ¬ Cache.Correct bits o.value.cache} = 0 := by
  classical
  have hprob : Code.probability I.weight bits (program n e key g l root cache)
      {o | ¬ Cache.Correct bits o.value.cache} =
      (tape (poolLaw (proposals n (k + 1)) (samples n)) (List.range g.intervals).length).prob
        {rows | ¬ Cache.Correct bits
          (MSTApproximation.answerTrace I.weight bits e key g EstimatorParameters.nu (accuracy n)
            (EstimatorParameters.BM n) (proposals n (k + 1)) (samples n) l root cache rows).cache} := by
    simpa only [Set.mem_ofPred_eq] using program_probability I bits n e key g l root cache hc he hr
      {r | ¬ Cache.Correct bits r.cache}
  rw [hprob]
  have hevents : {rows | ¬ Cache.Correct bits
      (MSTApproximation.answerTrace I.weight bits e key g EstimatorParameters.nu (accuracy n)
        (EstimatorParameters.BM n) (proposals n (k + 1)) (samples n) l root cache rows).cache} = ∅ := by
    ext rows
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact not_not.mpr (trace_cache I bits n e key g l root cache hc he hr rows)
  rw [hevents]
  exact Law.prob_empty _

theorem cache_on_support (I : Instance V) (bits : Q → Bool) (n : ℕ)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q) (g : MSTApproximation.Grid)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct bits cache) (he : Finset.univ.image e = l.toFinset)
    (hr : ∀ i < g.intervals, bits (key i (e root)) = true)
    (seed : ((program n e key g l root cache).compile I.weight).Seed)
    (hs : 0 < ((program n e key g l root cache).compile I.weight).law.mass seed) :
    Cache.Correct bits
      (((program n e key g l root cache).compile I.weight).tree seed |>.output bits).value.cache := by
  classical
  let p := program n e key g l root cache
  let E : Set (Outcome (MSTApproximation.IntervalAnswer Q)) := {o | ¬ Cache.Correct bits o.value.cache}
  have heq := Code.compile_probability I.weight bits p E
  have hz : (p.compile I.weight).law.prob {s | ((p.compile I.weight).tree s).output bits ∈ E} = 0 :=
    heq.trans (cache_failure_zero I bits n e key g l root cache hc he hr)
  by_contra hbad
  have hmem : seed ∈ {s | ((p.compile I.weight).tree s).output bits ∈ E} := hbad
  have hsub : ({seed} : Set (p.compile I.weight).Seed) ⊆
      {s | ((p.compile I.weight).tree s).output bits ∈ E} := by
    intro x hx
    have hxs : x = seed := Set.mem_singleton_iff.mp hx
    simpa only [hxs] using hmem
  have hm := (p.compile I.weight).law.prob_mono hsub
  rw [CategoricalCoupling.probability_atom, hz] at hm
  exact (not_le_of_gt hs) hm

end SteinerUpperBound.EstimatorMST
