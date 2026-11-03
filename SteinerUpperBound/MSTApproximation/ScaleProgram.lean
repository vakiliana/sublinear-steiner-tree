module

public import SteinerUpperBound.MSTApproximation.ScoresProgram
public import SteinerUpperBound.MSTApproximation.SamplerLaw

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry QueryProgram
open scoped Classical BigOperators
open Covers.Rejection
open Covers.OracleProgram.Sampler

variable {V Q : Type*} [Fintype V] {k : ℕ}

structure ScaleAnswer (Q : Type*) where
  gminus : ℝ
  empirical : ℝ
  successful : Bool
  cache : Cache Q

noncomputable def scaleContinuation (e : Fin (k + 1) → V) (key : V → Q)
    (a xi : ℝ) (B : ℕ) (l : List V) (samples : ℕ) (cache : Cache Q)
    (obs : Observation k samples) : Code (Sym2 V) Q (ScaleAnswer Q) :=
  match obs.labels with
  | none => .tick 5 (.pure ⟨0, 0, false, cache⟩)
  | some ys => .tick (3 * samples + 5)
      ((scoresProgram key a B l (List.ofFn (fun j => e (ys j))) cache).bind (fun r =>
        .tick 8 (.pure ⟨lowerEstimate (k + 1) samples obs.proposals xi,
          r.total / samples, obs.successful, r.cache⟩)))

noncomputable def continuationResult (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : V → Q)
    (a xi : ℝ) (B : ℕ) (l : List V) (samples : ℕ) (cache : Cache Q)
    (obs : Observation k samples) : Outcome (ScaleAnswer Q) :=
  match obs.labels with
  | none => ⟨⟨0, 0, false, cache⟩, 6, 0, 0, 0⟩
  | some ys =>
      let r := scoresResult w b key a B l (List.ofFn (fun j => e (ys j))) cache
      r.combine ((Outcome.pure ⟨lowerEstimate (k + 1) samples obs.proposals xi,
        r.value.total / samples, obs.successful, r.value.cache⟩).add 9 0 0 0)
        |>.add (3 * samples + 6) 0 0 0

theorem scaleContinuation_evaluates (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : V → Q)
    (a xi : ℝ) (B : ℕ) (l : List V) (samples : ℕ) (cache : Cache Q)
    (obs : Observation k samples) :
    Code.Evaluates w b (scaleContinuation e key a xi B l samples cache obs)
      (continuationResult w b e key a xi B l samples cache obs) := by
  intro F
  cases hy : obs.labels with
  | none => simp [scaleContinuation, continuationResult, hy, Code.evaluate, Outcome.add, Outcome.pure]
  | some ys =>
    simp only [scaleContinuation, continuationResult, hy, Code.evaluate, Code.evaluate_bind]
    rw [scoresProgram_evaluates]

/-- Sampling and exploration use truthful caches. Exploration restarts from the incoming
cache so its continuation depends only on the sampler's checked observation. -/
noncomputable def scaleProgram (e : Fin (k + 1) → V) (key : V → Q)
    (a xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q) :
    Code (Sym2 V) Q (ScaleAnswer Q) :=
  (Covers.OracleProgram.Sampler.program (fun j => key (e j)) root C samples (samples * C) cache).bind
    (fun r => scaleContinuation e key a xi B l samples cache (Observation.ofRecords r))

noncomputable def scaleTrace (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : V → Q)
    (a xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (rows : Fin samples → Fin C → Fin (k + 1)) : ScaleAnswer Q :=
  (continuationResult w b e key a xi B l samples cache
    (fullObservation (fun y => b (key (e y))) root C samples (samples * C) 0 rows)).value

theorem scaleProgram_law (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : V → Q)
    (a xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct b cache) (F : ScaleAnswer Q → ℝ) :
    (scaleProgram e key a xi B C samples l root cache).evaluate w b (fun o => F o.value) =
      (poolLaw C samples).expect (fun rows => F (scaleTrace w b e key a xi B C samples l root cache rows)) := by
  rw [scaleProgram, Code.evaluate_bind]
  have heq : (fun o : Outcome (Records Q k samples) =>
      (scaleContinuation e key a xi B l samples cache (Observation.ofRecords o.value)).evaluate w b
        (fun r => F (o.combine r).value)) =
      (fun o => F (continuationResult w b e key a xi B l samples cache
        (Observation.ofRecords o.value)).value) := by
    funext o
    exact scaleContinuation_evaluates w b e key a xi B l samples cache
      (Observation.ofRecords o.value) (fun r => F r.value)
  rw [heq]
  simpa only [scaleTrace] using
    sampler_observation_law w b (fun j => key (e j)) root C samples cache hc
      (fun obs => F (continuationResult w b e key a xi B l samples cache obs).value)

theorem enumeration_selectedPoints (e : Fin (k + 1) → V) (key : V → Q) (b : Q → Bool)
    (l : List V) (he : Finset.univ.image e = l.toFinset) :
    selectedPoints e (fun y => b (key (e y))) = ComponentExplore.retained b key l.toFinset := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hb : b (key (e j)) = true := by
      simpa only [retained, CategoricalCoupling.selected, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    exact Finset.mem_filter.mpr ⟨he ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, hb⟩
  · intro hx
    obtain ⟨hxT, hxb⟩ := Finset.mem_filter.mp hx
    rw [← he] at hxT
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hxT
    exact Finset.mem_image.mpr ⟨j, by simp [retained, CategoricalCoupling.selected, hxb], rfl⟩

theorem scaleTrace_fields (I : Instance V) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : V → Q)
    (a xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct b cache) (hroot : b (key (e root)) = true)
    (he : Finset.univ.image e = l.toFinset)
    (rows : Fin samples → Fin C → Fin (k + 1)) :
    let b' := fun y => b (key (e y))
    let r := scaleTrace I.weight b e key a xi B C samples l root cache rows
    r.gminus = lowerEstimate (k + 1) samples (proposals b' C samples rows) xi ∧
      r.empirical = ScoreSampling.empirical
        (fun y => scoreOn I (ComponentExplore.retained b key l.toFinset) a B (e y))
          samples (labels b' root C samples rows) ∧
      r.successful = decide (Successful b' C samples rows) ∧ Cache.Correct b r.cache := by
  dsimp only
  let b' := fun y => b (key (e y))
  let ys := labels b' root C samples rows
  have hroots : ∀ x ∈ List.ofFn (fun j => e (ys j)),
      x ∈ ComponentExplore.retained b key l.toFinset := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    refine Finset.mem_filter.mpr ⟨?_, labels_retained b' root hroot C samples rows j⟩
    exact he ▸ Finset.mem_image.mpr ⟨ys j, Finset.mem_univ _, rfl⟩
  have hs := scoresResult_correct I b key a B l (List.ofFn (fun j => e (ys j))) cache hc hroots
  have hcache := scoresResult_cache I.weight b key a B l (List.ofFn (fun j => e (ys j))) cache hc
  simp only [List.map_ofFn, List.sum_ofFn] at hs
  refine ⟨?_, ?_, rfl, hcache⟩
  · simp [scaleTrace, continuationResult, fullObservation, Outcome.add, Outcome.combine, Outcome.pure]
  · change (scoresResult I.weight b key a B l (List.ofFn (fun j => e (ys j))) cache).value.total /
      samples = _
    rw [hs]
    rfl

end SteinerUpperBound.MSTApproximation
