module

public import SteinerUpperBound.MSTApproximation.Interval
public import SteinerUpperBound.MSTApproximation.ScaleProbability

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry QueryProgram
open scoped Classical BigOperators
open Covers.Rejection Covers.FiniteSampling

variable {V Q : Type*} [Fintype V] {k : ℕ}

structure Measurement where
  gminus : ℝ
  empirical : ℝ
  successful : Bool

structure FrontendState (Q : Type*) where
  correction : ℝ
  readings : ℕ → Measurement
  successful : Bool
  cache : Cache Q

def initialState (cache : Cache Q) : FrontendState Q := ⟨0, fun _ => ⟨0, 0, false⟩, true, cache⟩

noncomputable def contribution (g : Grid) (xi : ℝ) (i : ℕ) (r : Measurement) : ℝ :=
  g.width i * max 0 (Estimation.lowerCount r.gminus r.empirical xi - 1)

noncomputable abbrev recordScale (g : Grid) (xi : ℝ) (s : FrontendState Q)
    (i : ℕ) (r : ScaleAnswer Q) : FrontendState Q :=
  ⟨s.correction + contribution g xi i ⟨r.gminus, r.empirical, r.successful⟩,
    Function.update s.readings i ⟨r.gminus, r.empirical, r.successful⟩,
    s.successful && r.successful, r.cache⟩

noncomputable def frontendLoop (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) :
    List ℕ → FrontendState Q → Code (Sym2 V) Q (FrontendState Q)
  | [], s => .pure s
  | i :: is, s =>
      (scaleProgram e (key i) (g.scale i) xi B C samples l root s.cache).bind (fun r =>
        .tick (2 * i + 12) (frontendLoop e key g xi B C samples l root is (recordScale g xi s i r)))

noncomputable def frontendTrace (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) :
    (is : List ℕ) → FrontendState Q →
      (Fin is.length → Fin samples → Fin C → Fin (k + 1)) → FrontendState Q
  | [], s, _ => s
  | i :: is, s, rows =>
      frontendTrace w b e key g xi B C samples l root is
        (recordScale g xi s i
          (scaleTrace w b e (key i) (g.scale i) xi B C samples l root s.cache (rows 0)))
        (Fin.tail rows)

theorem frontendTrace_cache (I : Instance V) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1))
    (is : List ℕ) (s : FrontendState Q) (hc : Cache.Correct b s.cache)
    (he : Finset.univ.image e = l.toFinset) (hr : ∀ i ∈ is, b (key i (e root)) = true)
    (rows : Fin is.length → Fin samples → Fin C → Fin (k + 1)) :
    Cache.Correct b (frontendTrace I.weight b e key g xi B C samples l root is s rows).cache := by
  induction is generalizing s with
  | nil => exact hc
  | cons i is ih =>
    have hstep := (scaleTrace_fields I b e (key i) (g.scale i) xi B C samples l root s.cache
      hc (hr i List.mem_cons_self) he (rows 0)).2.2.2
    exact ih _ hstep (fun j hj => hr j (List.mem_cons_of_mem _ hj)) (Fin.tail rows)

theorem frontendLoop_law (I : Instance V) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1))
    (is : List ℕ) (s : FrontendState Q) (hc : Cache.Correct b s.cache)
    (he : Finset.univ.image e = l.toFinset) (hr : ∀ i ∈ is, b (key i (e root)) = true)
    (F : FrontendState Q → ℝ) :
    (frontendLoop e key g xi B C samples l root is s).evaluate I.weight b (fun o => F o.value) =
      (tape (poolLaw C samples) is.length).expect
        (fun rows => F (frontendTrace I.weight b e key g xi B C samples l root is s rows)) := by
  induction is generalizing s with
  | nil => simp [frontendLoop, frontendTrace, Code.evaluate, tape, Outcome.pure]
  | cons i is ih =>
    rw [frontendLoop, Code.evaluate_bind]
    have hfun : (fun o : Outcome (ScaleAnswer Q) =>
        (Code.tick (2 * i + 12) (frontendLoop e key g xi B C samples l root is
          (recordScale g xi s i o.value))).evaluate I.weight b (fun r => F (o.combine r).value)) =
        (fun o => (frontendLoop e key g xi B C samples l root is (recordScale g xi s i o.value)).evaluate
          I.weight b (fun r => F r.value)) := by funext o; rfl
    rw [hfun]
    rw [scaleProgram_law I.weight b e (key i) (g.scale i) xi B C samples l root s.cache hc
      (fun r => (frontendLoop e key g xi B C samples l root is (recordScale g xi s i r)).evaluate
        I.weight b (fun o => F o.value))]
    change _ = (tape (poolLaw C samples) (is.length + 1)).expect
      (fun rows : Fin (is.length + 1) → Fin samples → Fin C → Fin (k + 1) =>
        F (frontendTrace I.weight b e key g xi B C samples l root (i :: is) s rows))
    rw [expect_tape_succ]
    apply congrArg (poolLaw C samples).expect
    funext row
    have hstep := (scaleTrace_fields I b e (key i) (g.scale i) xi B C samples l root s.cache
      hc (hr i List.mem_cons_self) he row).2.2.2
    simpa only [frontendTrace, Fin.cons_zero, Fin.tail_cons] using
      ih _ hstep (fun j hj => hr j (List.mem_cons_of_mem _ hj))

theorem frontendTrace_reading_unchanged (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1))
    (is : List ℕ) (s : FrontendState Q) (j : ℕ) (hj : j ∉ is)
    (rows : Fin is.length → Fin samples → Fin C → Fin (k + 1)) :
    (frontendTrace w b e key g xi B C samples l root is s rows).readings j = s.readings j := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    have hji : j ≠ i := fun h => hj (List.mem_cons.mpr (Or.inl h))
    have hjis : j ∉ is := fun h => hj (List.mem_cons_of_mem _ h)
    rw [frontendTrace, ih _ hjis]
    exact Function.update_of_ne hji _ _

theorem frontendTrace_correction (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1))
    (is : List ℕ) (s : FrontendState Q) (hn : is.Nodup)
    (rows : Fin is.length → Fin samples → Fin C → Fin (k + 1)) :
    let r := frontendTrace w b e key g xi B C samples l root is s rows
    r.correction = s.correction + ∑ i ∈ is.toFinset, contribution g xi i (r.readings i) := by
  induction is generalizing s with
  | nil => simp [frontendTrace]
  | cons i is ih =>
    have hni : i ∉ is := (List.nodup_cons.mp hn).1
    have hnt : is.Nodup := (List.nodup_cons.mp hn).2
    let r := scaleTrace w b e (key i) (g.scale i) xi B C samples l root s.cache (rows 0)
    let s' := recordScale g xi s i r
    have ht := ih s' hnt (Fin.tail rows)
    have hread := frontendTrace_reading_unchanged w b e key g xi B C samples l root is s' i hni
      (Fin.tail rows)
    simp only [s', recordScale, Function.update_self] at hread
    change (frontendTrace w b e key g xi B C samples l root is s' (Fin.tail rows)).correction =
      s.correction + ∑ j ∈ (i :: is).toFinset, contribution g xi j
        ((frontendTrace w b e key g xi B C samples l root is s' (Fin.tail rows)).readings j)
    rw [List.toFinset_cons, Finset.sum_insert (by simpa only [List.mem_toFinset] using hni), hread, ht]
    dsimp only [s', recordScale]
    ring

structure IntervalAnswer (Q : Type*) where
  value : ℝ
  lower : ℝ
  upper : ℝ
  successful : Bool
  readings : ℕ → Measurement
  cache : Cache Q

noncomputable def finish (k : ℕ) (g : Grid) (nu : ℝ) (s : FrontendState Q) : IntervalAnswer Q :=
  let value := ((k - 1 : ℕ) : ℝ) * g.first + s.correction
  ⟨value, lowerEndpoint nu value, upperEndpoint nu value, s.successful, s.readings, s.cache⟩

noncomputable def frontend (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (nu xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q) :
    Code (Sym2 V) Q (IntervalAnswer Q) :=
  (frontendLoop e key g xi B C samples l root (List.range g.intervals) (initialState cache)).bind
    (fun s => .tick 10 (.pure (finish (k + 1) g nu s)))

theorem finish_trace_value (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (nu xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (rows : Fin g.intervals → Fin samples → Fin C → Fin (k + 1)) :
    let s := frontendTrace w b e key g xi B C samples l root (List.range g.intervals) (initialState cache)
      (fun j => rows ⟨j.val, by simpa only [List.length_range] using j.isLt⟩)
    (finish (k + 1) g nu s).value =
      estimate (k + 1) g (fun i => s.readings i |>.gminus) (fun i => s.readings i |>.empirical) xi := by
  dsimp only
  have h := frontendTrace_correction w b e key g xi B C samples l root (List.range g.intervals)
    (initialState cache) List.nodup_range
    (fun j => rows ⟨j.val, by simpa only [List.length_range] using j.isLt⟩)
  simp only [List.toFinset_range, show (initialState cache).correction = 0 from rfl, zero_add] at h
  dsimp only [finish, estimate]
  rw [h]
  rfl

end SteinerUpperBound.MSTApproximation
