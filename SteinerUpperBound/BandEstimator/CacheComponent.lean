module

public import SteinerUpperBound.BandEstimator.Program

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.BandEstimator

open QueryProgram MSTApproximation Covers.OracleProgram
open scoped Classical

variable {V Q : Type*}

def CacheFrame (allowed : Q → Prop) (initial current : Cache Q) : Prop :=
  (∀ q v, initial q = some v → current q = some v) ∧
    ∀ q, ¬ allowed q → current q = initial q

theorem cacheFrame_refl (allowed : Q → Prop) (c : Cache Q) : CacheFrame allowed c c :=
  ⟨fun _ _ h => h, fun _ _ => rfl⟩

theorem cacheFrame_resolved (allowed : Q → Prop) (initial c : Cache Q) (b : Q → Bool)
    (q : Q) (hq : allowed q) (hc : CacheFrame allowed initial c) :
    CacheFrame allowed initial (Cache.resolved b q c).value.2 := by
  cases he : c q with
  | some v => simpa only [Cache.resolved, he] using hc
  | none =>
    simp only [Cache.resolved, he]
    constructor
    · intro q' v hv
      have hne : q' ≠ q := by
        intro h
        subst q'
        have hh := hc.1 q v hv
        simp [he] at hh
      simpa only [Function.update_of_ne hne] using hc.1 q' v hv
    · intro q' hnot
      have hne : q' ≠ q := fun h => hnot (h.symm ▸ hq)
      simpa only [Function.update_of_ne hne] using hc.2 q' hnot

private theorem remember_cache (s : ComponentExplore.Memory V Q) (x : V) (bit : Bool) (c : Cache Q) :
    (s.remember x bit c).cache = c := by cases bit <;> rfl

private theorem step_invariant (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x y : V) (s : ComponentExplore.Memory V Q)
    (P : Cache Q → Prop) (hs : P s.cache)
    (hresolve : ∀ c, P c → P (Cache.resolved b (key y) c).value.2) :
    P (ComponentExplore.stepResult w b key a B x s y).value.cache := by
  have hr := hresolve s.cache hs
  by_cases hb : B < s.count <;>
    by_cases hm : (ComponentExplore.memberResult y s.points).value = true <;>
    by_cases hd : w (Sym2.mk x y) < a <;>
    simp only [ComponentExplore.stepResult, hb, hm, hd, ite_true, ite_false, Bool.false_eq_true,
      Outcome.add, Outcome.combine, Outcome.pure, remember_cache] <;> assumption

private theorem scan_invariant [Fintype V] (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (l : List V) (s : ComponentExplore.Memory V Q)
    (P : Cache Q → Prop) (hs : P s.cache)
    (hresolve : ∀ y ∈ l, ∀ c, P c → P (Cache.resolved b (key y) c).value.2) :
    P (ComponentExplore.scanResult w b key a B x l s).value.cache := by
  induction l generalizing s with
  | nil => exact hs
  | cons y l ih =>
    have ht := step_invariant w b key a B x y s P hs (hresolve y List.mem_cons_self)
    exact ih _ ht (fun z hz => hresolve z (List.mem_cons_of_mem _ hz))

private theorem loop_invariant [Fintype V] (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (fuel : ℕ) (s : ComponentExplore.Memory V Q)
    (P : Cache Q → Prop) (hs : P s.cache)
    (hresolve : ∀ y ∈ l, ∀ c, P c → P (Cache.resolved b (key y) c).value.2) :
    P (ComponentExplore.loopResult w b key a B l fuel s).value.memory.cache := by
  induction fuel generalizing s with
  | zero =>
    by_cases hb : B < s.count <;>
      simpa only [ComponentExplore.loopResult, hb, ite_true, ite_false, Outcome.pure, Outcome.add,
        Outcome.combine] using hs
  | succ fuel ih =>
    by_cases hb : B < s.count
    · simpa only [ComponentExplore.loopResult, hb, ite_true, Outcome.pure, Outcome.add] using hs
    · cases hp : (ComponentExplore.pendingResult s.points s.processed l).value with
      | none =>
        simpa only [ComponentExplore.loopResult, hb, ite_false, hp, Outcome.pure, Outcome.add,
          Outcome.combine] using hs
      | some x =>
        have ht := scan_invariant w b key a B x l (s.process x) P hs hresolve
        simpa only [ComponentExplore.loopResult, hb, ite_false, hp, Outcome.pure, Outcome.add,
          Outcome.combine] using ih _ ht

theorem component_cache_invariant [Fintype V] (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V) (c : Cache Q)
    (P : Cache Q → Prop) (hc : P c)
    (hresolve : ∀ y ∈ l, ∀ c, P c → P (Cache.resolved b (key y) c).value.2) :
    P (ComponentExplore.result w b key a B l root c).value.memory.cache :=
  loop_invariant w b key a B l (B + 1) (ComponentExplore.initial root c) P hc hresolve

variable {n : ℕ}

theorem callback_cache_invariant (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n)
    (hroot : root ∈ terminals) (c : Cache Q) (P : Cache Q → Prop) (hc : P c)
    (hresolve : ∀ y ∈ terminals, ∀ c, P c → P (Cache.resolved b (key y) c).value.2) :
    ∀ o, Runs w b (BandEvaluation.guardedCallback key a B terminals rho tau root c) o → P o.value.2 := by
  intro o ho
  have he := BandEvaluation.runs_eq_of_evaluates w b _
    (BandEvaluation.guarded_noRandom _ _ _ _ _ _ _ _) _
    (BandEvaluation.guarded_evaluates _ _ _ _ _ _ _ _ _ _) o ho
  rw [he]
  have hr := hresolve root hroot c hc
  dsimp only [BandEvaluation.guardedRun, Outcome.combine, Outcome.add]
  split_ifs
  · rw [BandEvaluation.frontendRun_cache]
    exact component_cache_invariant w b key a B terminals root
      (Cache.resolved b (key root) c).value.2 P hr hresolve
  · exact hr

end SteinerUpperBound.BandEstimator
