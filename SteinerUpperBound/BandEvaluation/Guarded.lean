module

public import SteinerUpperBound.BandEvaluation.Frontend

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical

variable {Q U : Type*} {n : ℕ}

/-- The guard supplies the all-public-label refinement required by the mean helper. -/
noncomputable def guardedCallback (key : Fin n → Q) (a : ℝ) (B : ℕ) (terminals : List (Fin n))
    (rho tau : ℝ) (root : Fin n) (c : Cache Q) : Code (Sym2 (Fin n)) Q (ℝ × Cache Q) :=
  (Cache.resolve (key root) c).bind (fun r => .tick 3 (if r.1 then
    frontend key a B terminals rho tau root r.2 else .pure (0, r.2)))

noncomputable def guardedRun (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q) :
    Outcome (ℝ × Cache Q) :=
  let r := Cache.resolved b (key root) c
  r.combine ((if r.value.1 then frontendRun w b key a B terminals rho tau root r.value.2
    else Outcome.pure (0, r.value.2)).add 4 0 0 0)

theorem guarded_evaluates (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q) :
    Code.Evaluates w b (guardedCallback key a B terminals rho tau root c)
      (guardedRun w b key a B terminals rho tau root c) := by
  apply Code.Evaluates.bind _ _ _ _ _ _ (Cache.resolve_evaluates _ _ _ _)
  apply Code.Evaluates.tick
  split_ifs
  · exact frontend_evaluates _ _ _ _ _ _ _ _ _ _
  · exact Code.evaluates_pure _ _ _

theorem guarded_noRandom (key : Fin n → Q) (a : ℝ) (B : ℕ) (terminals : List (Fin n))
    (rho tau : ℝ) (root : Fin n) (c : Cache Q) :
    NoRandom (guardedCallback key a B terminals rho tau root c) := by
  apply noRandom_bind _ _ (resolve_noRandom _ _)
  intro r
  split_ifs
  · exact frontend_noRandom _ _ _ _ _ _ _ _
  · trivial

theorem guarded_cache_correct (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct b c) :
    Cache.Correct b (guardedRun w b key a B terminals rho tau root c).value.2 := by
  have hr := (Cache.resolved_correct b (key root) c hc).2
  dsimp only [guardedRun, Outcome.combine, Outcome.add]
  split_ifs
  · exact frontendRun_cache_correct _ _ _ _ _ _ _ _ _ _ hr
  · exact hr

theorem guarded_correct (I : Instance (Fin n)) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n)
    (hrT : root ∈ terminals) (c : Cache Q) (hc : Cache.Correct b c)
    (hband : tau * a ≤ a - 2 * rho) :
    (guardedRun I.weight b key a B terminals rho tau root c).value.1 =
      pointScore I (retainedSet b key terminals) a rho tau B root := by
  classical
  let : DecidableEq (Fin n) := Classical.decEq _
  have hr := Cache.resolved_correct b (key root) c hc
  cases hb : b (key root) with
  | false =>
      have hn : root ∉ retainedSet b key terminals := by
        intro h
        have ht := (Finset.mem_filter.mp h).2
        simp only [hb, Bool.false_eq_true] at ht
      rw [pointScore_outside I _ a rho tau B root hn]
      simp only [guardedRun, hr.1, hb, Bool.false_eq_true, ↓reduceIte,
        Outcome.combine, Outcome.add, Outcome.pure]
  | true =>
      have hroot : root ∈ retainedSet b key terminals :=
        Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hrT, hb⟩
      have hh := frontendRun_correct I b key a B terminals rho tau root
        (Cache.resolved b (key root) c).value.2 hr.2 hroot hband
      simpa only [guardedRun, hr.1, hb, ↓reduceIte, Outcome.combine, Outcome.add] using hh

noncomputable def indexedCallback (label : U → Fin n) (key : Fin n → Q) (a : ℝ) (B : ℕ)
    (terminals : List (Fin n)) (rho tau : ℝ) : Mean.Callback (Sym2 (Fin n)) Q U :=
  fun u c => guardedCallback key a B terminals rho tau (label u) c

theorem callback_kernel (I : Instance (Fin n)) (b : Q → Bool) (label : U → Fin n)
    (key : Fin n → Q) (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ)
    (hlabel : ∀ u, label u ∈ terminals) (hband : tau * a ≤ a - 2 * rho) :
    Mean.KernelSpec (indexedCallback label key a B terminals rho tau) I.weight b
      (fun _ => Law.pure ()) (fun u _ => pointScore I (retainedSet b key terminals) a rho tau B (label u)) := by
  apply Mean.KernelSpec.of_deterministic
  · intro u c hc o ho
    have he := runs_eq_of_evaluates I.weight b
      (guardedCallback key a B terminals rho tau (label u) c)
      (guarded_noRandom _ _ _ _ _ _ _ _) _
      (guarded_evaluates _ _ _ _ _ _ _ _ _ _) o ho
    rw [he]
    exact guarded_cache_correct _ _ _ _ _ _ _ _ _ _ hc
  · intro u c hc F
    change (guardedCallback key a B terminals rho tau (label u) c).evaluate I.weight b
      (fun o => F o.value.1) = _
    rw [guarded_evaluates]
    rw [guarded_correct I b key a B terminals rho tau (label u) (hlabel u) c hc hband]

theorem guarded_positive (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q) :
    (guardedRun w b key a B terminals rho tau root c).positiveReplies ≤ B + 1 := by
  have hr := Cache.resolved_positive_le b (key root) c
  have hf := frontendRun_positive w b key a B terminals rho tau root (Cache.resolved b (key root) c).value.2
  dsimp only [guardedRun, Outcome.combine, Outcome.add, Outcome.pure]
  split_ifs <;> (try dsimp only) <;> omega

theorem guarded_positive_cached (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q)
    (hc : c (key root) = some true) :
    (guardedRun w b key a B terminals rho tau root c).positiveReplies ≤ B := by
  simpa only [guardedRun, Cache.resolved, hc, ↓reduceIte, Outcome.combine, Outcome.add,
    Nat.zero_add] using frontendRun_positive w b key a B terminals rho tau root c

theorem guarded_queries (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct b c) :
    (guardedRun w b key a B terminals rho tau root c).metricQueries ≤
      (n + terminals.length) * (B + 1) := by
  have hr := (Cache.resolved_correct b (key root) c hc).2
  have hf := frontendRun_queries w b key a B terminals rho tau root
    (Cache.resolved b (key root) c).value.2 hr
  have hm : (Cache.resolved b (key root) c).metricQueries = 0 := by
    unfold Cache.resolved
    cases c (key root) <;> rfl
  dsimp only [guardedRun, Outcome.combine, Outcome.add, Outcome.pure]
  split_ifs <;> (try dsimp only) <;> omega

theorem guarded_work (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct b c) :
    (guardedRun w b key a B terminals rho tau root c).work ≤
      40000000000 * (n + terminals.length + 1) * (B + 2) ^ 12 := by
  have hr := Cache.resolved_work_le b (key root) c
  have hc' := (Cache.resolved_correct b (key root) c hc).2
  have hf := frontendRun_work w b key a B terminals rho tau root
    (Cache.resolved b (key root) c).value.2 hc'
  have hp : 1 ≤ (n + terminals.length + 1) * (B + 2) ^ 12 := by
    have hh : 0 < (n + terminals.length + 1) * (B + 2) ^ 12 := by positivity
    omega
  dsimp only [guardedRun, Outcome.combine, Outcome.add, Outcome.pure]
  split_ifs <;> nlinarith

end SteinerUpperBound.BandEvaluation
