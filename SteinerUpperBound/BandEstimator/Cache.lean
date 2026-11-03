module

public import SteinerUpperBound.BandEstimator.CacheMean
public import SteinerUpperBound.BandEstimator.Stage

@[expose] public section

namespace SteinerUpperBound.BandEstimator

open QueryProgram MSTApproximation Covers.OracleProgram
open scoped Classical

variable {Q : Type*} {n k : ℕ}

def allowed (g : Grid) (key : Index g → Fin n → Q) (terminals : List (Fin n)) (q : Q) : Prop :=
  ∃ i x, x ∈ terminals ∧ key i x = q

private theorem stage_invariant (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (key : Index g → Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (hlabels : ∀ u, label u ∈ terminals)
    (d : Data) (i : Index g) (c : Cache Q) (P : Cache Q → Prop) (hc : P c)
    (hresolve : ∀ i y, y ∈ terminals → ∀ c, P c → P (Cache.resolved b (key i y) c).value.2) :
    ∀ o, Runs w b (stage g label key root terminals d i c) o → P o.value.2 := by
  intro o ho
  obtain ⟨r, hr, rfl⟩ := stage_runs w b g label key root terminals d i c o ho
  exact mean_cache_invariant w b (fun u => key i (label u)) root d.rowCap d.samples d.totalCap c
    (accuracy d) (BandEvaluation.indexedCallback label (key i) (g.scale i.val) d.cutoff terminals
      (EstimatorParameters.deltaCoarse * g.scale i.val) EstimatorParameters.tau)
    P hc (fun u => hresolve i (label u) (hlabels u))
    (fun u c hc => callback_cache_invariant w b (key i) (g.scale i.val) d.cutoff terminals
      (EstimatorParameters.deltaCoarse * g.scale i.val) EstimatorParameters.tau (label u)
      (hlabels u) c P hc (hresolve i)) r hr

private theorem rounds_invariant (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (key : Index g → Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (hlabels : ∀ u, label u ∈ terminals) (d : Data)
    (indices : List (Index g)) (total : Option ℝ) (c : Cache Q) (P : Cache Q → Prop) (hc : P c)
    (hresolve : ∀ i y, y ∈ terminals → ∀ c, P c → P (Cache.resolved b (key i y) c).value.2) :
    ∀ o, Runs w b (rounds g label key root terminals d indices total c) o → P o.value.2 := by
  induction indices generalizing total c with
  | nil =>
    intro o ho
    rw [rounds] at ho
    cases ho with
    | tick ho => cases ho; exact hc
  | cons i l ih =>
    intro o ho
    rw [rounds] at ho
    obtain ⟨r, z, hr, hz, rfl⟩ := Mean.runs_bind_inv w b (stage g label key root terminals d i c) _ _ ho
    have ht := stage_invariant w b g label key root terminals hlabels d i c P hc hresolve r hr
    cases hz with
    | tick hz =>
      have h := ih (add total r.value.1) r.value.2 ht _ hz
      exact h

theorem program_cache_frame (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (key : Index g → Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (hlabels : ∀ u, label u ∈ terminals) (d : Data) (c : Cache Q) :
    ∀ o, Runs w b (program g label key root terminals d c) o →
      CacheFrame (allowed g key terminals) c o.value.2 := by
  intro o ho
  rw [program] at ho
  cases ho with
  | tick ho =>
    have h := rounds_invariant w b g label key root terminals hlabels d
      (List.finRange (g.intervals + 1)) (some 0) c (CacheFrame (allowed g key terminals) c)
      (cacheFrame_refl _ _) (fun i y hy c hc =>
        cacheFrame_resolved _ _ c b (key i y) ⟨i, y, hy, rfl⟩ hc) _ ho
    exact h

theorem program_compiled_cache_frame (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (key : Index g → Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (hlabels : ∀ u, label u ∈ terminals) (d : Data) (c : Cache Q)
    (seed : ((program g label key root terminals d c).compile w).Seed) :
    CacheFrame (allowed g key terminals) c
      ((((program g label key root terminals d c).compile w).tree seed).output b).value.2 :=
  program_cache_frame w b g label key root terminals hlabels d c _ (runs_compile w b _ seed)

theorem fromParameters_cache_frame (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (key : Index g → Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (hlabels : ∀ u, label u ∈ terminals)
    (p : EstimatorParameters.PublicParameters) (c : Cache Q) :
    ∀ o, Runs w b (fromParameters g label key root terminals p c) o →
      CacheFrame (allowed g key terminals) c o.value.2 := by
  intro o ho
  rw [fromParameters] at ho
  cases ho with
  | tick ho =>
    have h := program_cache_frame w b g label key root terminals hlabels (ofParameters p (k + 1)) c _ ho
    exact h

end SteinerUpperBound.BandEstimator
