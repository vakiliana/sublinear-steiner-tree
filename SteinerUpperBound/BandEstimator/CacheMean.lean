module

public import SteinerUpperBound.BandEstimator.CacheComponent

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.BandEstimator

open QueryProgram Covers.OracleProgram
open scoped Classical

variable {M Q R U : Type*} {k : ℕ}

private theorem sampler_row_invariant (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (C used : ℕ) (u : Sampler.Store Q)
    (P : Cache Q → Prop) (hu : P u.cache)
    (hresolve : ∀ y c, P c → P (Cache.resolved b (query y) c).value.2)
    (next : Option (Fin (k + 1)) → ℕ → Sampler.Store Q → Code M Q R)
    (abort : Sampler.Store Q → Code M Q R) (getCache : R → Cache Q)
    (hn : ∀ label used t, P t.cache → ∀ o, Runs m b (next label used t) o → P (getCache o.value))
    (ha : ∀ t, P t.cache → ∀ o, Runs m b (abort t) o → P (getCache o.value)) :
    ∀ o, Runs m b (Sampler.row query C used u next abort) o → P (getCache o.value) := by
  induction C generalizing used u with
  | zero =>
    intro o ho
    rw [Sampler.row] at ho
    cases ho with
    | tick ho =>
      have h := hn none used u hu _ ho
      exact h
  | succ C ih =>
    intro o ho
    rw [Sampler.row] at ho
    cases ho with
    | tick ho =>
      by_cases hB : u.remaining = 0
      · rw [ite_eq_left hB] at ho
        have h := ha u hu _ ho
        exact h
      · rw [ite_eq_right hB] at ho
        cases ho with
        | uniform y ho =>
          cases ho with
          | tick ho =>
            obtain ⟨a, ha', he⟩ := Sampler.member_runs m b (query y) u.draw _ _ ho
            let t := u.draw.replaceCache (Cache.resolved b (query y) u.draw.cache).value.2
            have ht : P t.cache := hresolve y u.draw.cache hu
            cases hv : (Cache.resolved b (query y) u.draw.cache).value.1 with
            | true =>
              rw [hv, ite_eq_left rfl] at ha'
              simpa only [he, Outcome.add, Outcome.combine] using hn (some y) (used + 1) t ht _ ha'
            | false =>
              rw [hv, ite_eq_right Bool.false_ne_true] at ha'
              simpa only [he, Outcome.add, Outcome.combine] using ih (used + 1) t ht _ ha'

private theorem sampler_pool_invariant (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s : ℕ) (u : Sampler.Store Q)
    (P : Cache Q → Prop) (hu : P u.cache)
    (hresolve : ∀ y c, P c → P (Cache.resolved b (query y) c).value.2) :
    ∀ o, Runs m b (Sampler.pool query root C s u) o → P o.value.store.cache := by
  induction s generalizing u with
  | zero =>
    intro o ho
    rw [Sampler.pool] at ho
    cases ho with
    | tick ho => cases ho; exact hu
  | succ s ih =>
    intro o ho
    apply sampler_row_invariant m b query C 0 u P hu hresolve _ _ (fun r => r.store.cache) _ _ o ho
    · intro label used t ht z hz
      cases hz with
      | tick hz =>
        obtain ⟨a, ha, rfl⟩ := runs_map_inv m b (Sampler.pool query root C s t) _ _ hz
        exact ih t ht _ ha
    · intro t ht z hz
      cases hz
      exact ht

private theorem scores_invariant (m : M → ℝ) (b : Q → Bool) (callback : Mean.Callback M Q U)
    (P : Cache Q → Prop)
    (hcallback : ∀ u c, P c → ∀ o, Runs m b (callback u c) o → P o.value.2)
    (s : ℕ) (labels : Fin s → U) (c : Cache Q) (hc : P c) :
    ∀ o, Runs m b (Mean.scores callback s labels c) o → P o.value.2 := by
  induction s generalizing c with
  | zero =>
    intro o ho
    rw [Mean.scores] at ho
    cases ho with
    | tick ho => cases ho; exact hc
  | succ s ih =>
    intro o ho
    rw [Mean.scores] at ho
    cases ho with
    | tick ho =>
      obtain ⟨a, z, ha, hz, rfl⟩ := Mean.runs_bind_inv m b (callback (labels 0) c) _ _ ho
      have ha' := hcallback (labels 0) c hc a ha
      obtain ⟨a', z', ha'', hz', rfl⟩ := Mean.runs_bind_inv m b
        (Mean.scores callback s (Fin.tail labels) a.value.2) _ _ hz
      cases hz' with
      | tick hz' =>
        cases hz'
        exact ih (Fin.tail labels) a.value.2 ha' a' ha''

private theorem afterSample_invariant (m : M → ℝ) (b : Q → Bool)
    (callback : Mean.Callback M Q (Fin (k + 1))) (P : Cache Q → Prop)
    (hcallback : ∀ u c, P c → ∀ o, Runs m b (callback u c) o → P o.value.2)
    (s : ℕ) (ξ : ℝ) (r : Sampler.Records Q k s) (hc : P r.store.cache) :
    ∀ o, Runs m b (Mean.afterSample ξ callback r) o → P o.value.cache := by
  intro o ho
  rw [Mean.afterSample] at ho
  cases ho with
  | tick ho =>
    cases he : r.labels with
    | none =>
      simp only [he] at ho
      cases ho with
      | tick ho => cases ho; exact hc
    | some labels =>
      simp only [he] at ho
      cases hs : r.successful with
      | false =>
        simp only [hs, Bool.false_eq_true, ite_false] at ho
        cases ho with
        | tick ho => cases ho; exact hc
      | true =>
        simp only [hs, ite_true] at ho
        obtain ⟨a, z, ha, hz, rfl⟩ := Mean.runs_bind_inv m b
          (Mean.scores callback s labels r.store.cache) _ _ ho
        cases hz with
        | tick hz =>
          cases hz
          exact scores_invariant m b callback P hcallback s labels r.store.cache hc a ha

theorem mean_cache_invariant (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ) (c : Cache Q) (ξ : ℝ)
    (callback : Mean.Callback M Q (Fin (k + 1))) (P : Cache Q → Prop) (hc : P c)
    (hresolve : ∀ y c, P c → P (Cache.resolved b (query y) c).value.2)
    (hcallback : ∀ u c, P c → ∀ o, Runs m b (callback u c) o → P o.value.2) :
    ∀ o, Runs m b (Mean.program query root C s B c ξ callback) o → P o.value.cache := by
  intro o ho
  obtain ⟨a, z, ha, hz, rfl⟩ := Mean.runs_bind_inv m b
    (Sampler.program query root C s B c) _ _ ho
  have hcache := sampler_pool_invariant m b query root C s (Sampler.Store.initial c B) P hc hresolve a ha
  exact afterSample_invariant m b callback P hcallback s ξ a.value hcache z hz

end SteinerUpperBound.BandEstimator
