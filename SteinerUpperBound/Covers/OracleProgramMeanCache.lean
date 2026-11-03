module

public import SteinerUpperBound.Covers.OracleProgramMeanBasic

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram.Mean

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {M Q U A : Type*}

/-- Modular refinement of one actual callback. Its value kernel is independent
of the incoming correct cache. Cache updates may depend on the sampled value;
neither their independence nor empirical accuracy is assumed. -/
structure KernelSpec [Fintype A] (callback : Callback M Q U)
    (m : M → ℝ) (b : Q → Bool) (kernel : U → Law A) (score : U → A → ℝ) : Prop where
  cache_correct : ∀ u c, Cache.Correct b c → ∀ o, Runs m b (callback u c) o →
    Cache.Correct b o.value.2
  value_law : ∀ u c, Cache.Correct b c → ∀ F : ℝ → ℝ,
    (callback u c).evaluate m b (fun o => F o.value.1) =
      (kernel u).expect (fun a => F (score u a))

theorem KernelSpec.continuation [Fintype A] {callback : Callback M Q U}
    {m : M → ℝ} {b : Q → Bool} {kernel : U → Law A} {score : U → A → ℝ}
    (h : KernelSpec callback m b kernel score) (u : U) (c : Cache Q)
    (hc : Cache.Correct b c) (F : ℝ × Cache Q → ℝ) (G : ℝ → ℝ)
    (hFG : ∀ z d, Cache.Correct b d → F (z, d) = G z) :
    (callback u c).evaluate m b (fun o => F o.value) =
      (kernel u).expect (fun a => G (score u a)) := by
  calc
    _ = (callback u c).evaluate m b (fun o => G o.value.1) := by
      apply evaluate_congr_runs
      intro o ho
      exact hFG o.value.1 o.value.2 (h.cache_correct u c hc o ho)
    _ = _ := h.value_law u c hc G

theorem KernelSpec.of_deterministic (callback : Callback M Q U)
    (m : M → ℝ) (b : Q → Bool) (score : U → ℝ)
    (hcache : ∀ u c, Cache.Correct b c → ∀ o, Runs m b (callback u c) o →
      Cache.Correct b o.value.2)
    (hlaw : ∀ u c, Cache.Correct b c → ∀ F : ℝ → ℝ,
      (callback u c).evaluate m b (fun o => F o.value.1) = F (score u)) :
    KernelSpec callback m b (fun _ => Law.pure ()) (fun u _ => score u) := by
  refine ⟨hcache, ?_⟩
  intro u c hc F
  simpa only [Law.expect_pure] using hlaw u c hc F

theorem sampler_row_cache {R : Type*} {k : ℕ} (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (C used : ℕ) (u : Sampler.Store Q)
    (hc : Cache.Correct b u.cache)
    (next : Option (Fin (k + 1)) → ℕ → Sampler.Store Q → Code M Q R)
    (abort : Sampler.Store Q → Code M Q R) (getCache : R → Cache Q)
    (hn : ∀ label used t, Cache.Correct b t.cache → ∀ o,
      Runs m b (next label used t) o → Cache.Correct b (getCache o.value))
    (ha : ∀ t, Cache.Correct b t.cache → ∀ o,
      Runs m b (abort t) o → Cache.Correct b (getCache o.value)) :
    ∀ o, Runs m b (Sampler.row query C used u next abort) o →
      Cache.Correct b (getCache o.value) := by
  induction C generalizing used u with
  | zero =>
    intro o ho
    rw [Sampler.row] at ho
    cases ho with
    | tick ho =>
      have h := hn none used u hc _ ho
      exact h
  | succ C ih =>
    intro o ho
    rw [Sampler.row] at ho
    cases ho with
    | tick ho =>
      by_cases hB : u.remaining = 0
      · rw [ite_eq_left hB] at ho
        have h := ha u hc _ ho
        exact h
      · rw [ite_eq_right hB] at ho
        cases ho with
        | uniform y ho =>
          cases ho with
          | tick ho =>
            obtain ⟨a, ha', he⟩ := Sampler.member_runs m b (query y) u.draw _ _ ho
            let t := u.draw.replaceCache (Cache.resolved b (query y) u.draw.cache).value.2
            have ht : Cache.Correct b t.cache :=
              (Sampler.member_correct b (query y) u.draw hc).2
            cases hv : (Cache.resolved b (query y) u.draw.cache).value.1 with
            | true =>
              rw [hv, ite_eq_left rfl] at ha'
              have h := hn (some y) (used + 1) t ht _ ha'
              simpa only [he, Outcome.add, Outcome.combine] using h
            | false =>
              rw [hv, ite_eq_right Bool.false_ne_true] at ha'
              have h := ih (used + 1) t ht _ ha'
              simpa only [he, Outcome.add, Outcome.combine] using h

theorem sampler_pool_cache {k : ℕ} (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s : ℕ) (u : Sampler.Store Q)
    (hc : Cache.Correct b u.cache) :
    ∀ o, Runs m b (Sampler.pool query root C s u) o →
      Cache.Correct b o.value.store.cache := by
  induction s generalizing u with
  | zero =>
    intro o ho
    rw [Sampler.pool] at ho
    cases ho with
    | tick ho =>
      cases ho
      exact hc
  | succ s ih =>
    intro o ho
    apply sampler_row_cache m b query C 0 u hc _ _ (fun r => r.store.cache) _ _ o ho
    · intro label used t ht z hz
      cases hz with
      | tick hz =>
        obtain ⟨a, ha, rfl⟩ := runs_map_inv m b (Sampler.pool query root C s t) _ _ hz
        exact ih t ht _ ha
    · intro t ht z hz
      cases hz
      exact ht

theorem sampler_cache_correct {k : ℕ} (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ) (c : Cache Q)
    (hc : Cache.Correct b c) :
    ∀ o, Runs m b (Sampler.program query root C s B c) o →
      Cache.Correct b o.value.store.cache :=
  sampler_pool_cache m b query root C s (Sampler.Store.initial c B) hc

theorem scores_cache_correct [Fintype A] {callback : Callback M Q U}
    {m : M → ℝ} {b : Q → Bool} {kernel : U → Law A} {score : U → A → ℝ}
    (h : KernelSpec callback m b kernel score) (s : ℕ) (labels : Fin s → U)
    (c : Cache Q) (hc : Cache.Correct b c) :
    ∀ o, Runs m b (scores callback s labels c) o → Cache.Correct b o.value.2 := by
  induction s generalizing c with
  | zero =>
    intro o ho
    rw [scores] at ho
    cases ho with
    | tick ho => cases ho; exact hc
  | succ s ih =>
    intro o ho
    rw [scores] at ho
    cases ho with
    | tick ho =>
      obtain ⟨a, z, ha, hz, rfl⟩ := runs_bind_inv m b (callback (labels 0) c) _ _ ho
      have ha' := h.cache_correct (labels 0) c hc a ha
      obtain ⟨a', z', ha'', hz', rfl⟩ := runs_bind_inv m b
        (scores callback s (Fin.tail labels) a.value.2) _ _ hz
      cases hz' with
      | tick hz' =>
        cases hz'
        have ht := ih (Fin.tail labels) a.value.2 ha' a' ha''
        exact ht

theorem afterSample_cache_correct [Fintype A] {k s : ℕ}
    {callback : Callback M Q (Fin (k + 1))} {m : M → ℝ} {b : Q → Bool}
    {kernel : Fin (k + 1) → Law A} {score : Fin (k + 1) → A → ℝ}
    (h : KernelSpec callback m b kernel score) (ξ : ℝ) (r : Sampler.Records Q k s)
    (hc : Cache.Correct b r.store.cache) :
    ∀ o, Runs m b (afterSample ξ callback r) o → Cache.Correct b o.value.cache := by
  intro o ho
  rw [afterSample] at ho
  cases ho with
  | tick ho =>
    cases he : r.labels with
    | none =>
      rw [he] at ho
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
        obtain ⟨a, z, ha, hz, rfl⟩ := runs_bind_inv m b (scores callback s labels r.store.cache) _ _ ho
        cases hz with
        | tick hz =>
          cases hz
          exact scores_cache_correct h s labels r.store.cache hc a ha

theorem program_cache_correct [Fintype A] {k : ℕ}
    {callback : Callback M Q (Fin (k + 1))} {m : M → ℝ} {b : Q → Bool}
    {kernel : Fin (k + 1) → Law A} {score : Fin (k + 1) → A → ℝ}
    (h : KernelSpec callback m b kernel score)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ) (c : Cache Q)
    (hc : Cache.Correct b c) (ξ : ℝ) :
    ∀ o, Runs m b (program query root C s B c ξ callback) o →
      Cache.Correct b o.value.cache := by
  intro o ho
  obtain ⟨a, z, ha, hz, rfl⟩ := runs_bind_inv m b (Sampler.program query root C s B c) _ _ ho
  exact afterSample_cache_correct h ξ a.value
    (sampler_cache_correct m b query root C s B c hc a ha) z hz

end SteinerUpperBound.Covers.OracleProgram.Mean
