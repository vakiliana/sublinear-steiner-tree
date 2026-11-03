module

public import SteinerUpperBound.Covers.OracleProgramSampler

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram.Sampler

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {M Q : Type*} {k s : ℕ}

theorem member_runs {R : Type*} (m : M → ℝ) (b : Q → Bool) (q : Q) (u : Store Q)
    (next : Bool → Store Q → Code M Q R) (o : Outcome R)
    (hr : Runs m b (member q u next) o) :
    ∃ a, Runs m b
      (next (Cache.resolved b q u.cache).value.1
        (u.replaceCache (Cache.resolved b q u.cache).value.2)) a ∧
      o = (Cache.resolved b q u.cache).combine a := by
  classical
  cases he : u.cache q with
  | some v =>
    simp only [member, Cache.resolve, he, Code.bind] at hr
    cases hr with
    | @tick _ _ a hr =>
      refine ⟨a, ?_, ?_⟩
      · simpa only [Cache.resolved, he] using hr
      simp [Cache.resolved, he, Outcome.add, Outcome.combine]
  | none =>
    simp only [member, Cache.resolve, he, Code.bind] at hr
    cases hr with
    | tick hr =>
      cases hr with
      | retained hr =>
        cases hr with
        | @tick _ _ a hr =>
          refine ⟨a, ?_, ?_⟩
          · simpa only [Cache.resolved, he] using hr
          simp [Cache.resolved, he, Outcome.add, Outcome.combine, Nat.add_assoc]
          omega

theorem resolved_counters (b : Q → Bool) (q : Q) (u : Store Q) :
    (Cache.resolved b q u.cache).work ≤ 3 ∧
      (Cache.resolved b q u.cache).metricQueries = 0 ∧
      (Cache.resolved b q u.cache).retentionQueries ≤ 1 ∧
      (Cache.resolved b q u.cache).positiveReplies ≤
        if (Cache.resolved b q u.cache).value.1 then 1 else 0 := by
  cases he : u.cache q with
  | some v => cases v <;> simp [Cache.resolved, he]
  | none => cases hb : b q <;> simp [Cache.resolved, he, hb]

theorem row_resources (m : M → ℝ) (b : Q → Bool) (query : Fin (k + 1) → Q)
    (C used : ℕ) (u : Store Q) (L : ℕ)
    (next : Option (Fin (k + 1)) → ℕ → Store Q → Code M Q (Records Q k s))
    (hn : ∀ label used t o, Runs m b (next label used t) o →
      t.proposals ≤ o.value.store.proposals ∧ o.metricQueries = 0 ∧
      o.retentionQueries ≤ o.value.store.proposals - t.proposals ∧ o.positiveReplies ≤ L ∧
      o.work ≤ 16 * (o.value.store.proposals - t.proposals + L + 1) + 4 ∧
      o.value.store.proposals + o.value.store.remaining = t.proposals + t.remaining) :
    ∀ o, Runs m b (row query C used u next (fun t => .pure (Records.failure s t))) o →
      u.proposals ≤ o.value.store.proposals ∧ o.metricQueries = 0 ∧
      o.retentionQueries ≤ o.value.store.proposals - u.proposals ∧ o.positiveReplies ≤ L + 1 ∧
      o.work ≤ 16 * (o.value.store.proposals - u.proposals + L + 1) + 8 ∧
      o.value.store.proposals + o.value.store.remaining = u.proposals + u.remaining := by
  induction C generalizing used u with
  | zero =>
    intro o hr
    rw [row] at hr
    cases hr with
    | tick hr =>
      have h := hn none used u _ hr
      simp only [Outcome.add] at *
      omega
  | succ C ih =>
    intro o hr
    rw [row] at hr
    cases hr with
    | tick hr =>
      by_cases hu : u.remaining = 0
      · rw [if_pos hu] at hr
        cases hr
        simp [Outcome.add, Outcome.pure, Records.failure] <;> omega
      · rw [if_neg hu] at hr
        cases hr with
        | uniform y hr =>
          cases hr with
          | tick hr =>
            obtain ⟨a, ha, he⟩ := member_runs m b (query y) u.draw _ _ hr
            have hc := resolved_counters b (query y) u.draw
            let t := u.draw.replaceCache (Cache.resolved b (query y) u.draw.cache).value.2
            have htP : t.proposals = u.proposals + 1 := rfl
            have htB : t.remaining = u.remaining - 1 := rfl
            cases hv : (Cache.resolved b (query y) u.draw.cache).value.1 with
            | true =>
              rw [hv, if_pos rfl] at ha
              have h := hn (some y) (used + 1) t _ ha
              simp only [hv, ite_true] at hc
              simp only [he, Outcome.add, Outcome.combine] at *
              omega
            | false =>
              rw [hv, if_neg Bool.false_ne_true] at ha
              have h := ih (used + 1) t _ ha
              simp only [hv, Bool.false_eq_true, ite_false] at hc
              simp only [he, Outcome.add, Outcome.combine] at *
              omega

theorem pool_resources (m : M → ℝ) (b : Q → Bool) (query : Fin (k + 1) → Q)
    (root : Fin (k + 1)) (C s : ℕ) (u : Store Q) :
    ∀ o, Runs m b (pool query root C s u) o →
      u.proposals ≤ o.value.store.proposals ∧ o.metricQueries = 0 ∧
      o.retentionQueries ≤ o.value.store.proposals - u.proposals ∧ o.positiveReplies ≤ s ∧
      o.work ≤ 16 * (o.value.store.proposals - u.proposals + s + 1) ∧
      o.value.store.proposals + o.value.store.remaining = u.proposals + u.remaining := by
  induction s generalizing u with
  | zero =>
    intro o hr
    rw [pool] at hr
    cases hr with
    | tick hr =>
      cases hr
      simp [Outcome.add, Outcome.pure] <;> omega
  | succ s ih =>
    intro o hr
    rw [pool] at hr
    have hn :
        ∀ (label : Option (Fin (k + 1))) (used : ℕ) (t : Store Q) o,
          Runs m b (.tick 3 ((pool query root C s t).map (Records.prepend root label used))) o →
          t.proposals ≤ o.value.store.proposals ∧ o.metricQueries = 0 ∧
          o.retentionQueries ≤ o.value.store.proposals - t.proposals ∧ o.positiveReplies ≤ s ∧
          o.work ≤ 16 * (o.value.store.proposals - t.proposals + s + 1) + 4 ∧
          o.value.store.proposals + o.value.store.remaining = t.proposals + t.remaining := by
      intro label used t o ho
      cases ho with
      | tick ho =>
        obtain ⟨a, ha, rfl⟩ := runs_map_inv m b (pool query root C s t) (Records.prepend root label used) _ ho
        have h := ih t a ha
        simp only [Outcome.add, Outcome.map, Records.prepend] at *
        omega
    have h := row_resources m b query C 0 u s _ hn _ hr
    omega

/-- Every real execution uses at most the proposal cap, but its sharper work
bound charges only proposals actually made, plus the number of records. -/
theorem program_resources (m : M → ℝ) (b : Q → Bool) (query : Fin (k + 1) → Q)
    (root : Fin (k + 1)) (C s B : ℕ) (cache : Q → Option Bool)
    (seed : ((program query root C s B cache : Code M Q (Records Q k s)).compile m).Seed) :
    let o := (((program query root C s B cache : Code M Q (Records Q k s)).compile m).tree seed).output b
    o.metricQueries = 0 ∧ o.retentionQueries ≤ o.value.store.proposals ∧
      o.positiveReplies ≤ s ∧ o.work ≤ 16 * (o.value.store.proposals + s + 1) ∧
      o.value.store.proposals ≤ B := by
  have h := pool_resources m b query root C s (Store.initial cache B) _
    (runs_compile m b (program query root C s B cache) seed)
  simp only [Store.initial, Nat.sub_zero, Nat.zero_add] at h
  omega

theorem program_positive_tail_zero (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ) (cache : Q → Option Bool) :
    (program query root C s B cache : Code M Q (Records Q k s)).evaluate m b
      (fun o => threshold (s : ℝ) o.positiveReplies) = 0 := by
  rw [← Code.compile_expect]
  unfold Compiled.expect
  have he :
      (fun seed => threshold (s : ℝ)
        ((((program query root C s B cache : Code M Q (Records Q k s)).compile m).tree seed).output b).positiveReplies) =
      (fun _ => (0 : ℝ)) := by
    funext seed
    have hp := (program_resources m b query root C s B cache seed).2.2.1
    have hR : ((((program query root C s B cache : Code M Q (Records Q k s)).compile m).tree seed).output b).positiveReplies ≤ s := hp
    have hR' : (((((program query root C s B cache : Code M Q (Records Q k s)).compile m).tree seed).output b).positiveReplies : ℝ) ≤ s := by
      exact_mod_cast hR
    simp only [threshold, not_lt_of_ge hR', ite_false]
  rw [he, Law.expect_const]

end SteinerUpperBound.Covers.OracleProgram.Sampler
