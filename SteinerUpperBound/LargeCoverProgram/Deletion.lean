module

public import SteinerUpperBound.LargeCoverProgram.Basic

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

variable {Q : Type*} {n k : ℕ}

noncomputable def deletionValue (w : Sym2 (Fin n) → ℝ) (a : ℝ) (bits : Fin n → Bool) :
    Selection (Fin n) × Vector Bool n :=
  let selected := selectionValue (fun v : Fin n => v) bits
  (selected, (LocalAccess.coveredResult w (5 * a / 8) selected.centers).value)

theorem deletionAfterPool_value (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (a : ℝ)
    (records : Sampler.Records Q k p.poolSamples)
    (F : Option (Selection (Fin n) × Vector Bool n) → ℝ) :
    (deletionAfterPool p terminals a records).evaluate w bits (fun o => F o.value.value) =
      (Mean.selected (Sampler.Observation.ofRecords records)).elim (F none) (fun labels =>
        (ReusableSample.rationalMatrixMechanism p.Lbar p.poolSamples p.t
          (ReusableSample.OracleProgram.observedMatrix w (fun v : Fin n => v)
            (fun i => terminals.get (labels i)) (5 * a / 8))).expect
          (fun T => F (some (deletionValue w a T)))) := by
  cases hl : records.labels with
  | none => simp [deletionAfterPool, Mean.selected, Sampler.Observation.ofRecords, hl,
      Code.evaluate, Outcome.add, Outcome.pure]
  | some labels =>
      cases hs : records.successful
      · simp [deletionAfterPool, Mean.selected, Sampler.Observation.ofRecords, hl, hs,
          Code.evaluate, Outcome.add, Outcome.pure]
      · simp only [deletionAfterPool, hl, hs, ite_true, Code.evaluate, Outcome.add,
          Mean.selected, Sampler.Observation.ofRecords, Option.elim_some]
        rw [Code.evaluate_bind]
        have he : (fun o : Outcome (Fin n → Bool) =>
            (((selectionProgram (fun v : Fin n => v) o.value).bind fun selected =>
              (LocalAccess.coveredProgram (5 * a / 8) selected.centers).bind fun D =>
                .tick 3 (.pure (⟨some (selected, D), records.store.cache⟩ : Deletion Q n)))).evaluate w bits
              (fun z => F (o.combine z).value.value)) =
            fun o => F (some (deletionValue w a o.value)) := by
          funext o
          rw [Code.evaluate_bind, selection_evaluates w bits, Code.evaluate_bind,
            LocalAccess.covered_evaluates w bits]
          simp only [Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure,
            deletionValue, selection_value]
        rw [he]
        exact ReusableSample.OracleProgram.program_evaluate w bits _ _ _ _ _
          (fun T => F (some (deletionValue w a T)))

def deletionWork (n : ℕ) (p : Parameters) : ℕ :=
  16 * (p.poolProposals + p.poolSamples + 1) +
    ReusableSample.OracleProgram.workBound n p.poolSamples + (2 * p.t + 12) * n + 16

theorem deletionAfterPool_resources (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (a : ℝ)
    (records : Sampler.Records Q k p.poolSamples) :
    ∀ o, Runs w bits (deletionAfterPool p terminals a records) o →
      o.value.cache = records.store.cache ∧
      o.work ≤ ReusableSample.OracleProgram.workBound n p.poolSamples +
        (2 * p.t + 12) * n + 16 ∧
      o.metricQueries ≤ n * p.poolSamples + n * p.t ∧
      o.retentionQueries = 0 ∧ o.positiveReplies = 0 ∧
      ∀ selected D, o.value.value = some (selected, D) →
        selected.count ≤ p.t ∧ selected.centers.length = selected.count ∧
        selected.centers.Nodup ∧ D = (LocalAccess.coveredResult w (5 * a / 8) selected.centers).value := by
  intro o ho
  rw [deletionAfterPool] at ho
  cases ho with
  | tick ho =>
      cases hl : records.labels with
      | none =>
          simp only [hl] at ho
          cases ho
          simp [Outcome.add, Outcome.pure]
      | some labels =>
          simp only [hl] at ho
          cases hs : records.successful
          · simp only [hs, Bool.false_eq_true, ite_false] at ho
            cases ho
            simp [Outcome.add, Outcome.pure]
          · simp only [hs, ite_true] at ho
            obtain ⟨noise, tail, hn, ht, rfl⟩ := Mean.runs_bind_inv w bits
              (ReusableSample.OracleProgram.program (fun v : Fin n => v)
                (fun i => terminals.get (labels i)) (5 * a / 8) p.t p.Lbar) _ _ ho
            have hn' : ReusableSample.acceptances noise.value ≤ p.t ∧
                noise.work ≤ ReusableSample.OracleProgram.workBound n p.poolSamples ∧
                noise.metricQueries = n * p.poolSamples ∧ noise.retentionQueries = 0 ∧
                noise.positiveReplies = 0 := Mean.runs_of_compiled w bits _
              (fun o => ReusableSample.acceptances o.value ≤ p.t ∧
                o.work ≤ ReusableSample.OracleProgram.workBound n p.poolSamples ∧
                o.metricQueries = n * p.poolSamples ∧ o.retentionQueries = 0 ∧ o.positiveReplies = 0)
              (fun seed => ReusableSample.OracleProgram.program_resources w bits _ _ _ _ _ seed) noise hn
            obtain ⟨selected, rest, hsel, hrest, rfl⟩ := Mean.runs_bind_inv w bits
              (selectionProgram (fun v : Fin n => v) noise.value) _ _ ht
            have he := deterministic_run_eq w bits _ (selection_deterministic _ _) _
              (selection_evaluates w bits _ _) selected hsel
            subst selected
            obtain ⟨Dout, last, hD, hlast, rfl⟩ := Mean.runs_bind_inv w bits
              (LocalAccess.coveredProgram (5 * a / 8)
                (selectionResult (fun v : Fin n => v) noise.value).value.centers) _ _ hrest
            have he := deterministic_run_eq w bits _ (covered_deterministic _ _) _
              (LocalAccess.covered_evaluates w bits _ _) Dout hD
            subst Dout
            cases hlast with
            | tick hlast =>
                cases hlast
                have hsc := selection_count (fun v : Fin n => v) noise.value
                have hsr := selection_resources (fun v : Fin n => v) noise.value
                have hlen : (selectionResult (fun v : Fin n => v) noise.value).value.centers.length ≤ p.t := by
                  rw [selection_value, hsc.2, hsc.1]
                  exact hn'.1
                have hcw := LocalAccess.covered_work w (5 * a / 8)
                  (selectionResult (fun v : Fin n => v) noise.value).value.centers
                have hcq := LocalAccess.covered_queries w (5 * a / 8)
                  (selectionResult (fun v : Fin n => v) noise.value).value.centers
                have hcz := LocalAccess.covered_counters w (5 * a / 8)
                  (selectionResult (fun v : Fin n => v) noise.value).value.centers
                dsimp only [Outcome.add, Outcome.combine, Outcome.pure]
                refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
                · nlinarith [hn'.2.1, hsr.1]
                · nlinarith [hn'.2.2.1, hsr.2.1]
                · simp [hn'.2.2.2.1, hsr.2.2.1, hcz.1]
                · simp [hn'.2.2.2.2, hsr.2.2.2, hcz.2]
                · intro selected D h
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
                  rw [selection_value]
                  exact ⟨by rw [hsc.1]; exact hn'.1, hsc.2,
                    selection_nodup (fun v : Fin n => v) (fun _ _ h => h) _, rfl⟩

theorem deletion_cache_resources (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ) (c : Cache Q) (hc : Cache.Correct bits c) :
    ∀ o, Runs w bits (deletion p terminals root key a c) o →
      Cache.Correct bits o.value.cache ∧ o.work ≤ deletionWork n p ∧
      o.metricQueries ≤ n * p.poolSamples + n * p.t ∧
      o.positiveReplies ≤ p.poolSamples ∧
      ∀ selected D, o.value.value = some (selected, D) →
        selected.count ≤ p.t ∧ selected.centers.length = selected.count ∧ selected.centers.Nodup := by
  intro o ho
  obtain ⟨sample, next, hs, hn, rfl⟩ := Mean.runs_bind_inv w bits
    (Sampler.program (fun i => key (terminals.get i)) root p.poolRowCap p.poolSamples p.poolProposals c)
    _ _ ho
  have hr := Sampler.pool_resources w bits (fun i => key (terminals.get i)) root
    p.poolRowCap p.poolSamples (Sampler.Store.initial c p.poolProposals) sample hs
  have hcache := Mean.sampler_cache_correct w bits _ root _ _ _ c hc sample hs
  have hnext := deletionAfterPool_resources w bits p terminals a sample.value next hn
  have hproposals : sample.value.store.proposals ≤ p.poolProposals := by
    dsimp [Sampler.Store.initial] at hr
    omega
  simp only [Outcome.combine]
  refine ⟨hnext.1 ▸ hcache, ?_, ?_, ?_, ?_⟩
  · dsimp [deletionWork]
    dsimp [Sampler.Store.initial] at hr
    nlinarith [hr.2.2.2.2.1, hnext.2.1]
  · have hm := hr.2.1
    simpa [hm] using hnext.2.2.1
  · have hp := hr.2.2.2.1
    simpa [hnext.2.2.2.2.1] using hp
  · intro selected D h
    have hh := hnext.2.2.2.2.2 selected D h
    exact ⟨hh.1, hh.2.1, hh.2.2.1⟩

theorem deletion_covered (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ) (c : Cache Q) :
    ∀ o, Runs w bits (deletion p terminals root key a c) o →
      ∀ selected D, o.value.value = some (selected, D) →
        D = (LocalAccess.coveredResult w (5 * a / 8) selected.centers).value := by
  intro o ho selected D hv
  obtain ⟨sample, next, _, hn, rfl⟩ := Mean.runs_bind_inv w bits
    (Sampler.program (fun i => key (terminals.get i)) root p.poolRowCap p.poolSamples p.poolProposals c)
    _ _ ho
  exact ((deletionAfterPool_resources w bits p terminals a sample.value next hn).2.2.2.2.2
    selected D hv).2.2.2

end SteinerUpperBound.LargeCoverProgram
