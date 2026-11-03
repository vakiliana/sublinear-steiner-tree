module

public import SteinerUpperBound.LargeCoverProgram.Deletion
public import SteinerUpperBound.LargeCoverProgram.Small

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

variable {M Q U : Type*}

theorem scores_cache_only (m : M → ℝ) (bits : Q → Bool)
    (callback : Mean.Callback M Q U)
    (hcb : ∀ u c, Cache.Correct bits c → ∀ o, Runs m bits (callback u c) o →
      Cache.Correct bits o.value.2)
    (s : ℕ) (labels : Fin s → U) (c : Cache Q) (hc : Cache.Correct bits c) :
    ∀ o, Runs m bits (Mean.scores callback s labels c) o → Cache.Correct bits o.value.2 := by
  induction s generalizing c with
  | zero =>
      intro o ho
      cases ho with
      | tick ho => cases ho; exact hc
  | succ s ih =>
      intro o ho
      cases ho with
      | tick ho =>
          obtain ⟨head, tail, hh, ht, rfl⟩ := Mean.runs_bind_inv m bits (callback (labels 0) c) _ _ ho
          have hhc := hcb _ c hc head hh
          obtain ⟨rest, last, hr, hl, rfl⟩ := Mean.runs_bind_inv m bits
            (Mean.scores callback s (Fin.tail labels) head.value.2) _ _ ht
          cases hl with
          | tick hl =>
              cases hl
              exact ih (Fin.tail labels) _ hhc rest hr

theorem mean_cache_only {k : ℕ} (m : M → ℝ) (bits : Q → Bool)
    (callback : Mean.Callback M Q (Fin (k + 1)))
    (hcb : ∀ u c, Cache.Correct bits c → ∀ o, Runs m bits (callback u c) o →
      Cache.Correct bits o.value.2)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct bits c) (xi : ℝ) :
    ∀ o, Runs m bits (Mean.program query root C s B c xi callback) o →
      Cache.Correct bits o.value.cache := by
  intro o ho
  obtain ⟨sample, next, hs, hn, rfl⟩ := Mean.runs_bind_inv m bits
    (Sampler.program query root C s B c) _ _ ho
  have hsc := Mean.sampler_cache_correct m bits query root C s B c hc sample hs
  cases hn with
  | tick hn =>
      cases hl : sample.value.labels with
      | none =>
          simp only [Mean.afterSample, hl] at hn
          cases hn with
          | tick hn => cases hn; exact hsc
      | some labels =>
          simp only [Mean.afterSample, hl] at hn
          cases hsuccess : sample.value.successful
          · simp only [hsuccess, Bool.false_eq_true, ite_false] at hn
            cases hn with
            | tick hn => cases hn; exact hsc
          · simp only [hsuccess, ite_true] at hn
            obtain ⟨sum, last, hsum, hlast, rfl⟩ := Mean.runs_bind_inv m bits
              (Mean.scores callback s labels sample.value.store.cache) _ _ hn
            cases hlast with
            | tick hlast =>
                cases hlast
                exact scores_cache_only m bits callback hcb s labels _ hsc sum hsum

variable {n k : ℕ}

theorem reveal_deterministic (key : Fin n → Q) (l : List (Fin n)) (c : Cache Q) :
    Deterministic (LocalAccess.revealProgram (M := M) key l c) := by
  induction l generalizing c with
  | nil => trivial
  | cons x l ih =>
      apply deterministic_bind _ _ (resolve_deterministic _ _)
      intro reply
      exact deterministic_bind _ _ (ih _) (fun _ => trivial)

theorem small_deterministic (p : Parameters) (terminals : Vector (Fin n) (k + 1))
    (key : Fin n → Q) (a : ℝ) (gminus gplus : ℚ) (cache : Cache Q) :
    Deterministic (small p terminals key a gminus gplus cache) := by
  apply deterministic_bind _ _ (reveal_deterministic _ _ _)
  intro revealed
  apply deterministic_bind _ _ (length_deterministic _)
  intro size
  dsimp [Deterministic]
  split_ifs
  · exact deterministic_bind _ _
      (deterministic_of_metricOnly _ (SmallCoverProgram.program_metricOnly _ _)) (fun _ => trivial)
  · trivial

theorem small_cache (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1))
    (key : Fin n → Q) (a : ℝ) (gminus gplus : ℚ) (cache : Cache Q)
    (hc : Cache.Correct bits cache) :
    ∀ o, Runs w bits (small p terminals key a gminus gplus cache) o →
      Cache.Correct bits o.value.cache := by
  intro o ho
  have he := deterministic_run_eq w bits _ (small_deterministic _ _ _ _ _ _ _) _
    (small_evaluates w bits _ _ _ _ _ _ _) o ho
  subst o
  have hcache := (LocalAccess.reveal_correct bits key terminals.toList cache hc).2
  dsimp [smallResult]
  split_ifs <;> exact hcache

theorem afterCovered_cache (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ) (vo : VOBuilder Q n p.cutoff)
    (hvo : ∀ D d f c, Cache.Correct bits c → ∀ o, Runs w bits (vo D d f c) o →
      Cache.Correct bits o.value.2)
    (gminus gplus : ℚ) (selected : Selection (Fin n)) (c : Cache Q)
    (hc : Cache.Correct bits c) (D : Vector Bool n) :
    ∀ o, Runs w bits (afterCovered p terminals root key a vo gminus gplus selected c D) o →
      Cache.Correct bits o.value.cache := by
  intro o ho
  cases ho with
  | tick ho =>
      obtain ⟨mean, last, hm, hl, rfl⟩ := Mean.runs_bind_inv w bits _ _ _ ho
      have hmc := mean_cache_only w bits _ (fun u c hc o ho =>
        point_cache w bits key a _ _ D _ (hvo D _) _ c hc o ho)
        _ root p.meanRowCap p.meanSamples p.meanProposals c hc (p.xi : ℝ) mean hm
      cases hl with
      | tick hl => cases hl; exact hmc

theorem large_cache (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ) (vo : VOBuilder Q n p.cutoff)
    (hvo : ∀ D d f c, Cache.Correct bits c → ∀ o, Runs w bits (vo D d f c) o →
      Cache.Correct bits o.value.2)
    (gminus gplus : ℚ) (c : Cache Q) (hc : Cache.Correct bits c) :
    ∀ o, Runs w bits (large p terminals root key a vo gminus gplus c) o →
      Cache.Correct bits o.value.cache := by
  intro o ho
  obtain ⟨deleted, next, hd, hn, rfl⟩ := Mean.runs_bind_inv w bits
    (deletion p terminals root key a c) _ _ ho
  have hdc := (deletion_cache_resources w bits p terminals root key a c hc deleted hd).1
  cases hn with
  | tick hn =>
      cases hv : deleted.value.value with
      | none => simp only [hv] at hn; cases hn; exact hdc
      | some v =>
          simp only [hv] at hn
          have hfinal := afterCovered_cache w bits p terminals root key a vo hvo gminus gplus
            v.1 deleted.value.cache hdc v.2 _ hn
          simpa only [Outcome.combine, Outcome.add] using hfinal

theorem program_cache (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ) (vo : VOBuilder Q n p.cutoff)
    (hvo : ∀ D d f c, Cache.Correct bits c → ∀ o, Runs w bits (vo D d f c) o →
      Cache.Correct bits o.value.2)
    (c : Cache Q) (hc : Cache.Correct bits c) :
    ∀ o, Runs w bits (program p terminals root key a vo c) o →
      Cache.Correct bits o.value.cache := by
  intro o ho
  obtain ⟨sample, next, hs, hn, rfl⟩ := Mean.runs_bind_inv w bits
    (Sampler.program (fun i => key (terminals.get i)) root p.calibrationRowCap
      p.calibrationSamples p.calibrationProposals c) _ _ ho
  have hsc := Mean.sampler_cache_correct w bits _ root _ _ _ c hc sample hs
  cases hn with
  | tick hn =>
      dsimp only [afterCalibration] at hn
      cases hl : sample.value.labels with
      | none => simp only [hl] at hn; cases hn; exact hsc
      | some labels =>
          simp only [hl] at hn
          cases ht : sample.value.successful
          · simp only [ht, Bool.false_eq_true, ite_false] at hn; cases hn; exact hsc
          · simp only [ht, ite_true] at hn
            split_ifs at hn
            · have hfinal := small_cache w bits p terminals key a _ _ _ hsc _ hn
              simpa only [Outcome.combine, Outcome.add] using hfinal
            · have hfinal := large_cache w bits p terminals root key a vo hvo _ _ _ hsc _ hn
              simpa only [Outcome.combine, Outcome.add] using hfinal

end SteinerUpperBound.LargeCoverProgram
