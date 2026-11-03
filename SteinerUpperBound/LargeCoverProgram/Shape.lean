module

public import SteinerUpperBound.LargeCoverProgram.Contract
public import SteinerUpperBound.LargeCoverProgram.Cache

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical

variable {Q : Type*} {n k : ℕ}

def AnswerShape (w : Sym2 (Fin n) → ℝ) (p : Parameters) (a : ℝ) (r : Answer Q n) : Prop :=
  r.selected.count ≤ p.t ∧ r.selected.centers.length = r.selected.count ∧
    r.selected.centers.Nodup ∧ ∀ D, r.covered = some D →
      D = (LocalAccess.coveredResult w (5 * a / 8) r.selected.centers).value

theorem abort_shape (w : Sym2 (Fin n) → ℝ) (p : Parameters) (a : ℝ)
    (c : Cache Q) (gm gp : ℚ) (small : Bool) :
    AnswerShape w p a (abort c gm gp small : Answer Q n) := by
  simp [AnswerShape, abort]

theorem small_shape (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ)
    (gm gp : ℚ) (c : Cache Q) :
    ∀ o, Runs w bits (small p terminals key a gm gp c) o → AnswerShape w p a o.value := by
  intro o ho
  have he := deterministic_run_eq w bits _ (small_deterministic p terminals key a gm gp c)
    _ (small_evaluates w bits p terminals key a gm gp c) o ho
  subst o
  dsimp [smallResult]
  split_ifs
  · simp [AnswerShape, Outcome.combine, Outcome.add, Outcome.pure]
  · exact abort_shape w p a _ _ _ _

theorem large_shape (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ) (vo : VOBuilder Q n p.cutoff)
    (gm gp : ℚ) (c : Cache Q) (hc : Cache.Correct bits c) :
    ∀ o, Runs w bits (large p terminals root key a vo gm gp c) o → AnswerShape w p a o.value := by
  intro o ho
  obtain ⟨deleted, next, hd, hn, rfl⟩ := Mean.runs_bind_inv w bits (deletion p terminals root key a c) _ _ ho
  cases hn with
  | tick hn =>
    cases hv : deleted.value.value with
    | none =>
      simp only [hv] at hn
      cases hn
      exact abort_shape w p a _ _ _ _
    | some val =>
      obtain ⟨selected, D⟩ := val
      simp only [hv] at hn
      have hshape := (deletion_cache_resources w bits p terminals root key a c hc deleted hd).2.2.2.2 selected D hv
      have hD := deletion_covered w bits p terminals root key a c deleted hd selected D hv
      have hf := afterCovered_fields w bits p terminals root key a vo gm gp selected deleted.value.cache D _ hn
      dsimp only [AnswerShape, Outcome.combine, Outcome.add]
      rw [hf.2.1, hf.2.2]
      exact ⟨hshape.1, hshape.2.1, hshape.2.2, fun _ h => Option.some.inj h ▸ hD⟩

/-- Pathwise selected-count, stored-list, uniqueness, and actual D-bitmap
fidelity for the full program; NO VO value or cache assumption is needed. -/
theorem program_shape (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ) (vo : VOBuilder Q n p.cutoff) (c : Cache Q)
    (hc : Cache.Correct bits c) :
    ∀ o, Runs w bits (program p terminals root key a vo c) o → AnswerShape w p a o.value := by
  intro o ho
  obtain ⟨sample, next, hs, hn, rfl⟩ := Mean.runs_bind_inv w bits
    (Sampler.program (fun i => key (terminals.get i)) root p.calibrationRowCap
      p.calibrationSamples p.calibrationProposals c) _ _ ho
  have hsc := Mean.sampler_cache_correct w bits _ root _ _ _ c hc sample hs
  cases hn with
  | tick hn =>
    dsimp only [afterCalibration] at hn
    cases hl : sample.value.labels with
    | none => simp only [hl] at hn; cases hn; exact abort_shape w p a _ _ _ _
    | some labels =>
      simp only [hl] at hn
      cases ht : sample.value.successful
      · simp only [ht, Bool.false_eq_true, ite_false] at hn
        cases hn
        exact abort_shape w p a _ _ _ _
      · simp only [ht, ite_true] at hn
        split_ifs at hn
        · have hfinal := small_shape w bits p terminals key a _ _ _ _ hn
          simpa only [Outcome.combine, Outcome.add] using hfinal
        · have hfinal := large_shape w bits p terminals root key a vo _ _ _ hsc _ hn
          simpa only [Outcome.combine, Outcome.add] using hfinal

end SteinerUpperBound.LargeCoverProgram
