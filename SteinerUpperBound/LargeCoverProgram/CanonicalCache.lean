module

public import SteinerUpperBound.LargeCoverProgram.Cache
public import SteinerUpperBound.LargeCoverProgram.PointKernel

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical

variable {Q : Type} {n k : ℕ}

def CanonicalVOBuilderCache (I : Instance (Fin n)) (bits : Q → Bool) (p : Parameters)
    (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ)
    (vo : VOBuilder Q n p.cutoff) : Prop :=
  ∀ D d, CanonicalVOCache I bits ⟨key, a, terminals, D⟩ d p.cutoff (vo D d)

theorem afterCovered_cache_canonical (I : Instance (Fin n)) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (vo : VOBuilder Q n p.cutoff) (hvo : CanonicalVOBuilderCache I bits p terminals key a vo)
    (gm gp : ℚ) (selected : Selection (Fin n)) (c : Cache Q)
    (hc : Cache.Correct bits c) (D : Vector Bool n) :
    ∀ o, Runs I.weight bits (afterCovered p terminals root key a vo gm gp selected c D) o →
      Cache.Correct bits o.value.cache := by
  intro o ho
  cases ho with
  | tick ho =>
    obtain ⟨mean, last, hm, hl, rfl⟩ := Mean.runs_bind_inv I.weight bits _ _ _ ho
    have hmc := mean_cache_only I.weight bits _
      (fun u c hc o ho => point_cache_canonical I bits ⟨key, a, terminals, D⟩ hT hnd _
        (hvo D _) u c hc o ho)
      _ root p.meanRowCap p.meanSamples p.meanProposals c hc (p.xi : ℝ) mean hm
    cases hl with
    | tick hl => cases hl; exact hmc

theorem large_cache_canonical (I : Instance (Fin n)) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (vo : VOBuilder Q n p.cutoff) (hvo : CanonicalVOBuilderCache I bits p terminals key a vo)
    (gm gp : ℚ) (c : Cache Q) (hc : Cache.Correct bits c) :
    ∀ o, Runs I.weight bits (large p terminals root key a vo gm gp c) o →
      Cache.Correct bits o.value.cache := by
  intro o ho
  obtain ⟨deleted, next, hd, hn, rfl⟩ := Mean.runs_bind_inv I.weight bits
    (deletion p terminals root key a c) _ _ ho
  have hdc := (deletion_cache_resources I.weight bits p terminals root key a c hc deleted hd).1
  cases hn with
  | tick hn =>
    cases hv : deleted.value.value with
    | none => simp only [hv] at hn; cases hn; exact hdc
    | some val =>
      simp only [hv] at hn
      have hfinal := afterCovered_cache_canonical I bits p terminals root key a hT hnd vo hvo gm gp
        val.1 deleted.value.cache hdc val.2 _ hn
      simpa only [Outcome.combine, Outcome.add] using hfinal

/-- Pathwise cache correctness for the entire actual frontend, requiring a
callback invariant ONLY on its reachable canonical small/uncovered frames. -/
theorem program_cache_canonical (I : Instance (Fin n)) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (vo : VOBuilder Q n p.cutoff) (hvo : CanonicalVOBuilderCache I bits p terminals key a vo)
    (c : Cache Q) (hc : Cache.Correct bits c) :
    ∀ o, Runs I.weight bits (program p terminals root key a vo c) o →
      Cache.Correct bits o.value.cache := by
  intro o ho
  obtain ⟨sample, next, hs, hn, rfl⟩ := Mean.runs_bind_inv I.weight bits
    (Sampler.program (fun i => key (terminals.get i)) root p.calibrationRowCap
      p.calibrationSamples p.calibrationProposals c) _ _ ho
  have hsc := Mean.sampler_cache_correct I.weight bits _ root _ _ _ c hc sample hs
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
        · have hfinal := small_cache I.weight bits p terminals key a _ _ _ hsc _ hn
          simpa only [Outcome.combine, Outcome.add] using hfinal
        · have hfinal := large_cache_canonical I bits p terminals root key a hT hnd vo hvo _ _ _ hsc _ hn
          simpa only [Outcome.combine, Outcome.add] using hfinal

end SteinerUpperBound.LargeCoverProgram
