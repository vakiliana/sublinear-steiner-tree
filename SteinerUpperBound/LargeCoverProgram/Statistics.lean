module

public import SteinerUpperBound.LargeCoverProgram.Basic
public import SteinerUpperBound.LargeCoverProgram.ApproxPoint

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

variable {Q A : Type} [Fintype A] {n k : ℕ}

noncomputable def expectedPoint (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (B : ℕ)
    (mu : Law A) (matched : Finset (Fin n) → A → Bool)
    (hb : (Covers.Rejection.retained (bits ∘ cfg.key ∘ cfg.terminals.get)).Nonempty) : ℝ :=
  (Mean.pointKernel (Covers.Rejection.uniformRetained
      (fun u => bits (cfg.key (cfg.terminals.get u))) hb)
    (pointKernel I bits cfg mu)).expect (fun z => pointScore I bits cfg B matched z.1 z.2)

theorem afterCovered_empirical_value (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (cfg : LocalAccess.SlotConfig Q n (k + 1)) (root : Fin (k + 1))
    (vo : VOBuilder Q n p.cutoff) (gminus gplus : ℚ)
    (selected : Selection (Fin n)) (c : Cache Q) (F : Option ℝ → ℝ) :
    (afterCovered p cfg.terminals root cfg.key cfg.scale vo gminus gplus selected c cfg.covered).evaluate
      w bits (fun o => F o.value.empirical) =
    (Mean.program (fun u => cfg.key (cfg.terminals.get u)) root
      p.meanRowCap p.meanSamples p.meanProposals c (p.xi : ℝ)
      (fun u cache => point cfg.key cfg.scale (List.finRange n) cfg.terminals.toList
        cfg.covered (vo cfg.covered (rowCapacity n p gminus)) (cfg.terminals.get u) cache)).evaluate
        w bits (fun o => F o.value.value) := by
  simp only [afterCovered, Code.evaluate, Code.evaluate_bind, afterMean,
    Outcome.add, Outcome.combine, Outcome.pure]

theorem afterCovered_value (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (cfg : LocalAccess.SlotConfig Q n (k + 1)) (root : Fin (k + 1))
    (vo : VOBuilder Q n p.cutoff) (gminus gplus : ℚ)
    (selected : Selection (Fin n)) (c : Cache Q) (F : Option ℝ → ℝ) :
    (afterCovered p cfg.terminals root cfg.key cfg.scale vo gminus gplus selected c cfg.covered).evaluate
      w bits (fun o => F o.value.value) =
    (Mean.program (fun u => cfg.key (cfg.terminals.get u)) root
      p.meanRowCap p.meanSamples p.meanProposals c (p.xi : ℝ)
      (fun u cache => point cfg.key cfg.scale (List.finRange n) cfg.terminals.toList
        cfg.covered (vo cfg.covered (rowCapacity n p gminus)) (cfg.terminals.get u) cache)).evaluate
        w bits (fun o => F (o.value.value.map
          (fun empirical => SavingScores.Z gminus empirical (p.xi : ℝ) selected.count))) := by
  simp only [afterCovered, Code.evaluate, Code.evaluate_bind, afterMean,
    Outcome.add, Outcome.combine, Outcome.pure]

/-- Actual mean confidence, with an explicit `s*delta` correction for bad
matching calls. Neither calibration-conditioned uniformity nor a score-mean
certificate is used. -/
theorem afterCovered_confidence (I : Instance (Fin n)) (bits : Q → Bool)
    (p : Parameters) (cfg : LocalAccess.SlotConfig Q n (k + 1)) (root : Fin (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (vo : VOBuilder Q n p.cutoff) (gminus gplus : ℚ)
    (selected : Selection (Fin n)) (c : Cache Q) (hc : Cache.Correct bits c)
    (hb : (Covers.Rejection.retained (bits ∘ cfg.key ∘ cfg.terminals.get)).Nonempty)
    (mu : Law A) (matched : Finset (Fin n) → A → Bool) (delta beta : ℝ) (hd : 0 ≤ delta)
    (hvo : VOApproxRefinement I bits cfg (rowCapacity n p gminus) p.cutoff
      (vo cfg.covered (rowCapacity n p gminus)) mu matched delta)
    (hs : 0 < p.meanSamples) (hxi : 0 < (p.xi : ℝ))
    (hbudget : 1 ≤ beta * ((p.meanSamples : ℝ) * (p.xi : ℝ) ^ 2)) :
    (afterCovered p cfg.terminals root cfg.key cfg.scale vo gminus gplus selected c cfg.covered).probability
      I.weight bits {o | Mean.BadMean (expectedPoint I bits cfg p.cutoff mu matched hb)
        (p.xi : ℝ) o.value.empirical} ≤
      Mean.capError (bits ∘ cfg.key ∘ cfg.terminals.get)
        p.meanRowCap p.meanSamples p.meanProposals + p.meanSamples * delta + beta := by
  have hkernel := point_approxKernelSpec I bits cfg hT hnd
    (vo cfg.covered (rowCapacity n p gminus)) mu matched delta hd hvo
  have hm := mean_confidence hkernel hd (fun u => cfg.key (cfg.terminals.get u)) root
    p.meanRowCap p.meanSamples p.meanProposals c hc hb (p.xi : ℝ) (p.xi : ℝ) beta
    (fun u seed => (pointScore_bounds I bits cfg matched u seed).1)
    (fun u seed => (pointScore_bounds I bits cfg matched u seed).2) hs hxi hbudget
  unfold Code.probability
  simp only [Set.mem_ofPred_eq]
  rw [afterCovered_empirical_value I.weight bits p cfg root vo gminus gplus selected c
    (fun value => if Mean.BadMean (expectedPoint I bits cfg p.cutoff mu matched hb)
      (p.xi : ℝ) value then 1 else 0)]
  exact hm

end SteinerUpperBound.LargeCoverProgram
