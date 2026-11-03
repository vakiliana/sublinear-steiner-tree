module

public import SteinerUpperBound.LargeCoverProgram.Point

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

structure Parameters where
  t : ℕ
  Lbar : ℕ
  Mbar : ℕ
  cutoff : ℕ
  eps : ℚ
  xi : ℚ
  calibrationSamples : ℕ
  calibrationRowCap : ℕ
  calibrationProposals : ℕ
  poolRowCap : ℕ
  poolProposals : ℕ
  meanSamples : ℕ
  meanRowCap : ℕ
  meanProposals : ℕ

def Parameters.poolSamples (p : Parameters) : ℕ :=
  ReusableSample.integerSamples p.t p.Lbar p.Mbar

def lowerObserved (k s proposals : ℕ) (xi : ℚ) : ℚ :=
  (1 - xi / 2) * k * s / proposals

def upperObserved (k s proposals : ℕ) (xi : ℚ) : ℚ :=
  (1 + xi / 2) * k * s / proposals

def smallLimit (p : Parameters) : ℕ := ⌈100 * (p.t : ℚ) / p.eps⌉₊

/-- A public clamp prevents an erroneous size calibration from causing an
unbounded allocation. On the calibrated large branch it is inactive. -/
def rowCapacity (n : ℕ) (p : Parameters) (gminus : ℚ) : ℕ :=
  min (4 * n / max 1 p.t + 2) (max 1 ⌈100 * (n : ℚ) / (p.eps * gminus)⌉₊)

structure Answer (Q : Type*) (n : ℕ) where
  value : Option ℝ
  cache : Cache Q
  small : Bool
  lower : ℚ
  upper : ℚ
  selected : Selection (Fin n)
  covered : Option (Vector Bool n)
  empirical : Option ℝ

structure Deletion (Q : Type*) (n : ℕ) where
  value : Option (Selection (Fin n) × Vector Bool n)
  cache : Cache Q

variable {Q : Type*} {n k : ℕ}

abbrev VOBuilder (Q : Type*) (n B : ℕ) :=
  (D : Vector Bool n) → (d : ℕ) → VO Q n d B

def abort (cache : Cache Q) (gminus gplus : ℚ) (small : Bool) : Answer Q n :=
  ⟨none, cache, small, gminus, gplus, ⟨[], 0⟩, none, none⟩

noncomputable def afterMean (p : Parameters) (gminus gplus : ℚ)
    (selected : Selection (Fin n)) (D : Vector Bool n)
    (r : Mean.Result Q k p.meanSamples) : Code (Sym2 (Fin n)) Q (Answer Q n) :=
  .tick 15 (.pure ⟨r.value.map (fun empirical =>
    SavingScores.Z (gminus : ℝ) empirical (p.xi : ℝ) selected.count),
      r.cache, false, gminus, gplus, selected, some D, r.value⟩)

noncomputable def afterCovered (p : Parameters) (terminals : Vector (Fin n) (k + 1))
    (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (vo : VOBuilder Q n p.cutoff)
    (gminus gplus : ℚ) (selected : Selection (Fin n)) (cache : Cache Q)
    (D : Vector Bool n) : Code (Sym2 (Fin n)) Q (Answer Q n) :=
  .tick 15
    (let d := rowCapacity n p gminus
     Mean.program (fun i => key (terminals.get i)) root
       p.meanRowCap p.meanSamples p.meanProposals cache (p.xi : ℝ)
       (fun u c => point key a (List.finRange n) terminals.toList D (vo D d) (terminals.get u) c)
       |>.bind (afterMean p gminus gplus selected D))

noncomputable def deletionAfterPool (p : Parameters) (terminals : Vector (Fin n) (k + 1))
    (a : ℝ)
    (records : Sampler.Records Q k p.poolSamples) :
    Code (Sym2 (Fin n)) Q (Deletion Q n) :=
  .tick 3 (match records.labels with
    | none => .pure ⟨none, records.store.cache⟩
    | some labels =>
      if records.successful then
        (ReusableSample.OracleProgram.program (fun v : Fin n => v)
          (fun i => terminals.get (labels i)) (5 * a / 8) p.t p.Lbar).bind (fun bits =>
          (selectionProgram (fun v : Fin n => v) bits).bind (fun selected =>
            (LocalAccess.coveredProgram (5 * a / 8) selected.centers).bind
              (fun D => .tick 3 (.pure ⟨some (selected, D), records.store.cache⟩))))
      else .pure ⟨none, records.store.cache⟩)

noncomputable def deletion (p : Parameters) (terminals : Vector (Fin n) (k + 1))
    (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ) (cache : Cache Q) :
    Code (Sym2 (Fin n)) Q (Deletion Q n) :=
  (Sampler.program (fun i => key (terminals.get i)) root p.poolRowCap p.poolSamples
    p.poolProposals cache).bind (deletionAfterPool p terminals a)

noncomputable def large (p : Parameters) (terminals : Vector (Fin n) (k + 1))
    (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (vo : VOBuilder Q n p.cutoff) (gminus gplus : ℚ) (cache : Cache Q) :
    Code (Sym2 (Fin n)) Q (Answer Q n) :=
  (deletion p terminals root key a cache).bind (fun deleted =>
    .tick 3 (match deleted.value with
      | none => .pure (abort deleted.cache gminus gplus false)
      | some (selected, D) =>
        afterCovered p terminals root key a vo gminus gplus selected deleted.cache D))

noncomputable def small (p : Parameters) (terminals : Vector (Fin n) (k + 1))
    (key : Fin n → Q) (a : ℝ) (gminus gplus : ℚ) (cache : Cache Q) :
    Code (Sym2 (Fin n)) Q (Answer Q n) :=
  (LocalAccess.revealProgram key terminals.toList cache).bind (fun revealed =>
    (lengthProgram revealed.points).bind (fun size =>
      .tick 3 (if size ≤ smallLimit p then
        (SmallCoverProgram.program revealed.points a).bind (fun Z =>
          .tick 7 (.pure ⟨some Z, revealed.cache, true, gminus, gplus,
            ⟨[], 0⟩, none, none⟩))
      else .pure (abort revealed.cache gminus gplus true))))

noncomputable def afterCalibration (p : Parameters) (terminals : Vector (Fin n) (k + 1))
    (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (vo : VOBuilder Q n p.cutoff) (records : Sampler.Records Q k p.calibrationSamples) :
    Code (Sym2 (Fin n)) Q (Answer Q n) :=
  .tick 31
    (let gminus := lowerObserved (k + 1) p.calibrationSamples records.store.proposals p.xi
     let gplus := upperObserved (k + 1) p.calibrationSamples records.store.proposals p.xi
     match records.labels with
     | none => .pure (abort records.store.cache gminus gplus false)
     | some _ =>
       if records.successful then
         if gplus ≤ 100 * (p.t : ℚ) / p.eps then
           small p terminals key a gminus gplus records.store.cache
         else large p terminals root key a vo gminus gplus records.store.cache
       else .pure (abort records.store.cache gminus gplus false))

/-- The complete per-scale frontend. The only higher-order runtime argument is
the actual causal matching-VO code. No metric, retained set, partition, or
saving statistic is available to this program. -/
noncomputable def program (p : Parameters) (terminals : Vector (Fin n) (k + 1))
    (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (vo : VOBuilder Q n p.cutoff) (cache : Cache Q) :
    Code (Sym2 (Fin n)) Q (Answer Q n) :=
  (Sampler.program (fun i => key (terminals.get i)) root p.calibrationRowCap
    p.calibrationSamples p.calibrationProposals cache).bind
      (afterCalibration p terminals root key a vo)

end SteinerUpperBound.LargeCoverProgram
