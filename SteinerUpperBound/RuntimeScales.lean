module

public import SteinerUpperBound.LabelledMetricWorld

@[expose] public section

noncomputable section

namespace SteinerUpperBound.RuntimeScales

open QueryProgram
open scoped Classical

variable {M Q : Type*}

def power (x : ℝ) : ℕ → Code M Q ℝ
  | 0 => .tick 0 (.pure 1)
  | i + 1 => (power x i).bind (fun a => .tick 1 (.pure (a * x)))

def powered (x : ℝ) (i : ℕ) : Outcome ℝ :=
  ⟨x ^ i, 2 * i + 1, 0, 0, 0⟩

theorem power_evaluates (m : M → ℝ) (bits : Q → Bool) (x : ℝ) (i : ℕ) :
    Code.Evaluates m bits (power x i) (powered x i) := by
  induction i with
  | zero => intro F; rfl
  | succ i ih =>
      intro F
      simp only [power, Code.evaluate_bind, Code.evaluate]
      rw [ih]
      simp only [powered, Outcome.combine, Outcome.add, Outcome.pure, pow_succ]
      congr 2

structure Config where
  offset : ℕ
  coarseFirst : ℝ
  coarseRatio : ℝ
  fineFirst : ℝ
  fineRatio : ℝ
  coarseDelta : ℝ
  fineDelta : ℝ
  hop : ℕ

def radius (cfg : Config) (i : ℕ) : ℝ :=
  if i < cfg.offset then cfg.coarseDelta * cfg.coarseFirst * cfg.coarseRatio ^ i / cfg.hop
  else cfg.fineDelta * cfg.fineFirst * cfg.fineRatio ^ (i - cfg.offset) / cfg.hop

def cellProgram (cfg : Config) (i : ℕ) : Code M Q ℝ :=
  .tick 2 (if i < cfg.offset then
    (power cfg.coarseRatio i).bind (fun p =>
      .tick 3 (.pure (cfg.coarseDelta * cfg.coarseFirst * p / cfg.hop)))
  else
    (power cfg.fineRatio (i - cfg.offset)).bind (fun p =>
      .tick 3 (.pure (cfg.fineDelta * cfg.fineFirst * p / cfg.hop))))

def cellResult (cfg : Config) (i : ℕ) : Outcome ℝ :=
  ⟨radius cfg i, (if i < cfg.offset then 2 * i else 2 * (i - cfg.offset)) + 8, 0, 0, 0⟩

theorem cell_evaluates (m : M → ℝ) (bits : Q → Bool) (cfg : Config) (i : ℕ) :
    Code.Evaluates m bits (cellProgram cfg i) (cellResult cfg i) := by
  intro F
  by_cases h : i < cfg.offset <;>
    simp only [cellProgram, h, ite_true, ite_false, Code.evaluate, Code.evaluate_bind] <;>
    rw [power_evaluates] <;>
    simp only [powered, cellResult, radius, h, ite_true, ite_false,
      Outcome.add, Outcome.combine, Outcome.pure] <;>
    congr 2 <;> omega

def program (cfg : Config) (length : ℕ) : Code M Q (Vector ℝ length) :=
  (SmallCoverProgram.allocate length 0).bind (fun init =>
    SmallCoverProgram.tabulate (fun i => cellProgram cfg i.val) init)

def result (cfg : Config) (length : ℕ) : Outcome (Vector ℝ length) :=
  (SmallCoverProgram.allocated length (0 : ℝ)).combine
    (SmallCoverProgram.tabulated (fun i => cellResult cfg i.val) (Vector.replicate length 0))

theorem program_evaluates (m : M → ℝ) (bits : Q → Bool) (cfg : Config) (length : ℕ) :
    Code.Evaluates m bits (program cfg length) (result cfg length) :=
  Code.Evaluates.bind m bits _ _ _ _ (SmallCoverProgram.allocate_evaluates m bits _ _)
    (SmallCoverProgram.tabulate_evaluates m bits _ _ (fun i => cell_evaluates m bits cfg i.val) _)

theorem get_result (cfg : Config) (length : ℕ) (i : Fin length) :
    (result cfg length).value.get i = radius cfg i.val := by
  change (SmallCoverProgram.tabulated _ _).value.get i = _
  rw [SmallCoverProgram.tabulated_get]
  rfl

theorem work (cfg : Config) (length : ℕ) :
    (result cfg length).work ≤ (2 * length + 11) * length + 1 := by
  have hc (i : Fin length) : (cellResult cfg i.val).work ≤ 2 * length + 8 := by
    simp only [cellResult]
    split_ifs <;> omega
  have ht := SmallCoverProgram.tabulated_work (fun i : Fin length => cellResult cfg i.val)
    (Vector.replicate length 0) (2 * length + 8) hc
  dsimp only [result, SmallCoverProgram.allocated, Outcome.combine]
  nlinarith

theorem counters (cfg : Config) (length : ℕ) :
    (result cfg length).metricQueries = 0 ∧ (result cfg length).retentionQueries = 0 ∧
      (result cfg length).positiveReplies = 0 := by
  have hm := SmallCoverProgram.tabulated_metricQueries (fun i : Fin length => cellResult cfg i.val)
    (Vector.replicate length 0) 0 (fun _ => le_rfl)
  have hr := SmallCoverProgram.tabulated_retention_zero (fun i : Fin length => cellResult cfg i.val)
    (Vector.replicate length 0) (fun _ => rfl)
  have hp := SmallCoverProgram.tabulated_positive_zero (fun i : Fin length => cellResult cfg i.val)
    (Vector.replicate length 0) (fun _ => rfl)
  simp only [Nat.zero_mul] at hm
  dsimp only [result, SmallCoverProgram.allocated, Outcome.combine]
  exact ⟨by omega, by simpa using hr, by simpa using hp⟩

theorem radius_pos (cfg : Config) (i : ℕ) (hc : 0 < cfg.coarseFirst) (hf : 0 < cfg.fineFirst)
    (hqc : 0 < cfg.coarseRatio) (hqf : 0 < cfg.fineRatio)
    (hdc : 0 < cfg.coarseDelta) (hdf : 0 < cfg.fineDelta) (hh : 0 < cfg.hop) :
    0 < radius cfg i := by
  unfold radius
  split_ifs <;> positivity

end SteinerUpperBound.RuntimeScales
