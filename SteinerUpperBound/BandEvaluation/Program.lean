module

public import SteinerUpperBound.BandEvaluation.Score
public import SteinerUpperBound.BandEvaluation.Bounds

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

open QueryProgram SmallCoverProgram
open scoped Classical

variable {Q : Type*} {n : ℕ}

/-- Only the public component IDs, scale, and band parameters are supplied. -/
noncomputable def program (C : List (Fin n)) (a rho tau : ℝ) : Code (Sym2 (Fin n)) Q ℝ :=
  let points := asVector C
  .tick (4 * C.length + 3) ((metricTable points).bind (fun d => score points d a rho tau))

noncomputable def run (oracle : Sym2 (Fin n) → ℝ) (C : List (Fin n)) (a rho tau : ℝ) : Outcome ℝ :=
  let points := asVector C
  let d := metricTableRun oracle points
  (d.combine (scoreRun points d.value a rho tau)).add (4 * C.length + 4) 0 0 0

theorem program_evaluates (oracle : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (C : List (Fin n)) (a rho tau : ℝ) :
    Code.Evaluates oracle bits (program C a rho tau) (run oracle C a rho tau) :=
  Code.Evaluates.tick _ _ _ _
    (Code.Evaluates.bind _ _ _ _ _ _ (metricTable_evaluates _ _ _)
      (score_evaluates _ _ _ _ _ _ _)) _

theorem program_correct (I : Instance (Fin n)) (C : List (Fin n)) (hC : C.Nodup)
    (a rho tau : ℝ) (hband : tau * a ≤ a - 2 * rho) :
    (run I.weight C a rho tau).value = Band.score I C.toFinset a rho tau := by
  have hd (i v) : distanceAt (metricTableRun I.weight (asVector C)).value i v =
      I.distance ((asVector C).get i) v := by
    simpa only [Instance.weight_mk] using metricTable_get I.weight (asVector C) i v
  simpa only [run, Outcome.add, Outcome.combine, retained_asVector] using
    scoreRun_correct I (asVector C) (asVector_injective C hC) _ hd a rho tau hband

theorem program_bounds (I : Instance (Fin n)) (C : List (Fin n)) (hC : C.Nodup)
    (a rho tau : ℝ) (ha : 0 ≤ a) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (hband : tau * a ≤ a - 2 * rho) :
    0 ≤ (run I.weight C a rho tau).value ∧ (run I.weight C a rho tau).value ≤ 3 * a := by
  rw [program_correct I C hC a rho tau hband]
  exact score_bounds I C.toFinset a rho tau ha hrho htau hband

theorem run_queries (oracle : Sym2 (Fin n) → ℝ) (C : List (Fin n)) (a rho tau : ℝ) :
    (run oracle C a rho tau).metricQueries ≤ n * C.length := by
  have hm := metricTable_queries oracle (asVector C)
  have hs := scoreRun_resources (asVector C) (metricTableRun oracle (asVector C)).value a rho tau
  simpa only [run, Outcome.add, Outcome.combine, hs.1, Nat.zero_add, Nat.add_zero, Nat.mul_comm] using hm

theorem run_resources (oracle : Sym2 (Fin n) → ℝ) (C : List (Fin n)) (a rho tau : ℝ) :
    (run oracle C a rho tau).retentionQueries = 0 ∧ (run oracle C a rho tau).positiveReplies = 0 := by
  have hm := metricTable_resources oracle (asVector C)
  have hs := scoreRun_resources (asVector C) (metricTableRun oracle (asVector C)).value a rho tau
  simp only [run, Outcome.add, Outcome.combine, hm, hs, Nat.zero_add, and_self]

theorem run_work (oracle : Sym2 (Fin n) → ℝ) (C : List (Fin n)) (a rho tau : ℝ) :
    (run oracle C a rho tau).work ≤ 10000000000 * (n + 1) * (C.length + 1) ^ 12 := by
  have hm := metricTable_work oracle (asVector C)
  have hs := scoreRun_work (asVector C) (metricTableRun oracle (asVector C)).value a rho tau
  have hp : (C.length + 1) ^ 11 ≤ (C.length + 1) ^ 12 :=
    pow_le_pow_right₀ (by omega) (by omega)
  have hsp := Nat.mul_le_mul_left (6000000000 * (n + 1)) hp
  have hCp : C.length ≤ (C.length + 1) ^ 12 := by
    have hh : C.length + 1 ≤ (C.length + 1) ^ 12 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1 ≤ C.length + 1) (by omega : 1 ≤ 12)
    omega
  have hnC := Nat.mul_le_mul (Nat.le_succ n) hCp
  have hbase : (C.length + 1) ^ 12 ≤ (n + 1) * (C.length + 1) ^ 12 := by nlinarith
  have hC := hCp.trans hbase
  have h1 : 1 ≤ (n + 1) * (C.length + 1) ^ 12 := by
    have hp : 0 < (n + 1) * (C.length + 1) ^ 12 := by positivity
    omega
  dsimp only [run, Outcome.add, Outcome.combine]
  nlinarith

end SteinerUpperBound.BandEvaluation
