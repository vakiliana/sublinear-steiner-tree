module

public import SteinerUpperBound.BandEvaluation.Program

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

open QueryProgram SmallCoverProgram
open scoped Classical

variable {M Q : Type*} {n m : ℕ}

private theorem member_only (x : Fin n) (l : List (Fin n)) :
    MetricOnly (member (M := M) (Q := Q) x l) := by
  induction l with
  | nil => trivial
  | cons y l ih =>
      unfold member
      split_ifs
      · trivial
      · exact ih

private theorem unique_only (l acc : List (Fin n)) :
    MetricOnly (unique (M := M) (Q := Q) l acc) := by
  induction l generalizing acc with
  | nil => trivial
  | cons x l ih => exact metricOnly_bind _ _ (member_only x acc) (fun _ => ih _)

private theorem augment_only (L : List (Fin n)) (v : Fin n) :
    MetricOnly (augment (M := M) (Q := Q) L v) :=
  metricOnly_bind _ _ (member_only v L) (fun _ => trivial)

private theorem lookup_only (C : Vector (Fin n) m) (d : MetricTable n m) (x y : Fin n) (l) :
    MetricOnly (lookup (M := M) (Q := Q) C d x y l) := by
  induction l with
  | nil => trivial
  | cons i l ih =>
      unfold lookup
      split_ifs
      · trivial
      · trivial
      · exact ih

private theorem rawMatrix_only (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    MetricOnly (rawMatrix (M := M) (Q := Q) C d L) := by
  apply metricOnly_bind _ _ (by trivial)
  intro init
  apply metricOnly_tabulate
  intro p
  exact lookup_only C d _ _ _

private theorem rawMST_only (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    MetricOnly (rawMST (M := M) (Q := Q) C d L) :=
  metricOnly_bind _ _ (rawMatrix_only C d L) FiniteMST.program_metricOnly

private theorem localCost_only (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    MetricOnly (localCost (M := M) (Q := Q) C d L) := by
  apply metricOnly_bind _ _ (rawMST_only C d L)
  intro base
  apply metricOnly_foldList
  intro best v
  exact metricOnly_bind _ _ (augment_only L v) (fun aug =>
    metricOnly_bind _ _ (rawMST_only C d aug) (fun _ => trivial))

private theorem clippedMST_only (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) :
    MetricOnly (clippedMST (M := M) (Q := Q) C d lo hi Y) := by
  apply metricOnly_bind
  · apply metricOnly_bind _ _ (by trivial)
    intro init
    apply metricOnly_tabulate
    intro _
    trivial
  · exact FiniteMST.program_metricOnly

private theorem benefit_only (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) :
    MetricOnly (finiteBenefit (M := M) (Q := Q) C d lo hi Y) :=
  metricOnly_bind _ _ (clippedMST_only C d lo hi []) (fun _ =>
    metricOnly_bind _ _ (clippedMST_only C d lo hi Y) (fun _ => trivial))

private theorem candidate_only (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau : ℝ) (t) :
    MetricOnly (candidate (M := M) (Q := Q) C d a rho tau t) := by
  apply metricOnly_bind _ _ (unique_only _ [])
  intro Y
  split_ifs
  · exact metricOnly_bind _ _ (benefit_only C d _ _ Y) (fun _ =>
      metricOnly_bind _ _ (localCost_only C d Y) (fun _ => trivial))
  · trivial

private theorem score_only (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau : ℝ) :
    MetricOnly (score (M := M) (Q := Q) C d a rho tau) := by
  apply metricOnly_foldList
  intro best t
  exact metricOnly_bind _ _ (candidate_only C d a rho tau t) (fun _ => trivial)

theorem program_metricOnly (C : List (Fin n)) (a rho tau : ℝ) :
    MetricOnly (program (Q := Q) C a rho tau) := by
  apply metricOnly_bind
  · apply metricOnly_bind _ _ (by trivial)
    intro init
    apply metricOnly_tabulate
    intro p
    change ∀ x : ℝ, True
    intro _
    trivial
  · intro d
    exact score_only _ d a rho tau

theorem compiled_outcome (oracle : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (C : List (Fin n)) (a rho tau : ℝ)
    (s : ((program (Q := Q) C a rho tau).compile oracle).Seed) :
    (((program (Q := Q) C a rho tau).compile oracle).tree s).output bits = run oracle C a rho tau :=
  compiled_output_of_evaluates _ _ _ (program_metricOnly C a rho tau) _ (program_evaluates _ _ _ _ _ _) s

theorem compiled_spec (I : Instance (Fin n)) (bits : Q → Bool) (C : List (Fin n)) (hC : C.Nodup)
    (a rho tau : ℝ) (ha : 0 ≤ a) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (hband : tau * a ≤ a - 2 * rho)
    (s : ((program (Q := Q) C a rho tau).compile I.weight).Seed) :
    let o := (((program (Q := Q) C a rho tau).compile I.weight).tree s).output bits
    o.value = Band.score I C.toFinset a rho tau ∧ 0 ≤ o.value ∧ o.value ≤ 3 * a ∧
      o.metricQueries ≤ n * C.length ∧
      o.work ≤ 10000000000 * (n + 1) * (C.length + 1) ^ 12 ∧
      o.retentionQueries = 0 ∧ o.positiveReplies = 0 := by
  dsimp only
  rw [compiled_outcome]
  have hb := program_bounds I C hC a rho tau ha hrho htau hband
  exact ⟨program_correct I C hC a rho tau hband, hb.1, hb.2,
    run_queries I.weight C a rho tau, run_work I.weight C a rho tau,
    (run_resources I.weight C a rho tau).1, (run_resources I.weight C a rho tau).2⟩

end SteinerUpperBound.BandEvaluation
