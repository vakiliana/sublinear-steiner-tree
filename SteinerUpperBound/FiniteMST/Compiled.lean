module

public import SteinerUpperBound.FiniteMST.Labels
public import SteinerUpperBound.SmallCoverProgram.Compiled

@[expose] public section

namespace SteinerUpperBound.FiniteMST

open QueryProgram SmallCoverProgram
open scoped Classical

variable {M Q : Type*} {m : ℕ}

theorem program_metricOnly (d : Matrix m) : MetricOnly (program (M := M) (Q := Q) d) := by
  have hi (e : Edge m) (l : List (Edge m)) : MetricOnly (insert (M := M) (Q := Q) d e l) := by
    induction l with
    | nil => trivial
    | cons f l ih =>
        unfold insert
        split_ifs
        · trivial
        · exact metricOnly_map _ _ ih
  have hs (l : List (Edge m)) : MetricOnly (sort (M := M) (Q := Q) d l) := by
    induction l with
    | nil => trivial
    | cons e l ih => exact metricOnly_bind _ _ ih (hi e)
  have hk (l : List (Edge m)) : MetricOnly (kruskal (M := M) (Q := Q) d l) := by
    apply metricOnly_bind _ _ (by trivial)
    intro a
    apply metricOnly_bind
    · apply metricOnly_foldList
      intro s e
      exact metricOnly_bind _ _ (closure_metricOnly s.adjacency) (fun _ => trivial)
    · intro _
      trivial
  have hc : MetricOnly (candidates (M := M) (Q := Q) m) := by
    apply metricOnly_foldList
    intro _ _
    trivial
  exact metricOnly_bind _ _ hc (fun l => metricOnly_bind _ _ (hs l) hk)

theorem compiled_outcome (oracle : M → ℝ) (bits : Q → Bool) (d : Matrix m)
    (s : ((program (M := M) (Q := Q) d).compile oracle).Seed) :
    (((program (M := M) (Q := Q) d).compile oracle).tree s).output bits = run d :=
  compiled_output_of_evaluates _ _ _ (program_metricOnly d) _ (program_evaluates _ _ d) s

theorem compiled_spec (oracle : M → ℝ) (bits : Q → Bool) (d : Matrix m)
    (hd : ∀ i j, 0 ≤ Closure.entry d i j)
    (s : ((program (M := M) (Q := Q) d).compile oracle).Seed) :
    let o := (((program (M := M) (Q := Q) d).compile oracle).tree s).output bits
    o.value = TerminalMST.value (weight d) Finset.univ ∧
      o.work ≤ 512 * (m + 1) ^ 6 * (1 + Nat.log2 (m + 1)) ∧
      o.metricQueries = 0 ∧ o.retentionQueries = 0 ∧ o.positiveReplies = 0 := by
  dsimp only
  rw [compiled_outcome]
  exact ⟨program_correct d hd, run_work d, (run_resources d).1,
    (run_resources d).2.1, (run_resources d).2.2⟩

end SteinerUpperBound.FiniteMST
