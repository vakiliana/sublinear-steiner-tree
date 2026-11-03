module

public import SteinerUpperBound.FiniteMST.Kruskal

@[expose] public section

set_option maxHeartbeats 1500000

namespace SteinerUpperBound.FiniteMST

open SteinerLowerBound QueryProgram SmallCoverProgram
open scoped Classical

variable {M Q : Type*} {m : ℕ}

noncomputable def kruskal (d : Matrix m) (l : List (Edge m)) : Code M Q ℝ :=
  (allocate (m * m) false).bind (fun a =>
    .tick 0 ((Code.foldList (step d) l ⟨a, 0⟩).bind (fun s => .tick 0 (.pure s.cost))))

def kruskalRun (d : Matrix m) (l : List (Edge m)) : Outcome ℝ :=
  let init : State m := ⟨Vector.replicate (m * m) false, 0⟩
  let out := Code.folded (stepRun d) l init
  (allocated (m * m) false).combine
    ((out.combine ((Outcome.pure out.value.cost).add 1 0 0 0)).add 1 0 0 0)

noncomputable def program (d : Matrix m) : Code M Q ℝ :=
  (candidates m).bind (fun l => (sort d l).bind (kruskal d))

noncomputable def run (d : Matrix m) : Outcome ℝ :=
  let c := candidatesRun m
  let s := sortRun d c.value
  c.combine (s.combine (kruskalRun d s.value))

theorem kruskal_evaluates (oracle : M → ℝ) (bits : Q → Bool) (d : Matrix m) (l : List (Edge m)) :
    Code.Evaluates oracle bits (kruskal d l) (kruskalRun d l) :=
  Code.Evaluates.bind _ _ _ _ _ _ (allocate_evaluates _ _ _ _)
    (Code.Evaluates.tick _ _ _ _
      (Code.Evaluates.bind _ _ _ _ _ _
        (Code.foldList_evaluates _ _ _ _ (step_evaluates oracle bits d) _ _)
        (Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 0)) 0)

theorem program_evaluates (oracle : M → ℝ) (bits : Q → Bool) (d : Matrix m) :
    Code.Evaluates oracle bits (program d) (run d) :=
  Code.Evaluates.bind _ _ _ _ _ _ (candidates_evaluates _ _ _)
    (Code.Evaluates.bind _ _ _ _ _ _ (sort_evaluates _ _ _ _) (kruskal_evaluates _ _ _ _))

theorem kruskalRun_value (d : Matrix m) (l : List (Edge m)) (hv : ∀ e ∈ l, valid e) :
    (kruskalRun d l).value = GraphCost.cost (weight d) (SpanningForest.run (l.map sym) ⊥) := by
  have hi : Represents d (⟨Vector.replicate (m * m) false, 0⟩ : State m) ⊥ := by
    refine ⟨?_, ?_⟩
    · intro x y
      simp [Closure.entry, Vector.get_replicate]
    · exact (Network.cost_bot _).symm
  exact (folded_represents d l hv _ _ hi).2

theorem run_value (d : Matrix m) :
    (run d).value = (kruskalRun d (sortRun d (baseCandidates m)).value).value := by
  simp only [run, Outcome.combine, candidatesRun_value]

theorem program_correct (d : Matrix m) (hd : ∀ i j, 0 ≤ Closure.entry d i j) :
    (run d).value = TerminalMST.value (weight d) (Finset.univ : Finset (Fin m)) := by
  let l := (sortRun d (baseCandidates m)).value
  have hp : l.Perm (baseCandidates m) := sortRun_perm d _
  have hv : ∀ e ∈ l, valid e := fun e he => (mem_baseCandidates e).mp (hp.mem_iff.mp he)
  have hn := sym_list_nodup l (hp.nodup_iff.mpr (baseCandidates_nodup m)) hv
  have hs := sortRun_sym_pairwise d (baseCandidates m) (fun e he => (mem_baseCandidates e).mp he)
  rw [run_value, kruskalRun_value d _ hv]
  exact (TerminalMST.SortedInput.value_eq_cost (weight d) (weight_nonneg d hd)
    (l.map sym) Finset.univ (candidates_span l hp) hn hs).symm

theorem kruskalRun_work (d : Matrix m) (l : List (Edge m)) :
    (kruskalRun d l).work ≤
      (32 * (m + 1) ^ 3 * (1 + Nat.log2 (m + 1)) + 65) * l.length + m * m + 3 := by
  have hh := Code.folded_work (stepRun d)
    (32 * (m + 1) ^ 3 * (1 + Nat.log2 (m + 1)) + 64)
    (stepRun_work d) l ⟨Vector.replicate (m * m) false, 0⟩
  dsimp only [kruskalRun, allocated, Outcome.combine, Outcome.add, Outcome.pure]
  nlinarith

theorem run_work (d : Matrix m) :
    (run d).work ≤ 512 * (m + 1) ^ 6 * (1 + Nat.log2 (m + 1)) := by
  let p := m + 1
  let r := 1 + Nat.log2 (m + 1)
  have hp : 1 ≤ p := by dsimp [p]; omega
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hc := candidatesRun_work m
  have hn := baseCandidates_length m
  have hsort := sortRun_work d (baseCandidates m)
  have hlen := (sortRun_perm d (baseCandidates m)).length_eq
  have hk := kruskalRun_work d (sortRun d (baseCandidates m)).value
  rw [hlen] at hk
  have hm2 : m * m + 1 ≤ p ^ 2 := by dsimp [p]; nlinarith
  have hc' : (candidatesRun m).work ≤ 9 * p ^ 2 := by nlinarith
  have hs' : (sortRun d (baseCandidates m)).work ≤ 20 * p ^ 4 := by
    have hh : ((baseCandidates m).length + 1) ^ 2 ≤ (p ^ 2) ^ 2 := by gcongr; omega
    nlinarith
  have hk' : (kruskalRun d (sortRun d (baseCandidates m)).value).work ≤
      32 * p ^ 5 * r + 66 * p ^ 2 + 3 := by
    have hh : (32 * p ^ 3 * r + 65) * (baseCandidates m).length ≤
        (32 * p ^ 3 * r + 65) * p ^ 2 := by gcongr; omega
    change _ ≤ (32 * p ^ 3 * r + 65) * (baseCandidates m).length + m * m + 3 at hk
    nlinarith
  have hp6 : p ^ 6 ≤ p ^ 6 * r := by nlinarith [Nat.mul_le_mul_left (p ^ 6) hr]
  have hp2 := (pow_le_pow_right₀ hp (by omega : 2 ≤ 6)).trans hp6
  have hp4 := (pow_le_pow_right₀ hp (by omega : 4 ≤ 6)).trans hp6
  have hp5 := Nat.mul_le_mul_right r (pow_le_pow_right₀ hp (by omega : 5 ≤ 6))
  have h1 : 1 ≤ p ^ 6 * r := by
    have hpos : 0 < p ^ 6 * r := by positivity
    omega
  simp only [run, Outcome.combine, candidatesRun_value]
  change _ ≤ 512 * p ^ 6 * r
  nlinarith

theorem kruskalRun_resources (d : Matrix m) (l : List (Edge m)) :
    (kruskalRun d l).metricQueries = 0 ∧ (kruskalRun d l).retentionQueries = 0 ∧
      (kruskalRun d l).positiveReplies = 0 := by
  let init : State m := ⟨Vector.replicate (m * m) false, 0⟩
  have hm := Code.folded_metric_queries (stepRun d) 0
    (fun s e => (stepRun_resources d s e).1.le) l init
  have hr := folded_retention_zero (stepRun d) (fun s e => (stepRun_resources d s e).2.1) l init
  have hp := folded_positive_zero (stepRun d) (fun s e => (stepRun_resources d s e).2.2) l init
  dsimp only [kruskalRun, allocated, Outcome.combine, Outcome.add, Outcome.pure]
  simp only [Nat.zero_add, Nat.add_zero]
  exact ⟨by simpa only [Nat.zero_mul, Nat.le_zero] using hm, hr, hp⟩

theorem run_resources (d : Matrix m) :
    (run d).metricQueries = 0 ∧ (run d).retentionQueries = 0 ∧ (run d).positiveReplies = 0 := by
  have hc := candidatesRun_resources m
  have hs := sortRun_resources d (candidatesRun m).value
  have hk := kruskalRun_resources d (sortRun d (candidatesRun m).value).value
  simp only [run, Outcome.combine, hc, hs, hk, Nat.zero_add, and_self]

end SteinerUpperBound.FiniteMST
