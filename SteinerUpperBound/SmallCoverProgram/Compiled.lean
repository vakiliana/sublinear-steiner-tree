module

public import SteinerUpperBound.SmallCoverProgram.List

@[expose] public section

namespace SteinerUpperBound.SmallCoverProgram

open QueryProgram
open scoped Classical

variable {M Q R S : Type*}

def MetricOnly : Code M Q R → Prop
  | .pure _ => True
  | .metric _ next => ∀ x, MetricOnly (next x)
  | .tick _ next => MetricOnly next
  | _ => False

theorem metricOnly_bind (p : Code M Q R) (k : R → Code M Q S)
    (hp : MetricOnly p) (hk : ∀ r, MetricOnly (k r)) : MetricOnly (p.bind k) := by
  induction p with
  | pure r => exact hk r
  | metric q next ih => exact fun x => ih x (hp x)
  | tick n next ih => exact ih hp
  | retained q next ih => exact hp.elim
  | uniform n next ih => exact hp.elim
  | coin p next ih => exact hp.elim

theorem metricOnly_map (p : Code M Q R) (f : R → S) (hp : MetricOnly p) :
    MetricOnly (p.map f) :=
  metricOnly_bind p (fun r => .pure (f r)) hp (fun _ => trivial)

theorem metricOnly_foldList {A : Type*} (body : S → A → Code M Q S)
    (hbody : ∀ s a, MetricOnly (body s a)) (l : List A) (s : S) :
    MetricOnly (Code.foldList body l s) := by
  induction l generalizing s with
  | nil => trivial
  | cons a l ih => exact metricOnly_bind _ _ (hbody s a) ih

theorem metricOnly_tabulate {α : Type*} {n : ℕ} (body : Fin n → Code M Q α)
    (hbody : ∀ i, MetricOnly (body i)) (init : Vector α n) :
    MetricOnly (tabulate body init) := by
  apply metricOnly_foldList
  intro v i
  exact metricOnly_bind _ _ (hbody i) (fun _ => trivial)

theorem metricOnly_compiled_subsingleton (m : M → ℝ) (p : Code M Q R) (hp : MetricOnly p) :
    Subsingleton (p.compile m).Seed := by
  induction p with
  | pure r => change Subsingleton Unit; infer_instance
  | metric q next ih => exact ih (m q) (hp (m q))
  | tick n next ih => exact ih hp
  | retained q next ih => exact hp.elim
  | uniform n next ih => exact hp.elim
  | coin rate next ih => exact hp.elim

theorem compiled_output_of_evaluates (m : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (hp : MetricOnly p) (o : Outcome R) (he : Code.Evaluates m b p o)
    (s : (p.compile m).Seed) : ((p.compile m).tree s).output b = o := by
  classical
  let _ := metricOnly_compiled_subsingleton m p hp
  let F : Outcome R → ℝ := fun r => if r = o then 1 else 0
  have hmean : (p.compile m).expect b F = 1 := by
    rw [Code.compile_expect, he]
    simp [F]
  have hpoint : (p.compile m).expect b F = F (((p.compile m).tree s).output b) := by
    unfold Compiled.expect
    have hfun : (fun t => F (((p.compile m).tree t).output b)) =
        fun _ => F (((p.compile m).tree s).output b) := by
      funext t
      rw [Subsingleton.elim t s]
    rw [hfun]
    exact SteinerLowerBound.Law.expect_const _ _
  rw [hpoint] at hmean
  by_contra hn
  simp [F, hn] at hmean

private theorem allocate_only {α : Type*} (n : ℕ) (x : α) :
    MetricOnly (allocate (M := M) (Q := Q) n x) := trivial

private theorem metricTable_only {n g : ℕ} (N : Vector (Fin n) g) :
    MetricOnly (metricTable (Q := Q) N) := by
  apply metricOnly_bind _ _ (allocate_only _ _)
  intro init
  apply metricOnly_tabulate
  intro p
  change ∀ x : ℝ, True
  intro _
  trivial

private theorem adjacency_only {n g : ℕ} (N : Vector (Fin n) g) (d : MetricTable n g) (a : ℝ) :
    MetricOnly (adjacencyTable (Q := Q) N d a) := by
  apply metricOnly_bind _ _ (allocate_only _ _)
  intro init
  apply metricOnly_tabulate
  intro _
  trivial

theorem closure_metricOnly {g : ℕ} (a : Closure.Dense Bool g) :
    MetricOnly (Closure.closure (M := M) (Q := Q) a) := by
  have hi (t : Closure.Dense Bool g) : MetricOnly (Closure.initial (M := M) (Q := Q) t) := by
    apply metricOnly_bind _ _ (allocate_only _ _)
    intro init
    apply metricOnly_tabulate
    intro _
    trivial
  have hs (t : Closure.Dense Bool g) : MetricOnly (Closure.square (M := M) (Q := Q) t) := by
    apply metricOnly_bind _ _ (allocate_only _ _)
    intro init
    apply metricOnly_tabulate
    intro p
    apply metricOnly_foldList
    intro _ _
    trivial
  have hit (r : ℕ) (t : Closure.Dense Bool g) :
      MetricOnly (Closure.iterate (M := M) (Q := Q) r t) := by
    induction r generalizing t with
    | zero => trivial
    | succ r ih => exact metricOnly_bind _ _ (hs t) ih
  exact metricOnly_bind _ _ (hi a) (hit _)

private theorem roots_only {g : ℕ} (a : Closure.Dense Bool g) :
    MetricOnly (Closure.roots (M := M) (Q := Q) a) := by
  apply metricOnly_bind _ _ (allocate_only _ _)
  intro init
  apply metricOnly_tabulate
  intro x
  apply metricOnly_map
  apply metricOnly_foldList
  intro _ _
  trivial

private theorem rows_only {n g : ℕ} (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ) :
    MetricOnly (rowTable (M := M) (Q := Q) d roots radius) := by
  apply metricOnly_bind _ _ (allocate_only _ _)
  intro emptyRow
  apply metricOnly_bind _ _ (allocate_only _ _)
  intro init
  apply metricOnly_tabulate
  intro v
  apply metricOnly_bind _ _ (allocate_only _ _)
  intro mask
  apply metricOnly_foldList
  intro _ _
  trivial

private theorem greedy_only {n g : ℕ} (rows : Vector (Vector Bool g) n) :
    MetricOnly (greedyScore (M := M) (Q := Q) rows) := by
  have hc (row claimed : Vector Bool g) : MetricOnly (counts (M := M) (Q := Q) row claimed) := by
    apply metricOnly_foldList
    intro _ _
    trivial
  have hclaim (row claimed : Vector Bool g) : MetricOnly (claim (M := M) (Q := Q) row claimed) := by
    apply metricOnly_tabulate
    intro _
    trivial
  have hcommit (row : Vector Bool g) (s : GreedyState g) (c : ℕ × ℕ) :
      MetricOnly (commit (M := M) (Q := Q) row s c) := by
    unfold commit
    split_ifs
    · exact metricOnly_bind _ _ (hclaim _ _) (fun _ => trivial)
    · trivial
  have hg : MetricOnly (greedy (M := M) (Q := Q) rows) := by
    apply metricOnly_bind _ _ (allocate_only _ _)
    intro mask
    apply metricOnly_foldList
    intro s v
    exact metricOnly_bind _ _ (hc _ _) (hcommit _ _)
  exact metricOnly_bind _ _ hg (fun _ => trivial)

theorem programVector_metricOnly {n g : ℕ} (N : Vector (Fin n) g) (a : ℝ) :
    MetricOnly (programVector (Q := Q) N a) := by
  unfold programVector
  split_ifs
  · trivial
  · apply metricOnly_bind _ _ (metricTable_only N)
    intro d
    apply metricOnly_bind _ _ (adjacency_only N d a)
    intro adj
    apply metricOnly_bind _ _ (closure_metricOnly adj)
    intro connected
    apply metricOnly_bind _ _ (roots_only connected)
    intro roots
    exact metricOnly_bind _ _ (rows_only d roots _) greedy_only

theorem program_metricOnly {n : ℕ} (N : List (Fin n)) (a : ℝ) :
    MetricOnly (program (Q := Q) N a) := by
  cases N with
  | nil => trivial
  | cons x l => exact programVector_metricOnly _ _

theorem compiled_outcome {n : ℕ} (m : Sym2 (Fin n) → ℝ) (b : Q → Bool)
    (N : List (Fin n)) (a : ℝ) (s : ((program (Q := Q) N a).compile m).Seed) :
    (((program (Q := Q) N a).compile m).tree s).output b = run m N a :=
  compiled_output_of_evaluates m b _ (program_metricOnly N a) _ (program_evaluates m b N a) s

theorem compiled_spec {n : ℕ} (I : Instance (Fin n)) (b : Q → Bool)
    (N : List (Fin n)) (hN : N.Nodup) (a : ℝ)
    (s : ((program (Q := Q) N a).compile I.weight).Seed) :
    let o := (((program (Q := Q) N a).compile I.weight).tree s).output b
    o.value =
        SetSystem.smallCoverEstimate (Covers.Geometry.eligibleOn I N.toFinset a (5 * a / 8))
          (Covers.Geometry.rowOn I N.toFinset a (5 * a / 8))
          (Covers.Geometry.componentsOn I N.toFinset a) (List.finRange n) ∧
      0 ≤ o.value ∧ o.value ≤ Covers.Geometry.savingOn I N.toFinset a (5 * a / 8) ∧
      Covers.Geometry.savingOn I N.toFinset a (5 * a / 8) / 2 ≤ o.value ∧
      o.metricQueries ≤ n * N.length ∧
      o.work ≤ 128 * (n * N.length + N.length ^ 3 * (1 + Nat.log2 (N.length + 1))) ∧
      o.retentionQueries = 0 ∧ o.positiveReplies = 0 := by
  dsimp only
  rw [compiled_outcome I.weight b N a s]
  have hg := program_guarantee I N hN a
  exact ⟨program_agrees I N hN a, hg.1, hg.2.1, hg.2.2, run_queries I.weight N a,
    run_work I.weight N hN a, (run_resources I.weight N a).1, (run_resources I.weight N a).2⟩

end SteinerUpperBound.SmallCoverProgram
