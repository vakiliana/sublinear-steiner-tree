module

public import SteinerUpperBound.SmallCoverProgram.Tables

@[expose] public section

namespace SteinerUpperBound.SmallCoverProgram

open QueryProgram
open scoped Classical

variable {M Q : Type*} {n g : ℕ}

def putNat (v : Vector Bool g) (i : ℕ) (b : Bool) : Vector Bool g :=
  if h : i < g then put v ⟨i, h⟩ b else v

theorem get_putNat (v : Vector Bool g) (i : ℕ) (b : Bool) (j : Fin g) :
    (putNat v i b).get j = if i = j.val then b else v.get j := by
  by_cases hi : i < g
  · simp only [putNat, hi, ↓reduceDIte, get_put, Fin.ext_iff]
  · have hn : i ≠ j.val := by intro h; exact hi (h ▸ j.isLt)
    simp only [putNat, hi, ↓reduceDIte, hn, ↓reduceIte]

def mark (target : Fin g → ℕ) (near : Fin g → Bool)
    (v : Vector Bool g) (i : Fin g) : Vector Bool g :=
  if near i then putNat v (target i) true else v

theorem markFold_get (target : Fin g → ℕ) (near : Fin g → Bool)
    (l : List (Fin g)) (init : Vector Bool g) (j : Fin g) :
    (l.foldl (mark target near) init).get j = true ↔
      init.get j = true ∨ ∃ i ∈ l, near i = true ∧ target i = j.val := by
  induction l generalizing init with
  | nil => simp
  | cons i l ih =>
      rw [List.foldl_cons, ih]
      by_cases hn : near i = true
      · simp only [mark, hn, ↓reduceIte, get_putNat, List.mem_cons]
        by_cases ht : target i = j.val
        · simp [ht, hn]
        · simp [ht, hn]
      · simp only [mark, hn, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
        aesop

noncomputable def markRow (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ)
    (v : Fin n) (mask : Vector Bool g) (i : Fin g) : Code M Q (Vector Bool g) :=
  .tick 9 (.pure (mark roots.get (fun k => decide (distanceAt d k v ≤ radius)) mask i))

noncomputable def markRowRun (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ)
    (v : Fin n) (mask : Vector Bool g) (i : Fin g) : Outcome (Vector Bool g) :=
  ⟨mark roots.get (fun k => decide (distanceAt d k v ≤ radius)) mask i, 10, 0, 0, 0⟩

noncomputable def rowMask (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ) (v : Fin n) :
    Code M Q (Vector Bool g) :=
  (allocate g false).bind
    (fun init => Code.foldList (markRow d roots radius v) (List.finRange g) init)

noncomputable def rowMaskRun (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ) (v : Fin n) :
    Outcome (Vector Bool g) :=
  (allocated g false).combine
    (Code.folded (markRowRun d roots radius v) (List.finRange g) (Vector.replicate g false))

noncomputable def rowTable (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ) :
    Code M Q (Vector (Vector Bool g) n) :=
  (allocate g false).bind (fun emptyRow =>
    (allocate n emptyRow).bind (fun init => tabulate (rowMask d roots radius) init))

noncomputable def rowTableRun (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ) :
    Outcome (Vector (Vector Bool g) n) :=
  (allocated g false).combine ((allocated n (Vector.replicate g false)).combine
    (tabulated (rowMaskRun d roots radius) (Vector.replicate n (Vector.replicate g false))))

theorem markRow_evaluates (m : M → ℝ) (b : Q → Bool)
    (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ) (v : Fin n) (mask) (i) :
    Code.Evaluates m b (markRow d roots radius v mask i) (markRowRun d roots radius v mask i) :=
  Code.Evaluates.tick m b _ _ (Code.evaluates_pure m b _) 9

theorem rowMask_evaluates (m : M → ℝ) (b : Q → Bool)
    (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ) (v : Fin n) :
    Code.Evaluates m b (rowMask d roots radius v) (rowMaskRun d roots radius v) :=
  Code.Evaluates.bind m b _ _ _ _ (allocate_evaluates m b _ _)
    (Code.foldList_evaluates m b _ _ (markRow_evaluates m b d roots radius v) _ _)

theorem rowTable_evaluates (m : M → ℝ) (b : Q → Bool)
    (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ) :
    Code.Evaluates m b (rowTable d roots radius) (rowTableRun d roots radius) :=
  Code.Evaluates.bind m b _ _ _ _ (allocate_evaluates m b _ _)
    (Code.Evaluates.bind m b _ _ _ _ (allocate_evaluates m b _ _)
      (tabulate_evaluates m b _ _ (rowMask_evaluates m b d roots radius) _))

theorem rowMask_get (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ) (v : Fin n)
    (j : Fin g) :
    (rowMaskRun d roots radius v).value.get j = true ↔
      ∃ i : Fin g, distanceAt d i v ≤ radius ∧ roots.get i = j.val := by
  change (Code.folded (markRowRun d roots radius v) _ _).value.get j = true ↔ _
  rw [folded_value]
  change ((List.finRange g).foldl
    (mark roots.get (fun k => decide (distanceAt d k v ≤ radius))) (Vector.replicate g false)).get j =
      true ↔ _
  rw [markFold_get]
  simp

theorem rowTable_get (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ) (v : Fin n)
    (j : Fin g) :
    ((rowTableRun d roots radius).value.get v).get j = true ↔
      ∃ i : Fin g, distanceAt d i v ≤ radius ∧ roots.get i = j.val := by
  change ((tabulated (rowMaskRun d roots radius) _).value.get v).get j = true ↔ _
  rw [tabulated_get]
  exact rowMask_get d roots radius v j

theorem rowMask_work (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ) (v : Fin n) :
    (rowMaskRun d roots radius v).work ≤ 12 * g + 1 := by
  have hh := Code.folded_work (markRowRun d roots radius v) 10 (fun _ _ => le_rfl)
    (List.finRange g) (Vector.replicate g false)
  simp only [List.length_finRange] at hh
  dsimp only [rowMaskRun, Outcome.combine, allocated]
  omega

theorem rowTable_work (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ) :
    (rowTableRun d roots radius).work ≤ (12 * g + 4) * n + g + 2 := by
  have hh := tabulated_work (rowMaskRun d roots radius)
    (Vector.replicate n (Vector.replicate g false)) (12 * g + 1) (rowMask_work d roots radius)
  dsimp only [rowTableRun, Outcome.combine, allocated]
  nlinarith

theorem rowMask_resources (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ) (v : Fin n) :
    (rowMaskRun d roots radius v).metricQueries = 0 ∧
      (rowMaskRun d roots radius v).retentionQueries = 0 ∧
      (rowMaskRun d roots radius v).positiveReplies = 0 := by
  have hm := Code.folded_metric_queries (markRowRun d roots radius v) 0 (fun _ _ => le_rfl)
    (List.finRange g) (Vector.replicate g false)
  have hr := folded_retention_zero (markRowRun d roots radius v) (fun _ _ => rfl)
    (List.finRange g) (Vector.replicate g false)
  have hp := folded_positive_zero (markRowRun d roots radius v) (fun _ _ => rfl)
    (List.finRange g) (Vector.replicate g false)
  dsimp only [rowMaskRun, Outcome.combine, allocated]
  simp only [Nat.zero_add]
  exact ⟨by simpa only [Nat.zero_mul, Nat.le_zero] using hm, hr, hp⟩

theorem rowTable_resources (d : MetricTable n g) (roots : Vector ℕ g) (radius : ℝ) :
    (rowTableRun d roots radius).metricQueries = 0 ∧
      (rowTableRun d roots radius).retentionQueries = 0 ∧
      (rowTableRun d roots radius).positiveReplies = 0 := by
  have hm := tabulated_metricQueries (rowMaskRun d roots radius)
    (Vector.replicate n (Vector.replicate g false)) 0
    (fun v => (rowMask_resources d roots radius v).1.le)
  have hr := tabulated_retention_zero (rowMaskRun d roots radius)
    (Vector.replicate n (Vector.replicate g false))
    (fun v => (rowMask_resources d roots radius v).2.1)
  have hp := tabulated_positive_zero (rowMaskRun d roots radius)
    (Vector.replicate n (Vector.replicate g false))
    (fun v => (rowMask_resources d roots radius v).2.2)
  dsimp only [rowTableRun, Outcome.combine, allocated]
  simp only [Nat.zero_add]
  exact ⟨by simpa only [Nat.zero_mul, Nat.le_zero] using hm, hr, hp⟩

end SteinerUpperBound.SmallCoverProgram
