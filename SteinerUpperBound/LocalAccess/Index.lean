module

public import SteinerUpperBound.LocalAccess.Located

@[expose] public section

namespace SteinerUpperBound.LocalAccess

open QueryProgram
open scoped Classical

variable {V M Q : Type*} {d : ℕ}

noncomputable def indexScanProgram (get : Fin d → Option V) (x : V) :
    List (Fin d) → Code M Q (Option (Fin d))
  | [] => .tick 0 (.pure none)
  | i :: l => .tick 1 (if get i = some x then .pure (some i) else indexScanProgram get x l)

noncomputable def indexScanResult (get : Fin d → Option V) (x : V) :
    List (Fin d) → Outcome (Option (Fin d))
  | [] => (Outcome.pure none).add 1 0 0 0
  | i :: l =>
      (if get i = some x then Outcome.pure (some i) else indexScanResult get x l).add 2 0 0 0

theorem indexScan_evaluates (m : M → ℝ) (bits : Q → Bool) (get : Fin d → Option V)
    (x : V) (l : List (Fin d)) :
    Code.Evaluates m bits (indexScanProgram get x l) (indexScanResult get x l) := by
  induction l with
  | nil => intro F; rfl
  | cons i l ih =>
      intro F
      by_cases h : get i = some x
      · simp only [indexScanProgram, indexScanResult, h, ite_true, Code.evaluate]
      · simpa only [indexScanProgram, indexScanResult, h, ite_false, Code.evaluate] using
          ih (fun o => F (o.add 2 0 0 0))

theorem indexScan_some (get : Fin d → Option V) (x : V) (l : List (Fin d)) {i : Fin d}
    (h : (indexScanResult get x l).value = some i) : i ∈ l ∧ get i = some x := by
  induction l with
  | nil => simp [indexScanResult, Outcome.add, Outcome.pure] at h
  | cons j l ih =>
      by_cases hj : get j = some x
      · simp only [indexScanResult, hj, ite_true, Outcome.add, Outcome.pure, Option.some.injEq] at h
        subst i
        exact ⟨List.mem_cons_self, hj⟩
      · simp only [indexScanResult, hj, ite_false, Outcome.add] at h
        have hh := ih h
        exact ⟨List.mem_cons_of_mem _ hh.1, hh.2⟩

theorem indexScan_none (get : Fin d → Option V) (x : V) (l : List (Fin d)) :
    (indexScanResult get x l).value = none ↔ ∀ i ∈ l, get i ≠ some x := by
  induction l with
  | nil => simp [indexScanResult, Outcome.add, Outcome.pure]
  | cons j l ih =>
      by_cases hj : get j = some x <;>
        simp [indexScanResult, hj, Outcome.add, Outcome.pure, ih]

theorem indexScan_work (get : Fin d → Option V) (x : V) (l : List (Fin d)) :
    (indexScanResult get x l).work ≤ 2 * l.length + 1 := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih =>
      by_cases h : get i = some x <;>
        simp only [indexScanResult, h, ite_true, ite_false, Outcome.add, Outcome.pure,
          List.length_cons] <;> omega

theorem indexScan_counters (get : Fin d → Option V) (x : V) (l : List (Fin d)) :
    (indexScanResult get x l).metricQueries = 0 ∧
      (indexScanResult get x l).retentionQueries = 0 ∧
      (indexScanResult get x l).positiveReplies = 0 := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons i l ih =>
      by_cases h : get i = some x <;>
        simp [indexScanResult, h, Outcome.add, Outcome.pure, ih]

noncomputable def indexProgram (get : Fin d → Option V) (x : V) : Code M Q (Option (Fin d)) :=
  indexScanProgram get x (List.finRange d)

noncomputable def indexResult (get : Fin d → Option V) (x : V) : Outcome (Option (Fin d)) :=
  indexScanResult get x (List.finRange d)

theorem index_evaluates (m : M → ℝ) (bits : Q → Bool) (get : Fin d → Option V) (x : V) :
    Code.Evaluates m bits (indexProgram get x) (indexResult get x) :=
  indexScan_evaluates m bits get x _

theorem index_some (get : Fin d → Option V) (x : V) {i : Fin d}
    (h : (indexResult get x).value = some i) : get i = some x :=
  (indexScan_some get x _ h).2

theorem index_exists (get : Fin d → Option V) (x : V) (h : ∃ i, get i = some x) :
    ∃ i, (indexResult get x).value = some i := by
  have hn : (indexResult get x).value ≠ none := by
    intro hnone
    have hh := (indexScan_none get x (List.finRange d)).mp hnone
    obtain ⟨i, hi⟩ := h
    exact hh i (List.mem_finRange i) hi
  exact Option.ne_none_iff_exists'.mp hn

theorem index_work (get : Fin d → Option V) (x : V) :
    (indexResult get x).work ≤ 2 * d + 1 := by
  simpa only [indexResult, List.length_finRange] using indexScan_work get x (List.finRange d)

end SteinerUpperBound.LocalAccess
