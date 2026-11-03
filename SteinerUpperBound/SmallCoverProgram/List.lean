module

public import SteinerUpperBound.SmallCoverProgram.Program

@[expose] public section

namespace SteinerUpperBound.SmallCoverProgram

open QueryProgram Covers.Geometry
open scoped Classical

variable {α Q : Type*} {n : ℕ}

def asVector (l : List α) : Vector α l.length := ⟨l.toArray, by simp⟩

theorem asVector_get (l : List α) (i : Fin l.length) : (asVector l).get i = l.get i := by
  simp [asVector, Vector.get_eq_getElem, List.get_eq_getElem]

theorem asVector_injective (l : List α) (h : l.Nodup) : Function.Injective (asVector l).get := by
  intro i j he
  rw [asVector_get, asVector_get] at he
  exact h.get_inj_iff.mp he

theorem retained_asVector (l : List (Fin n)) : retained (asVector l) = l.toFinset := by
  ext x
  simp only [mem_retained, List.mem_toFinset, List.mem_iff_get, asVector_get]

/-- Convert the already revealed retained list once, then use RAM vector accesses. -/
noncomputable def program (N : List (Fin n)) (a : ℝ) : Code (Sym2 (Fin n)) Q ℝ :=
  match N with
  | [] => .pure 0
  | _ :: _ => .tick (4 * N.length + 3) (programVector (asVector N) a)

noncomputable def run (m : Sym2 (Fin n) → ℝ) (N : List (Fin n)) (a : ℝ) : Outcome ℝ :=
  match N with
  | [] => .pure 0
  | _ :: _ => (runVector m (asVector N) a).add (4 * N.length + 4) 0 0 0

theorem program_evaluates (m : Sym2 (Fin n) → ℝ) (b : Q → Bool)
    (N : List (Fin n)) (a : ℝ) :
    Code.Evaluates m b (program N a) (run m N a) := by
  cases N with
  | nil => exact Code.evaluates_pure _ _ _
  | cons x l =>
      exact Code.Evaluates.tick m b _ _ (programVector_evaluates m b (asVector (x :: l)) a) _

theorem run_value (m : Sym2 (Fin n) → ℝ) (N : List (Fin n)) (a : ℝ) :
    (run m N a).value = (runVector m (asVector N) a).value := by
  cases N <;> rfl

theorem program_agrees (I : Instance (Fin n)) (N : List (Fin n)) (hN : N.Nodup) (a : ℝ) :
    (run I.weight N a).value =
      SetSystem.smallCoverEstimate (eligibleOn I N.toFinset a (5 * a / 8))
        (rowOn I N.toFinset a (5 * a / 8)) (componentsOn I N.toFinset a) (List.finRange n) := by
  rw [run_value]
  simpa only [retained_asVector] using
    programVector_agrees I (asVector N) (asVector_injective N hN) a

theorem program_guarantee (I : Instance (Fin n)) (N : List (Fin n)) (hN : N.Nodup) (a : ℝ) :
    0 ≤ (run I.weight N a).value ∧
      (run I.weight N a).value ≤ savingOn I N.toFinset a (5 * a / 8) ∧
      savingOn I N.toFinset a (5 * a / 8) / 2 ≤ (run I.weight N a).value := by
  rw [run_value]
  simpa only [retained_asVector] using
    programVector_guarantee I (asVector N) (asVector_injective N hN) a

theorem run_queries (m : Sym2 (Fin n) → ℝ) (N : List (Fin n)) (a : ℝ) :
    (run m N a).metricQueries ≤ n * N.length := by
  cases N with
  | nil => simp [run, Outcome.pure]
  | cons x l =>
      simpa only [run, Outcome.add, Nat.zero_add] using
        runVector_queries m (asVector (x :: l)) a

theorem run_resources (m : Sym2 (Fin n) → ℝ) (N : List (Fin n)) (a : ℝ) :
    (run m N a).retentionQueries = 0 ∧ (run m N a).positiveReplies = 0 := by
  cases N with
  | nil => exact ⟨rfl, rfl⟩
  | cons x l =>
      simpa only [run, Outcome.add, Nat.zero_add] using
        runVector_resources m (asVector (x :: l)) a

theorem run_work (m : Sym2 (Fin n) → ℝ) (N : List (Fin n)) (hN : N.Nodup) (a : ℝ) :
    (run m N a).work ≤
      128 * (n * N.length + N.length ^ 3 * (1 + Nat.log2 (N.length + 1))) := by
  cases N with
  | nil => simp [run, Outcome.pure]
  | cons x l =>
      have hi := asVector_injective (x :: l) hN
      have hw := runVector_work m (asVector (x :: l)) hi a
      have hgn : (x :: l).length ≤ n := by
        simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (asVector (x :: l)).get hi
      have hg₁ : 1 ≤ (x :: l).length := by simp
      have hn₁ : 1 ≤ n := by omega
      have hprod : (x :: l).length + 1 ≤ 2 * (n * (x :: l).length) := by nlinarith
      simp only [run, Outcome.add]
      omega

end SteinerUpperBound.SmallCoverProgram
