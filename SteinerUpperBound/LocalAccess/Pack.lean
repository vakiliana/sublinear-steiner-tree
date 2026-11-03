module

public import SteinerUpperBound.LocalAccess.Third
public import SteinerUpperBound.SmallCoverProgram.Ram

@[expose] public section

namespace SteinerUpperBound.LocalAccess

open QueryProgram
open scoped Classical

variable {V M Q : Type*}

noncomputable def nthProgram : List V → ℕ → Code M Q (Option V)
  | [], _ => .tick 0 (.pure none)
  | x :: _, 0 => .tick 0 (.pure (some x))
  | _ :: l, i + 1 => .tick 0 (nthProgram l i)

def nthResult : List V → ℕ → Outcome (Option V)
  | [], _ => (Outcome.pure none).add 1 0 0 0
  | x :: _, 0 => (Outcome.pure (some x)).add 1 0 0 0
  | _ :: l, i + 1 => (nthResult l i).add 1 0 0 0

theorem nth_evaluates (m : M → ℝ) (b : Q → Bool) (l : List V) (i : ℕ) :
    Code.Evaluates m b (nthProgram l i) (nthResult l i) := by
  induction l generalizing i with
  | nil => intro F; rfl
  | cons x l ih =>
      cases i with
      | zero => intro F; rfl
      | succ i =>
          intro F
          exact ih i (fun o => F (o.add 1 0 0 0))

theorem nth_value (l : List V) (i : ℕ) : (nthResult l i).value = l[i]? := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih => cases i <;> simp [nthResult, Outcome.add, Outcome.pure, ih]

theorem nth_work (l : List V) (i : ℕ) : (nthResult l i).work ≤ l.length + 1 := by
  induction l generalizing i with
  | nil => exact le_rfl
  | cons x l ih =>
      cases i with
      | zero => simp [nthResult, Outcome.add, Outcome.pure]
      | succ i =>
          have h := ih i
          simp only [nthResult, Outcome.add, List.length_cons]
          omega

theorem nth_counters (l : List V) (i : ℕ) :
    (nthResult l i).metricQueries = 0 ∧ (nthResult l i).retentionQueries = 0 ∧
      (nthResult l i).positiveReplies = 0 := by
  induction l generalizing i with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons x l ih =>
      cases i with
      | zero => exact ⟨rfl, rfl, rfl⟩
      | succ i => simpa only [nthResult, Outcome.add, Nat.zero_add] using ih i

noncomputable def packProgram (capacity : ℕ) (l : List V) : Code M Q (Vector (Option V) capacity) :=
  (SmallCoverProgram.allocate capacity none).bind (fun init =>
    SmallCoverProgram.tabulate (fun i => nthProgram l i.val) init)

def packResult (capacity : ℕ) (l : List V) : Outcome (Vector (Option V) capacity) :=
  (SmallCoverProgram.allocated capacity (none : Option V)).combine
    (SmallCoverProgram.tabulated (fun i => nthResult l i.val) (Vector.replicate capacity none))

theorem pack_evaluates (m : M → ℝ) (b : Q → Bool) (capacity : ℕ) (l : List V) :
    Code.Evaluates m b (packProgram capacity l) (packResult capacity l) :=
  Code.Evaluates.bind m b _ _ _ _ (SmallCoverProgram.allocate_evaluates m b _ _)
    (SmallCoverProgram.tabulate_evaluates m b _ _ (fun i => nth_evaluates m b l i.val) _)

theorem pack_get (capacity : ℕ) (l : List V) (i : Fin capacity) :
    (packResult capacity l).value.get i = l[i.val]? := by
  change (SmallCoverProgram.tabulated _ _).value.get i = _
  rw [SmallCoverProgram.tabulated_get, nth_value]

theorem pack_work (capacity : ℕ) (l : List V) :
    (packResult capacity l).work ≤ capacity * (l.length + 4) + 1 := by
  have h := SmallCoverProgram.tabulated_work (fun i : Fin capacity => nthResult l i.val)
    (Vector.replicate capacity none) (l.length + 1) (fun i => nth_work l i.val)
  dsimp only [packResult, SmallCoverProgram.allocated, Outcome.combine]
  nlinarith

theorem pack_counters (capacity : ℕ) (l : List V) :
    (packResult capacity l).metricQueries = 0 ∧
      (packResult capacity l).retentionQueries = 0 ∧
      (packResult capacity l).positiveReplies = 0 := by
  have hm := SmallCoverProgram.tabulated_metricQueries (fun i : Fin capacity => nthResult l i.val)
    (Vector.replicate capacity none) 0 (fun i => by rw [(nth_counters l i.val).1])
  have hr := SmallCoverProgram.tabulated_retention_zero (fun i : Fin capacity => nthResult l i.val)
    (Vector.replicate capacity none) (fun i => (nth_counters l i.val).2.1)
  have hp := SmallCoverProgram.tabulated_positive_zero (fun i : Fin capacity => nthResult l i.val)
    (Vector.replicate capacity none) (fun i => (nth_counters l i.val).2.2)
  simp only [Nat.zero_mul] at hm
  dsimp only [packResult, Outcome.combine, SmallCoverProgram.allocated]
  exact ⟨by omega, by simpa using hr, by simpa using hp⟩

structure Prepared (V : Type*) (capacity : ℕ) where
  centers : List V
  slots : Vector (Option V) capacity

noncomputable def prepareProgram (r : ℝ) (points : List V) (capacity : ℕ) (vertices : List V) :
    Code (Sym2 V) Q (Prepared V capacity) :=
  (centersProgram r points capacity vertices).bind (fun centers =>
    (packProgram capacity centers).bind (fun slots => .tick 0 (.pure ⟨centers, slots⟩)))

noncomputable def prepareResult (w : Sym2 V → ℝ) (r : ℝ) (points : List V)
    (capacity : ℕ) (vertices : List V) : Outcome (Prepared V capacity) :=
  let c := centersResult w r points capacity vertices
  let p := packResult capacity c.value
  c.combine (p.combine ((Outcome.pure ⟨c.value, p.value⟩).add 1 0 0 0))

theorem prepare_evaluates (w : Sym2 V → ℝ) (b : Q → Bool) (r : ℝ) (points : List V)
    (capacity : ℕ) (vertices : List V) :
    Code.Evaluates w b (prepareProgram r points capacity vertices)
      (prepareResult w r points capacity vertices) :=
  Code.Evaluates.bind w b _ _ _ _ (centers_evaluates w b r points capacity vertices)
    (Code.Evaluates.bind w b _ _ _ _ (pack_evaluates w b capacity _)
      (Code.Evaluates.tick w b _ _ (Code.evaluates_pure w b _) 0))

theorem prepare_get (w : Sym2 V → ℝ) (r : ℝ) (points : List V)
    (capacity : ℕ) (vertices : List V) (i : Fin capacity) :
    (prepareResult w r points capacity vertices).value.slots.get i =
      ((vertices.filter (fun v => (nearResult w r v points).value)).take capacity)[i.val]? := by
  simp only [prepareResult, Outcome.combine, Outcome.add, Outcome.pure, pack_get, centers_value]

theorem prepare_work (w : Sym2 V → ℝ) (r : ℝ) (points : List V)
    (capacity : ℕ) (vertices : List V) :
    (prepareResult w r points capacity vertices).work ≤
      (2 * points.length + 5) * (vertices.length + 1) + capacity * (capacity + 4) + 2 := by
  have hc := centers_work w r points capacity vertices
  have hp := pack_work capacity (centersResult w r points capacity vertices).value
  have hl := centers_length w r points capacity vertices
  have hm := Nat.mul_le_mul_left capacity (Nat.add_le_add_right hl 4)
  simp only [prepareResult, Outcome.combine, Outcome.add, Outcome.pure]
  nlinarith

end SteinerUpperBound.LocalAccess
