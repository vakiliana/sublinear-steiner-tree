module

public import SteinerUpperBound.LocalAccess.Covered
public import SteinerUpperBound.ComponentExplore

@[expose] public section

namespace SteinerUpperBound.LocalAccess

open QueryProgram
open scoped Classical

variable {V Q : Type*}

theorem canonical_length (wanted order : List V) (hn : order.Nodup)
    (h : wanted.toFinset ⊆ order.toFinset) :
    (canonicalResult wanted order).value.length ≤ wanted.length := by
  have hnd := canonical_nodup wanted order hn
  have hs := canonical_set wanted order h
  calc
    _ = (canonicalResult wanted order).value.toFinset.card :=
      (List.toFinset_card_of_nodup hnd).symm
    _ = wanted.toFinset.card := congrArg Finset.card hs
    _ ≤ _ := List.toFinset_card_le _

structure Frame (V : Type*) (b B : ℕ) where
  points : List V
  pointSlots : Vector (Option V) B
  rows : Prepared V b

noncomputable def frameProgram (r : ℝ) (b B : ℕ) (vertices terminals points : List V) :
    Code (Sym2 V) Q (Frame V b B) :=
  (canonicalProgram points terminals).bind (fun C =>
    (packProgram B C).bind (fun pointSlots =>
      (prepareProgram r C b vertices).bind (fun rows =>
        .tick 2 (.pure ⟨C, pointSlots, rows⟩))))

noncomputable def frameResult (w : Sym2 V → ℝ) (r : ℝ) (b B : ℕ)
    (vertices terminals points : List V) : Outcome (Frame V b B) :=
  let C := canonicalResult points terminals
  let p := packResult B C.value
  let rows := prepareResult w r C.value b vertices
  C.combine (p.combine (rows.combine ((Outcome.pure ⟨C.value, p.value, rows.value⟩).add 3 0 0 0)))

theorem frame_evaluates (w : Sym2 V → ℝ) (bits : Q → Bool) (r : ℝ) (b B : ℕ)
    (vertices terminals points : List V) :
    Code.Evaluates w bits (frameProgram r b B vertices terminals points)
      (frameResult w r b B vertices terminals points) :=
  Code.Evaluates.bind w bits _ _ _ _ (canonical_evaluates w bits points terminals)
    (Code.Evaluates.bind w bits _ _ _ _ (pack_evaluates w bits B _)
      (Code.Evaluates.bind w bits _ _ _ _ (prepare_evaluates w bits r _ b vertices)
        (Code.Evaluates.tick w bits _ _ (Code.evaluates_pure w bits _) 2)))

theorem frame_points (w : Sym2 V → ℝ) (r : ℝ) (b B : ℕ)
    (vertices terminals points : List V) :
    (frameResult w r b B vertices terminals points).value.points =
      terminals.filter (fun x => decide (x ∈ points)) := by
  simp only [frameResult, Outcome.combine, Outcome.add, Outcome.pure, canonical_value]

theorem frame_pointSlot (w : Sym2 V → ℝ) (r : ℝ) (b B : ℕ)
    (vertices terminals points : List V) (i : Fin B) :
    (frameResult w r b B vertices terminals points).value.pointSlots.get i =
      (terminals.filter (fun x => decide (x ∈ points)))[i.val]? := by
  simp only [frameResult, Outcome.combine, Outcome.add, Outcome.pure, pack_get, canonical_value]

theorem frame_rows (w : Sym2 V → ℝ) (r : ℝ) (b B : ℕ)
    (vertices terminals points : List V) :
    (frameResult w r b B vertices terminals points).value.rows.centers =
      (vertices.filter (fun v =>
        (nearResult w r v (canonicalResult points terminals).value).value)).take b := by
  simp only [frameResult, Outcome.combine, Outcome.add, Outcome.pure, prepareResult, centers_value]

theorem frame_rowSlot (w : Sym2 V → ℝ) (r : ℝ) (b B : ℕ)
    (vertices terminals points : List V) (i : Fin b) :
    (frameResult w r b B vertices terminals points).value.rows.slots.get i =
      ((vertices.filter (fun v =>
        (nearResult w r v (canonicalResult points terminals).value).value)).take b)[i.val]? := by
  simp only [frameResult, Outcome.combine, Outcome.add, Outcome.pure, prepare_get]

def frameBudget (n k b B : ℕ) : ℕ :=
  (2 * B + 5) * (n + k + 2) + B * (B + 4) + b * (b + 4) + 6

theorem frame_work (w : Sym2 V → ℝ) (r : ℝ) (b B : ℕ)
    (vertices terminals points : List V) (hn : terminals.Nodup)
    (hs : points.toFinset ⊆ terminals.toFinset) (hB : points.length ≤ B) :
    (frameResult w r b B vertices terminals points).work ≤
      frameBudget vertices.length terminals.length b B := by
  have hc := canonical_work points terminals
  have hl := canonical_length points terminals hn hs
  have hp := pack_work B (canonicalResult points terminals).value
  have hr := prepare_work w r (canonicalResult points terminals).value b vertices
  have hm₀ := Nat.mul_le_mul_right (terminals.length + 1)
    (show 2 * points.length + 5 ≤ 2 * B + 5 by omega)
  have hm₁ := Nat.mul_le_mul_left B
    (show (canonicalResult points terminals).value.length + 4 ≤ B + 4 by omega)
  have hm₂ := Nat.mul_le_mul_right (vertices.length + 1)
    (show 2 * (canonicalResult points terminals).value.length + 5 ≤ 2 * B + 5 by omega)
  simp only [frameResult, Outcome.combine, Outcome.add, Outcome.pure, frameBudget]
  nlinarith

theorem frame_metric_queries (w : Sym2 V → ℝ) (r : ℝ) (b B : ℕ)
    (vertices terminals points : List V) (hn : terminals.Nodup)
    (hs : points.toFinset ⊆ terminals.toFinset) (hB : points.length ≤ B) :
    (frameResult w r b B vertices terminals points).metricQueries ≤ vertices.length * B := by
  have hc := (canonical_counters points terminals).1
  have hp := (pack_counters B (canonicalResult points terminals).value).1
  have hP := (pack_counters b (centersResult w r
    (canonicalResult points terminals).value b vertices).value).1
  have hr := centers_queries w r (canonicalResult points terminals).value b vertices
  have hl := canonical_length points terminals hn hs
  have hm := Nat.mul_le_mul_left vertices.length (show
    (canonicalResult points terminals).value.length ≤ B by omega)
  simp only [frameResult, prepareResult, Outcome.combine, Outcome.add, Outcome.pure,
    hc, hp, hP, Nat.zero_add, Nat.add_zero]
  omega

theorem frame_counters (w : Sym2 V → ℝ) (r : ℝ) (b B : ℕ)
    (vertices terminals points : List V) :
    (frameResult w r b B vertices terminals points).retentionQueries = 0 ∧
      (frameResult w r b B vertices terminals points).positiveReplies = 0 := by
  have hc := (canonical_counters points terminals).2
  have hp := (pack_counters B (canonicalResult points terminals).value).2
  have hr := centers_counters w r (canonicalResult points terminals).value b vertices
  have hs := (pack_counters b (centersResult w r
    (canonicalResult points terminals).value b vertices).value).2
  simp only [frameResult, prepareResult, Outcome.combine, Outcome.add, Outcome.pure,
    hc.1, hc.2, hp.1, hp.2, hr.1, hr.2, hs.1, hs.2, Nat.zero_add, true_and]

structure Located (V Q : Type*) (b B : ℕ) where
  frame : Option (Frame V b B)
  cache : Cache Q

noncomputable def locateProgram [Fintype V] (key : V → Q) (a : ℝ) (b B : ℕ)
    (vertices terminals : List V) (root : V) (c : Cache Q) :
    Code (Sym2 V) Q (Located V Q b B) :=
  (ComponentExplore.program key a B terminals root c).bind (fun explored =>
    .tick 0 (if explored.complete then
      (frameProgram (5 * a / 8) b B vertices terminals explored.memory.points).bind (fun f =>
        .tick 0 (.pure ⟨some f, explored.memory.cache⟩))
    else .pure ⟨none, explored.memory.cache⟩))

noncomputable def locateResult [Fintype V] (w : Sym2 V → ℝ) (bits : Q → Bool)
    (key : V → Q) (a : ℝ) (b B : ℕ) (vertices terminals : List V) (root : V) (c : Cache Q) :
    Outcome (Located V Q b B) :=
  let e := ComponentExplore.result w bits key a B terminals root c
  let tail : Outcome (Located V Q b B) :=
    if e.value.complete then
      let f := frameResult w (5 * a / 8) b B vertices terminals e.value.memory.points
      f.combine ((Outcome.pure ⟨some f.value, e.value.memory.cache⟩).add 1 0 0 0)
    else Outcome.pure ⟨none, e.value.memory.cache⟩
  e.combine (tail.add 1 0 0 0)

theorem locate_evaluates [Fintype V] (w : Sym2 V → ℝ) (bits : Q → Bool)
    (key : V → Q) (a : ℝ) (b B : ℕ) (vertices terminals : List V) (root : V) (c : Cache Q) :
    Code.Evaluates w bits (locateProgram key a b B vertices terminals root c)
      (locateResult w bits key a b B vertices terminals root c) := by
  intro F
  simp only [locateProgram, locateResult, Code.evaluate_bind]
  rw [ComponentExplore.program_evaluates w bits key a B terminals root c]
  cases he : (ComponentExplore.result w bits key a B terminals root c).value.complete <;>
    simp only [Code.evaluate, Bool.false_eq_true, ite_false, ite_true] <;>
    rw [Code.evaluate_bind, frame_evaluates w bits (5 * a / 8) b B vertices terminals _] <;> rfl

end SteinerUpperBound.LocalAccess
