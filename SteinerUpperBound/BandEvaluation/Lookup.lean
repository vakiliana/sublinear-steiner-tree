module

public import SteinerUpperBound.BandEvaluation.Tuples

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

open QueryProgram SmallCoverProgram
open scoped Classical

variable {M Q : Type*} {n m k : ℕ}

def lookup (C : Vector (Fin n) m) (d : MetricTable n m) (x y : Fin n) :
    List (Fin m) → Code M Q ℝ
  | [] => .tick 0 (.pure 0)
  | i :: l => .tick 15 (if C.get i = x then .pure (distanceAt d i y)
      else if C.get i = y then .pure (distanceAt d i x) else lookup C d x y l)

def lookupRun (C : Vector (Fin n) m) (d : MetricTable n m) (x y : Fin n) :
    List (Fin m) → Outcome ℝ
  | [] => ⟨0, 1, 0, 0, 0⟩
  | i :: l => if C.get i = x then ⟨distanceAt d i y, 16, 0, 0, 0⟩
      else if C.get i = y then ⟨distanceAt d i x, 16, 0, 0, 0⟩
      else (lookupRun C d x y l).add 16 0 0 0

theorem lookup_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (C : Vector (Fin n) m) (d : MetricTable n m) (x y : Fin n) (l) :
    Code.Evaluates oracle bits (lookup C d x y l) (lookupRun C d x y l) := by
  induction l with
  | nil => exact Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 0
  | cons i l ih =>
      unfold lookup lookupRun
      split_ifs
      · exact Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 15
      · exact Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 15
      · exact Code.Evaluates.tick _ _ _ _ ih 15

theorem lookupRun_nonneg (C : Vector (Fin n) m) (d : MetricTable n m)
    (hd : ∀ i v, 0 ≤ distanceAt d i v) (x y : Fin n) (l) :
    0 ≤ (lookupRun C d x y l).value := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih =>
      unfold lookupRun
      split_ifs
      · exact hd _ _
      · exact hd _ _
      · exact ih

theorem lookupRun_correct (I : Instance (Fin n)) (C : Vector (Fin n) m) (d : MetricTable n m)
    (hd : ∀ i v, distanceAt d i v = I.distance (C.get i) v) (x y : Fin n) (l)
    (hxy : x = y ∨ ∃ i ∈ l, C.get i = x ∨ C.get i = y) :
    (lookupRun C d x y l).value = I.distance x y := by
  induction l with
  | nil =>
      rcases hxy with rfl | ⟨i, hi, _⟩
      · exact (I.distance_self _).symm
      · simp at hi
  | cons i l ih =>
      by_cases hx : C.get i = x
      · simp only [lookupRun, hx, ↓reduceIte]
        simpa only [hx] using hd i y
      · by_cases hy : C.get i = y
        · rw [lookupRun, ite_eq_right hx, ite_eq_left hy]
          simpa only [hy, I.distance_comm] using hd i x
        · have ht : x = y ∨ ∃ j ∈ l, C.get j = x ∨ C.get j = y := by
            rcases hxy with h | ⟨j, hj, h⟩
            · exact Or.inl h
            · rcases List.mem_cons.mp hj with rfl | hj
              · exact (h.elim hx hy).elim
              · exact Or.inr ⟨j, hj, h⟩
          simpa only [lookupRun, hx, hy, ↓reduceIte, Outcome.add] using ih ht

theorem lookupRun_work (C : Vector (Fin n) m) (d : MetricTable n m) (x y : Fin n) (l) :
    (lookupRun C d x y l).work ≤ 16 * l.length + 1 := by
  induction l with
  | nil => simp [lookupRun]
  | cons i l ih =>
      unfold lookupRun
      split_ifs <;> simp only [Outcome.add, List.length_cons] <;> omega

theorem lookupRun_resources (C : Vector (Fin n) m) (d : MetricTable n m) (x y : Fin n) (l) :
    (lookupRun C d x y l).metricQueries = 0 ∧ (lookupRun C d x y l).retentionQueries = 0 ∧
      (lookupRun C d x y l).positiveReplies = 0 := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons i l ih =>
      unfold lookupRun
      split_ifs <;> simp only [Outcome.add, ih, Nat.zero_add, and_self]

def rawCell (C : Vector (Fin n) m) (d : MetricTable n m) (labels : Vector (Fin n) k)
    (p : Fin (k * k)) : Code M Q ℝ :=
  let ij := finProdFinEquiv.symm p
  .tick 7 (lookup C d (labels.get ij.1) (labels.get ij.2) (List.finRange m))

def rawCellRun (C : Vector (Fin n) m) (d : MetricTable n m) (labels : Vector (Fin n) k)
    (p : Fin (k * k)) : Outcome ℝ :=
  let ij := finProdFinEquiv.symm p
  (lookupRun C d (labels.get ij.1) (labels.get ij.2) (List.finRange m)).add 8 0 0 0

def rawMatrix (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    Code M Q (FiniteMST.Matrix L.length) :=
  let labels := asVector L
  .tick (4 * L.length + 3) ((allocate (L.length * L.length) (0 : ℝ)).bind
    (fun init => tabulate (rawCell C d labels) init))

def rawMatrixRun (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    Outcome (FiniteMST.Matrix L.length) :=
  ((allocated (L.length * L.length) (0 : ℝ)).combine
    (tabulated (rawCellRun C d (asVector L)) (Vector.replicate (L.length * L.length) 0))).add
      (4 * L.length + 4) 0 0 0

theorem rawCell_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (C : Vector (Fin n) m) (d : MetricTable n m) (labels : Vector (Fin n) k) (p) :
    Code.Evaluates oracle bits (rawCell C d labels p) (rawCellRun C d labels p) :=
  Code.Evaluates.tick _ _ _ _ (lookup_evaluates _ _ _ _ _ _ _) 7

theorem rawMatrix_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    Code.Evaluates oracle bits (rawMatrix C d L) (rawMatrixRun C d L) :=
  Code.Evaluates.tick _ _ _ _
    (Code.Evaluates.bind _ _ _ _ _ _ (allocate_evaluates _ _ _ _)
      (tabulate_evaluates _ _ _ _ (rawCell_evaluates oracle bits C d (asVector L)) _)) _

theorem rawMatrixRun_get (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n))
    (i j : Fin L.length) :
    Closure.entry (rawMatrixRun C d L).value i j =
      (lookupRun C d ((asVector L).get i) ((asVector L).get j) (List.finRange m)).value := by
  change (tabulated (rawCellRun C d (asVector L)) _).value.get (finProdFinEquiv (i, j)) = _
  rw [tabulated_get]
  simp only [rawCellRun, Equiv.symm_apply_apply, Outcome.add]

theorem rawMatrixRun_nonneg (C : Vector (Fin n) m) (d : MetricTable n m)
    (hd : ∀ i v, 0 ≤ distanceAt d i v) (L : List (Fin n)) :
    ∀ i j, 0 ≤ Closure.entry (rawMatrixRun C d L).value i j := by
  intro i j
  rw [rawMatrixRun_get]
  exact lookupRun_nonneg C d hd _ _ _

theorem rawMatrixRun_correct (I : Instance (Fin n)) (C : Vector (Fin n) m)
    (d : MetricTable n m) (hd : ∀ i v, distanceAt d i v = I.distance (C.get i) v)
    (L : List (Fin n))
    (hL : ∀ x ∈ L, ∀ y ∈ L, x = y ∨ x ∈ retained C ∨ y ∈ retained C) :
    ∀ i j, Closure.entry (rawMatrixRun C d L).value i j =
      I.weight (Sym2.mk ((asVector L).get i) ((asVector L).get j)) := by
  intro i j
  rw [rawMatrixRun_get, Instance.weight_mk]
  apply lookupRun_correct I C d hd
  have hi : (asVector L).get i ∈ L := by rw [asVector_get]; exact L.get_mem i
  have hj : (asVector L).get j ∈ L := by rw [asVector_get]; exact L.get_mem j
  rcases hL _ hi _ hj with he | h | h
  · exact Or.inl he
  · obtain ⟨k, hk⟩ := (mem_retained C _).mp h
    exact Or.inr ⟨k, List.mem_finRange k, Or.inl hk⟩
  · obtain ⟨k, hk⟩ := (mem_retained C _).mp h
    exact Or.inr ⟨k, List.mem_finRange k, Or.inr hk⟩

theorem rawMatrixRun_work (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    (rawMatrixRun C d L).work ≤ (16 * m + 12) * L.length ^ 2 + 4 * L.length + 5 := by
  have hc (p) : (rawCellRun C d (asVector L) p).work ≤ 16 * m + 9 := by
    have hh := lookupRun_work C d
      ((asVector L).get (finProdFinEquiv.symm p).1)
      ((asVector L).get (finProdFinEquiv.symm p).2) (List.finRange m)
    simp only [List.length_finRange] at hh
    dsimp only [rawCellRun, Outcome.add]
    omega
  have hh := tabulated_work (rawCellRun C d (asVector L)) (Vector.replicate (L.length * L.length) 0)
    (16 * m + 9) hc
  dsimp only [rawMatrixRun, allocated, Outcome.add, Outcome.combine]
  nlinarith

theorem rawMatrixRun_resources (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    (rawMatrixRun C d L).metricQueries = 0 ∧ (rawMatrixRun C d L).retentionQueries = 0 ∧
      (rawMatrixRun C d L).positiveReplies = 0 := by
  have hc (p) : (rawCellRun C d (asVector L) p).metricQueries = 0 ∧
      (rawCellRun C d (asVector L) p).retentionQueries = 0 ∧
      (rawCellRun C d (asVector L) p).positiveReplies = 0 := by
    simpa only [rawCellRun, Outcome.add, Nat.zero_add] using
      lookupRun_resources C d _ _ (List.finRange m)
  have hm := tabulated_metricQueries (rawCellRun C d (asVector L)) (Vector.replicate (L.length * L.length) 0) 0
    (fun p => (hc p).1.le)
  have hr := tabulated_retention_zero (rawCellRun C d (asVector L)) (Vector.replicate (L.length * L.length) 0)
    (fun p => (hc p).2.1)
  have hp := tabulated_positive_zero (rawCellRun C d (asVector L)) (Vector.replicate (L.length * L.length) 0)
    (fun p => (hc p).2.2)
  dsimp only [rawMatrixRun, allocated, Outcome.add, Outcome.combine]
  simp only [Nat.zero_add]
  exact ⟨by simpa only [Nat.zero_mul, Nat.le_zero] using hm, hr, hp⟩

end SteinerUpperBound.BandEvaluation
