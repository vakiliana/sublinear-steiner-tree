module

public import SteinerUpperBound.SmallCoverProgram.Ram

@[expose] public section

namespace SteinerUpperBound.PublicTerminals

open QueryProgram
open scoped Classical

variable {M Q : Type*} {n k : ℕ}

theorem toList_toFinset {V : Type*} [DecidableEq V] {length : ℕ} (label : Vector V length) :
    label.toList.toFinset = Finset.univ.image label.get := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    obtain ⟨i, hi, hx⟩ := List.mem_iff_getElem.mp hx
    have hi' : i < length := by simpa only [Vector.length_toList] using hi
    refine ⟨⟨i, hi'⟩, ?_⟩
    simpa [Vector.get] using hx
  · rintro ⟨i, rfl⟩
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val, by simpa only [Vector.length_toList] using i.isLt, ?_⟩
    simp [Vector.get]

theorem toList_nodup {V : Type*} {length : ℕ} (label : Vector V length)
    (hinj : Function.Injective label.get) : label.toList.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j hij
  have hi : i.val < length := by simpa only [Vector.length_toList] using i.isLt
  have hj : j.val < length := by simpa only [Vector.length_toList] using j.isLt
  change label.toList[i.val] = label.toList[j.val] at hij
  rw [Vector.getElem_toList, Vector.getElem_toList] at hij
  have he : label.get ⟨i.val, hi⟩ = label.get ⟨j.val, hj⟩ := by
    simpa [Vector.get] using hij
  exact Fin.ext (congrArg (fun z : Fin length => z.val) (hinj he))

theorem length_le {length : ℕ} (label : Vector (Fin n) length)
    (hinj : Function.Injective label.get) : length ≤ n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective label.get hinj

def inverseStep (label : Vector (Fin n) (k + 1)) (v : Vector (Fin (k + 1)) n)
    (i : Fin (k + 1)) : Code M Q (Vector (Fin (k + 1)) n) :=
  .tick 2 (.pure (SmallCoverProgram.put v (label.get i) i))

def inverseStepResult (label : Vector (Fin n) (k + 1)) (v : Vector (Fin (k + 1)) n)
    (i : Fin (k + 1)) : Outcome (Vector (Fin (k + 1)) n) :=
  ⟨SmallCoverProgram.put v (label.get i) i, 3, 0, 0, 0⟩

def inverseProgram (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) :
    Code M Q (Vector (Fin (k + 1)) n) :=
  (SmallCoverProgram.allocate n root).bind (fun init =>
    Code.foldList (inverseStep label) (List.finRange (k + 1)) init)

def inverseResult (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) :
    Outcome (Vector (Fin (k + 1)) n) :=
  (SmallCoverProgram.allocated n root).combine
    (Code.folded (inverseStepResult label) (List.finRange (k + 1))
      (Vector.replicate n root))

theorem inverse_evaluates (m : M → ℝ) (bits : Q → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) :
    Code.Evaluates m bits (inverseProgram label root) (inverseResult label root) :=
  Code.Evaluates.bind m bits _ _ _ _ (SmallCoverProgram.allocate_evaluates m bits _ _)
    (Code.foldList_evaluates m bits _ _ (fun _ _ _ => rfl) _ _)

theorem inverse_get_fold (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get)
    (l : List (Fin (k + 1))) (v : Vector (Fin (k + 1)) n) (j : Fin (k + 1)) :
    (l.foldl (fun a i => SmallCoverProgram.put a (label.get i) i) v).get (label.get j) =
      if j ∈ l then j else v.get (label.get j) := by
  induction l generalizing v with
  | nil => simp
  | cons i l ih =>
      rw [List.foldl_cons, ih, SmallCoverProgram.get_put]
      have he : label.get i = label.get j ↔ i = j :=
        ⟨fun h => hinj h, fun h => congrArg label.get h⟩
      simp only [he]
      by_cases hj : j ∈ l
      · simp [hj]
      · by_cases hij : i = j
        · subst j
          simp [hj]
        · simp [hj, hij, Ne.symm hij]

theorem inverse_left (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get)
    (root : Fin (k + 1)) (j : Fin (k + 1)) :
    (inverseResult label root).value.get (label.get j) = j := by
  change (Code.folded (inverseStepResult label) (List.finRange (k + 1))
    (Vector.replicate n root)).value.get (label.get j) = _
  rw [SmallCoverProgram.folded_value]
  change ((List.finRange (k + 1)).foldl
    (fun a i => SmallCoverProgram.put a (label.get i) i) _).get (label.get j) = _
  rw [inverse_get_fold label hinj]
  simp

theorem inverse_work (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) :
    (inverseResult label root).work ≤ n + 4 * (k + 1) + 1 := by
  have h := Code.folded_work (inverseStepResult label) 3 (fun _ _ => le_rfl)
    (List.finRange (k + 1)) (Vector.replicate n root)
  simp only [List.length_finRange] at h
  dsimp only [inverseResult, SmallCoverProgram.allocated, Outcome.combine]
  omega

theorem inverse_counters (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) :
    (inverseResult label root).metricQueries = 0 ∧
      (inverseResult label root).retentionQueries = 0 ∧
      (inverseResult label root).positiveReplies = 0 := by
  have hm := Code.folded_metric_queries (inverseStepResult label) 0 (fun _ _ => by exact le_rfl)
    (List.finRange (k + 1)) (Vector.replicate n root)
  have hr := SmallCoverProgram.folded_retention_zero (inverseStepResult label) (fun _ _ => rfl)
    (List.finRange (k + 1)) (Vector.replicate n root)
  have hp := SmallCoverProgram.folded_positive_zero (inverseStepResult label) (fun _ _ => rfl)
    (List.finRange (k + 1)) (Vector.replicate n root)
  simp only [Nat.zero_mul] at hm
  dsimp only [inverseResult, Outcome.combine, SmallCoverProgram.allocated]
  exact ⟨by omega, by simpa using hr, by simpa using hp⟩

end SteinerUpperBound.PublicTerminals
