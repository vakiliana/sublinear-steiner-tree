module

public import SteinerUpperBound.BandEvaluation.Lists

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerUpperBound.BandEvaluation

open QueryProgram SmallCoverProgram
open scoped Classical

variable {M Q : Type*} {n m : ℕ}

abbrev Quad (m : ℕ) := (Fin m × Fin m) × (Fin m × Fin m)
def quadEquiv (m : ℕ) : Quad m ≃ Fin ((m * m) * (m * m)) :=
  (Equiv.prodCongr finProdFinEquiv finProdFinEquiv).trans finProdFinEquiv

def tupleList (C : Vector (Fin n) m) (t : Fin ((m * m) * (m * m))) : List (Fin n) :=
  let q := (quadEquiv m).symm t
  [C.get q.1.1, C.get q.1.2, C.get q.2.1, C.get q.2.2]

def tuple (C : Vector (Fin n) m) (t : Fin ((m * m) * (m * m))) :
    Code M Q (List (Fin n)) := .tick 15 (unique (tupleList C t) [])

def tupleRun (C : Vector (Fin n) m) (t : Fin ((m * m) * (m * m))) : Outcome (List (Fin n)) :=
  (uniqueRun (tupleList C t) []).add 16 0 0 0

theorem tuple_evaluates (oracle : M → ℝ) (bits : Q → Bool) (C : Vector (Fin n) m) (t) :
    Code.Evaluates oracle bits (tuple C t) (tupleRun C t) :=
  Code.Evaluates.tick _ _ _ _ (unique_evaluates _ _ _ _) 15

theorem tupleRun_set (C : Vector (Fin n) m) (t) :
    (tupleRun C t).value.toFinset = (tupleList C t).toFinset := by
  simpa only [tupleRun, Outcome.add, List.toFinset_nil, Finset.empty_union] using
    uniqueRun_set (tupleList C t) []

theorem tupleRun_nodup (C : Vector (Fin n) m) (t) : (tupleRun C t).value.Nodup := by
  simpa only [tupleRun, Outcome.add] using uniqueRun_nodup (tupleList C t) [] (by simp)

theorem tupleRun_length (C : Vector (Fin n) m) (t) : (tupleRun C t).value.length ≤ 4 := by
  have hh := uniqueRun_length (tupleList C t) []
  have hl : (tupleList C t).length = 4 := rfl
  rw [hl] at hh
  simpa only [tupleRun, Outcome.add, List.length_nil, Nat.add_zero] using hh

theorem tupleRun_subset (C : Vector (Fin n) m) (t) :
    (tupleRun C t).value.toFinset ⊆ SmallCoverProgram.retained C := by
  rw [tupleRun_set]
  intro x hx
  simp only [List.mem_toFinset, tupleList, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> exact SmallCoverProgram.retained_get C _

theorem tupleRun_work (C : Vector (Fin n) m) (t) : (tupleRun C t).work ≤ 176 := by
  have hh := uniqueRun_work (tupleList C t) []
  have hl : (tupleList C t).length = 4 := rfl
  rw [hl] at hh
  norm_num only [List.length_nil] at hh
  dsimp only [tupleRun, Outcome.add]
  omega

theorem tupleRun_resources (C : Vector (Fin n) m) (t) :
    (tupleRun C t).metricQueries = 0 ∧ (tupleRun C t).retentionQueries = 0 ∧
      (tupleRun C t).positiveReplies = 0 := by
  simpa only [tupleRun, Outcome.add, Nat.zero_add] using uniqueRun_resources (tupleList C t) []

theorem tuple_surjective (C : Vector (Fin n) m) (Y : Finset (Fin n))
    (hYC : Y ⊆ SmallCoverProgram.retained C) (h2 : 2 ≤ Y.card) (h4 : Y.card ≤ 4) :
    ∃ t, (tupleRun C t).value.toFinset = Y := by
  classical
  let e := Fintype.equivFin ↥Y
  have hk : 0 < Fintype.card ↥Y := by simpa only [Fintype.card_coe] using (show 0 < Y.card by omega)
  let f : Fin 4 → ↥Y := fun j => e.symm ⟨j.val % Fintype.card ↥Y, Nat.mod_lt _ hk⟩
  have hf : Function.Surjective f := by
    intro y
    let j : Fin 4 := ⟨(e y).val, by
      have hh := (e y).isLt
      simp only [Fintype.card_coe] at hh
      omega⟩
    refine ⟨j, ?_⟩
    apply e.injective
    change e (e.symm _) = e y
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    exact Nat.mod_eq_of_lt (e y).isLt
  have hpoint : ∀ j : Fin 4, ∃ i : Fin m, C.get i = (f j).val := by
    intro j
    exact (SmallCoverProgram.mem_retained C _).mp (hYC (f j).property)
  choose point hpoint using hpoint
  let q : Quad m := ((point 0, point 1), (point 2, point 3))
  refine ⟨quadEquiv m q, ?_⟩
  rw [tupleRun_set]
  simp only [tupleList, Equiv.symm_apply_apply]
  change [C.get (point 0), C.get (point 1), C.get (point 2), C.get (point 3)].toFinset = Y
  ext x
  constructor
  · intro hx
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rw [hpoint] <;> exact (f _).property
  · intro hx
    obtain ⟨j, hj⟩ := hf ⟨x, hx⟩
    have hv : C.get (point j) = x := (hpoint j).trans (congrArg Subtype.val hj)
    fin_cases j <;> simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] <;> aesop

end SteinerUpperBound.BandEvaluation
