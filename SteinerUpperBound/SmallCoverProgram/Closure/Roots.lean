module

public import SteinerUpperBound.SmallCoverProgram.Closure.Program

@[expose] public section

namespace SteinerUpperBound.SmallCoverProgram.Closure

open QueryProgram
open scoped Classical

variable {M Q : Type*} {g : ℕ}

def rootStep (a : Dense Bool g) (x best y : Fin g) : Fin g :=
  if entry a x y then min best y else best

def rootValue (a : Dense Bool g) (x : Fin g) : Fin g :=
  (List.finRange g).foldl (rootStep a x) x

theorem rootStep_le (a : Dense Bool g) (x best y : Fin g) : rootStep a x best y ≤ best := by
  unfold rootStep
  split_ifs
  · exact min_le_left _ _
  · rfl

theorem rootFold_le (a : Dense Bool g) (x : Fin g) (l : List (Fin g)) (best : Fin g) :
    l.foldl (rootStep a x) best ≤ best := by
  induction l generalizing best with
  | nil => rfl
  | cons y l ih => exact (ih _).trans (rootStep_le a x best y)

theorem rootFold_member (a : Dense Bool g) (x : Fin g) (l : List (Fin g))
    (best y : Fin g) (hy : y ∈ l) (hxy : entry a x y = true) :
    l.foldl (rootStep a x) best ≤ y := by
  induction l generalizing best with
  | nil => simp at hy
  | cons z l ih =>
      rcases List.mem_cons.mp hy with rfl | hy
      · exact (rootFold_le a x l _).trans (by simp [rootStep, hxy])
      · exact ih _ hy

theorem rootFold_valid (a : Dense Bool g) (x : Fin g) (l : List (Fin g))
    (best : Fin g) (hb : entry a x best = true) :
    entry a x (l.foldl (rootStep a x) best) = true := by
  induction l generalizing best with
  | nil => exact hb
  | cons y l ih =>
      apply ih
      by_cases hy : entry a x y = true
      · by_cases hby : best ≤ y
        · simpa only [rootStep, hy, ↓reduceIte, min_eq_left hby] using hb
        · simp only [rootStep, hy, ↓reduceIte, min_eq_right (le_of_not_ge hby)]
      · simpa only [rootStep, hy, Bool.false_eq_true, ↓reduceIte] using hb

theorem root_reachable (a : Dense Bool g) (G : SimpleGraph (Fin g))
    (hclosure : ∀ x y, entry a x y = true ↔ G.Reachable x y) (x : Fin g) :
    G.Reachable x (rootValue a x) :=
  (hclosure x _).mp (rootFold_valid a x _ x ((hclosure x x).mpr (.refl x)))

theorem root_min (a : Dense Bool g) (G : SimpleGraph (Fin g))
    (hclosure : ∀ x y, entry a x y = true ↔ G.Reachable x y)
    {x y : Fin g} (hxy : G.Reachable x y) : rootValue a x ≤ y :=
  rootFold_member a x _ x y (List.mem_finRange y) ((hclosure x y).mpr hxy)

theorem root_eq_of_reachable (a : Dense Bool g) (G : SimpleGraph (Fin g))
    (hclosure : ∀ x y, entry a x y = true ↔ G.Reachable x y)
    {x y : Fin g} (hxy : G.Reachable x y) : rootValue a x = rootValue a y := by
  apply le_antisymm
  · exact root_min a G hclosure (hxy.trans (root_reachable a G hclosure y))
  · exact root_min a G hclosure (hxy.symm.trans (root_reachable a G hclosure x))

theorem root_eq_iff (a : Dense Bool g) (G : SimpleGraph (Fin g))
    (hclosure : ∀ x y, entry a x y = true ↔ G.Reachable x y) (x y : Fin g) :
    rootValue a x = rootValue a y ↔ G.Reachable x y := by
  refine ⟨?_, root_eq_of_reachable a G hclosure⟩
  intro he
  have hx := root_reachable a G hclosure x
  have hy := root_reachable a G hclosure y
  rw [he] at hx
  exact hx.trans hy.symm

theorem root_idempotent (a : Dense Bool g) (G : SimpleGraph (Fin g))
    (hclosure : ∀ x y, entry a x y = true ↔ G.Reachable x y) (x : Fin g) :
    rootValue a (rootValue a x) = rootValue a x :=
  (root_eq_of_reachable a G hclosure (root_reachable a G hclosure x)).symm

def rootCode (a : Dense Bool g) (x : Fin g) : Code M Q (Fin g) :=
  Code.foldList (fun best y => .tick 5 (.pure (rootStep a x best y))) (List.finRange g) x

def rootRun (a : Dense Bool g) (x : Fin g) : Outcome (Fin g) :=
  Code.folded (fun best y => ⟨rootStep a x best y, 6, 0, 0, 0⟩) (List.finRange g) x

def rootBody (a : Dense Bool g) (x : Fin g) : Code M Q ℕ :=
  .tick 0 ((rootCode a x).map Fin.val)

def rootBodyRun (a : Dense Bool g) (x : Fin g) : Outcome ℕ :=
  ((rootRun a x).map Fin.val).add 1 0 0 0

def roots (a : Dense Bool g) : Code M Q (Vector ℕ g) :=
  (allocate g 0).bind (fun init => tabulate (rootBody a) init)

def rootsRun (a : Dense Bool g) : Outcome (Vector ℕ g) :=
  (allocated g 0).combine (tabulated (rootBodyRun a) (Vector.replicate g 0))

theorem root_evaluates (m : M → ℝ) (b : Q → Bool) (a : Dense Bool g) (x : Fin g) :
    Code.Evaluates m b (rootCode a x) (rootRun a x) := by
  apply Code.foldList_evaluates
  intro best y
  exact Code.Evaluates.tick m b _ _ (Code.evaluates_pure m b _) 5

theorem rootBody_evaluates (m : M → ℝ) (b : Q → Bool) (a : Dense Bool g) (x : Fin g) :
    Code.Evaluates m b (rootBody a x) (rootBodyRun a x) := by
  apply Code.Evaluates.tick
  intro F
  rw [Code.evaluate_map, root_evaluates m b a x]

theorem roots_evaluates (m : M → ℝ) (b : Q → Bool) (a : Dense Bool g) :
    Code.Evaluates m b (roots a) (rootsRun a) :=
  Code.Evaluates.bind m b _ _ _ _ (allocate_evaluates m b _ _)
    (tabulate_evaluates m b _ _ (rootBody_evaluates m b a) _)

theorem rootRun_value (a : Dense Bool g) (x : Fin g) : (rootRun a x).value = rootValue a x := by
  rw [rootRun, folded_value]
  rfl

theorem rootsRun_get (a : Dense Bool g) (x : Fin g) :
    (rootsRun a).value.get x = (rootValue a x).val := by
  change (tabulated (rootBodyRun a) _).value.get x = _
  rw [tabulated_get]
  exact congrArg Fin.val (rootRun_value a x)

theorem computed_roots_partition (a : Dense Bool g) (G : SimpleGraph (Fin g))
    (hAdj : ∀ x y, entry a x y = true ↔ G.Adj x y) (x y : Fin g) :
    (rootsRun (computed a).value).value.get x = (rootsRun (computed a).value).value.get y ↔
      G.Reachable x y := by
  rw [rootsRun_get, rootsRun_get]
  exact (Fin.ext_iff).symm.trans (root_eq_iff _ G (computed_correct a hAdj) x y)

theorem computed_roots_bound (a : Dense Bool g) (x : Fin g) :
    (rootsRun (computed a).value).value.get x < g := by
  rw [rootsRun_get]
  exact (rootValue (computed a).value x).isLt

theorem computed_roots_min (a : Dense Bool g) (G : SimpleGraph (Fin g))
    (hAdj : ∀ x y, entry a x y = true ↔ G.Adj x y) {x y : Fin g} (hxy : G.Reachable x y) :
    (rootsRun (computed a).value).value.get x ≤ y.val := by
  rw [rootsRun_get]
  exact root_min _ G (computed_correct a hAdj) hxy

theorem rootRun_work (a : Dense Bool g) (x : Fin g) : (rootRun a x).work ≤ 7 * g := by
  have hh := Code.folded_work (fun best y => (⟨rootStep a x best y, 6, 0, 0, 0⟩ : Outcome (Fin g)))
    6 (fun _ _ => le_rfl) (List.finRange g) x
  simpa [rootRun] using hh

theorem rootsRun_work (a : Dense Bool g) : (rootsRun a).work ≤ 7 * g ^ 2 + 4 * g + 1 := by
  have hb (x : Fin g) : (rootBodyRun a x).work ≤ 7 * g + 1 := by
    have hh := rootRun_work a x
    dsimp only [rootBodyRun, Outcome.map, Outcome.add]
    omega
  have ht := tabulated_work (rootBodyRun a) (Vector.replicate g 0) (7 * g + 1) hb
  dsimp only [rootsRun, allocated, Outcome.combine]
  nlinarith

theorem rootRun_resources (a : Dense Bool g) (x : Fin g) :
    (rootRun a x).metricQueries = 0 ∧ (rootRun a x).retentionQueries = 0 ∧
      (rootRun a x).positiveReplies = 0 := by
  have hm := Code.folded_metric_queries
    (fun best y => (⟨rootStep a x best y, 6, 0, 0, 0⟩ : Outcome (Fin g)))
    0 (fun _ _ => le_rfl) (List.finRange g) x
  have hr := folded_retention_zero
    (fun best y => (⟨rootStep a x best y, 6, 0, 0, 0⟩ : Outcome (Fin g)))
    (fun _ _ => rfl) (List.finRange g) x
  have hp := folded_positive_zero
    (fun best y => (⟨rootStep a x best y, 6, 0, 0, 0⟩ : Outcome (Fin g)))
    (fun _ _ => rfl) (List.finRange g) x
  simpa only [rootRun] using
    (And.intro (by simpa only [Nat.zero_mul, Nat.le_zero] using hm) (And.intro hr hp))

theorem rootsRun_resources (a : Dense Bool g) :
    (rootsRun a).metricQueries = 0 ∧ (rootsRun a).retentionQueries = 0 ∧
      (rootsRun a).positiveReplies = 0 := by
  have hb (x : Fin g) : (rootBodyRun a x).metricQueries = 0 ∧
      (rootBodyRun a x).retentionQueries = 0 ∧ (rootBodyRun a x).positiveReplies = 0 := by
    simpa only [rootBodyRun, Outcome.map, Outcome.add, Nat.zero_add] using rootRun_resources a x
  have hm := tabulated_metricQueries (rootBodyRun a) (Vector.replicate g 0) 0 (fun x => (hb x).1.le)
  have hr := tabulated_retention_zero (rootBodyRun a) (Vector.replicate g 0) (fun x => (hb x).2.1)
  have hp := tabulated_positive_zero (rootBodyRun a) (Vector.replicate g 0) (fun x => (hb x).2.2)
  dsimp only [rootsRun, allocated, Outcome.combine]
  simp only [Nat.zero_add]
  exact ⟨by simpa only [Nat.zero_mul, Nat.le_zero] using hm, hr, hp⟩

end SteinerUpperBound.SmallCoverProgram.Closure
