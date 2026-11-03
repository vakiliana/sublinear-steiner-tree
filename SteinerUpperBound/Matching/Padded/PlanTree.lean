module

public import SteinerUpperBound.Matching.Padded.Plan

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Plan

open SteinerLowerBound
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} {S : Slots G} {Q : ℕ}

def tree : List (Item S) → List (Entry S Q) →
    SteinerLowerBound.DecisionTree E (Option (Fin Q)) (List (Entry S Q))
  | [], entries => .leaf entries
  | x :: xs, entries =>
    .query x.edge (fun obs => tree xs (match obs with
      | none => entries
      | some r => x.entry r :: entries))

def observations (xs : List (Item S)) (obs : E → Option (Fin Q)) : List (Entry S Q) :=
  xs.filterMap fun x => (obs x.edge).map x.entry

theorem tree_output (xs : List (Item S)) (entries : List (Entry S Q))
    (obs : E → Option (Fin Q)) :
    (tree xs entries).output obs = (observations xs obs).reverse ++ entries := by
  induction xs generalizing entries with
  | nil => simp [tree, observations, SteinerLowerBound.DecisionTree.output]
  | cons x xs ih =>
    simp only [tree, SteinerLowerBound.DecisionTree.output]
    rw [ih]
    cases ho : obs x.edge <;>
      simp [observations, ho, List.reverse_cons, List.append_assoc]

theorem tree_used_subset (xs : List (Item S)) (entries : List (Entry S Q)) :
    ∀ e ∈ (tree xs entries).used, e ∈ xs.map Item.edge := by
  induction xs generalizing entries with
  | nil => simp [tree, SteinerLowerBound.DecisionTree.used]
  | cons x xs ih =>
    intro e he
    rw [tree, SteinerLowerBound.DecisionTree.used] at he
    rcases Finset.mem_insert.mp he with rfl | he
    · simp
    · obtain ⟨obs, _, ho⟩ := Finset.mem_biUnion.mp he
      exact List.mem_cons_of_mem _ (ih _ e ho)

theorem tree_noRepeats (xs : List (Item S)) (hn : (xs.map Item.edge).Nodup)
    (entries : List (Entry S Q)) : (tree xs entries).NoRepeats := by
  induction xs generalizing entries with
  | nil => trivial
  | cons x xs ih =>
    have hnd := List.nodup_cons.mp hn
    refine ⟨fun obs => ih hnd.2 _, ?_⟩
    intro obs he
    exact hnd.1 (tree_used_subset xs _ x.edge he)

noncomputable def assignedMap (old : E → Option (Fin Q)) (xs : List (Item S))
    (obs : E → Option (Fin Q)) : E → Option (Fin Q) :=
  xs.foldr (fun x f => match obs x.edge with
    | none => f
    | some r => Function.update f x.edge (some r)) old

theorem assignedMap_none (old : E → Option (Fin Q)) (xs : List (Item S))
    (obs : E → Option (Fin Q)) (e : E) (ho : obs e = none) :
    assignedMap old xs obs e = old e := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    unfold assignedMap
    simp only [List.foldr_cons]
    cases hx : obs x.edge with
    | none => exact ih
    | some r =>
      have hne : e ≠ x.edge := by intro h; rw [← h, ho] at hx; cases hx
      change Function.update (assignedMap old xs obs) x.edge (some r) e = old e
      rw [Function.update_of_ne hne]
      exact ih

theorem assignedMap_some (old : E → Option (Fin Q)) (xs : List (Item S))
    (obs : E → Option (Fin Q)) (e : E) (r : Fin Q) (ho : obs e = some r)
    (he : e ∈ xs.map Item.edge) : assignedMap old xs obs e = some r := by
  induction xs with
  | nil => simp at he
  | cons x xs ih =>
    simp only [List.map_cons, List.mem_cons] at he
    by_cases hxe : e = x.edge
    · simp [assignedMap, ← hxe, ho]
    · have hrest := he.resolve_left hxe
      have hi := ih hrest
      unfold assignedMap
      simp only [List.foldr_cons]
      cases hx : obs x.edge with
      | none => exact hi
      | some b =>
        change Function.update (assignedMap old xs obs) x.edge (some b) e = some r
        rw [Function.update_of_ne hxe]
        exact hi

theorem assignedMap_absent (old : E → Option (Fin Q)) (xs : List (Item S))
    (obs : E → Option (Fin Q)) (e : E) (he : e ∉ xs.map Item.edge) :
    assignedMap old xs obs e = old e := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hxe : e ≠ x.edge := fun h => he (by simp [h])
    have hrest : e ∉ xs.map Item.edge := fun h => he (by simp [h])
    unfold assignedMap
    simp only [List.foldr_cons]
    cases hx : obs x.edge with
    | none => exact ih hrest
    | some r =>
      change Function.update (assignedMap old xs obs) x.edge (some r) e = old e
      rw [Function.update_of_ne hxe]
      exact ih hrest

theorem commit_assigned (s : Cache S Q) (xs : List (Item S)) (obs : E → Option (Fin Q)) :
    (Cache.commit S Q s (observations xs obs).reverse).assigned =
      assignedMap s.assigned xs obs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    cases ho : obs x.edge with
    | none =>
      simp only [observations, List.filterMap_cons, ho, Option.map_none, assignedMap,
        List.foldr_cons] at *
      exact ih s
    | some r =>
      have ho' : observations (x :: xs) obs = x.entry r :: observations xs obs := by
        simp only [observations, List.filterMap_cons, ho, Option.map_some]
      rw [ho', List.reverse_cons]
      have hc : Cache.commit S Q s ((observations xs obs).reverse ++ [x.entry r]) =
          Cache.assign S Q (Cache.commit S Q s (observations xs obs).reverse)
            x.source x.reverse x.edge r := by
        simp [Cache.commit, List.foldl_append, Item.entry]
      rw [hc]
      change Function.update (Cache.commit S Q s (observations xs obs).reverse).assigned
        x.edge (some r) = assignedMap s.assigned (x :: xs) obs
      rw [ih]
      simp [assignedMap, ho]

end SteinerUpperBound.Matching.Padded.Plan
