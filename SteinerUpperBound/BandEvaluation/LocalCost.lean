module

public import SteinerUpperBound.BandEvaluation.RawMST

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

open QueryProgram SmallCoverProgram
open scoped Classical

variable {M Q : Type*} {n m : ℕ}

noncomputable def augmentedVertices {V : Type*} (v : V) (Y : Finset V) : Finset V := insert v Y

noncomputable def localStep (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n))
    (best : ℝ) (v : Fin n) : Code M Q ℝ :=
  (augment L v).bind (fun aug =>
    (rawMST C d aug).bind (fun cost => .tick 2 (.pure (min best cost))))

noncomputable def localStepRun (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n))
    (best : ℝ) (v : Fin n) : Outcome ℝ :=
  let aug := augmentRun L v
  let mst := rawMSTRun C d aug.value
  aug.combine (mst.combine ((Outcome.pure (min best mst.value)).add 3 0 0 0))

noncomputable def localCost (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    Code M Q ℝ :=
  (rawMST C d L).bind (fun base => Code.foldList (localStep C d L) (List.finRange n) base)

noncomputable def localCostRun (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    Outcome ℝ :=
  let base := rawMSTRun C d L
  base.combine (Code.folded (localStepRun C d L) (List.finRange n) base.value)

theorem localStep_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) (best : ℝ) (v : Fin n) :
    Code.Evaluates oracle bits (localStep C d L best v) (localStepRun C d L best v) :=
  Code.Evaluates.bind _ _ _ _ _ _ (augment_evaluates _ _ _ _)
    (Code.Evaluates.bind _ _ _ _ _ _ (rawMST_evaluates _ _ _ _ _)
      (Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 2))

theorem localCost_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    Code.Evaluates oracle bits (localCost C d L) (localCostRun C d L) :=
  Code.Evaluates.bind _ _ _ _ _ _ (rawMST_evaluates _ _ _ _ _)
    (Code.foldList_evaluates _ _ _ _ (localStep_evaluates oracle bits C d L) _ _)

theorem augmented_observed (C : Vector (Fin n) m) (L : List (Fin n))
    (hLC : L.toFinset ⊆ retained C) (v : Fin n) :
    ∀ x ∈ (augmentRun L v).value, ∀ y ∈ (augmentRun L v).value,
      x = y ∨ x ∈ retained C ∨ y ∈ retained C := by
  intro x hx y hy
  have hx' : x ∈ insert v L.toFinset := by rw [← augmentRun_set]; exact List.mem_toFinset.mpr hx
  have hy' : y ∈ insert v L.toFinset := by rw [← augmentRun_set]; exact List.mem_toFinset.mpr hy
  by_cases hxL : x ∈ L.toFinset
  · exact Or.inr (Or.inl (hLC hxL))
  · by_cases hyL : y ∈ L.toFinset
    · exact Or.inr (Or.inr (hLC hyL))
    · exact Or.inl (((Finset.mem_insert.mp hx').resolve_right hxL).trans
        ((Finset.mem_insert.mp hy').resolve_right hyL).symm)

theorem localStepRun_value (I : Instance (Fin n)) (C : Vector (Fin n) m)
    (d : MetricTable n m) (hd : ∀ i v, distanceAt d i v = I.distance (C.get i) v)
    (L : List (Fin n)) (hL : L.Nodup) (hLC : L.toFinset ⊆ retained C) (best : ℝ) (v : Fin n) :
    (localStepRun C d L best v).value =
      min best (TerminalMST.value I.weight (augmentedVertices v L.toFinset)) := by
  have hh := rawMSTRun_correct I C d hd (augmentRun L v).value
    (augmentRun_nodup L hL v) (augmented_observed C L hLC v)
  rw [augmentRun_set] at hh
  have he : insert v L.toFinset = augmentedVertices v L.toFinset := by
    ext x
    simp [augmentedVertices]
  rw [he] at hh
  change min best (rawMSTRun C d (augmentRun L v).value).value = _
  rw [hh]

theorem foldMin_le_init {A : Type*} (l : List A) (f : A → ℝ) (init : ℝ) :
    l.foldl (fun best a => min best (f a)) init ≤ init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => exact (ih _).trans (min_le_left _ _)

theorem foldMin_le_member {A : Type*} (l : List A) (f : A → ℝ) (init : ℝ)
    (a : A) (ha : a ∈ l) : l.foldl (fun best a => min best (f a)) init ≤ f a := by
  induction l generalizing init with
  | nil => simp at ha
  | cons b l ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact (foldMin_le_init l f _).trans (min_le_right _ _)
      · exact ih _ ha

theorem le_foldMin {A : Type*} (l : List A) (f : A → ℝ) (init b : ℝ)
    (hi : b ≤ init) (hf : ∀ a ∈ l, b ≤ f a) :
    b ≤ l.foldl (fun best a => min best (f a)) init := by
  induction l generalizing init with
  | nil => exact hi
  | cons a l ih =>
      exact ih _ (le_min hi (hf a List.mem_cons_self)) (fun a ha => hf a (List.mem_cons_of_mem _ ha))

theorem localCostRun_correct (I : Instance (Fin n)) (C : Vector (Fin n) m)
    (d : MetricTable n m) (hd : ∀ i v, distanceAt d i v = I.distance (C.get i) v)
    (L : List (Fin n)) (hL : L.Nodup) (hLC : L.toFinset ⊆ retained C) :
    (localCostRun C d L).value = Structural.localCost I L.toFinset := by
  have hb := rawMSTRun_correct I C d hd L hL
    (fun x hx y _ => Or.inr (Or.inl (hLC (List.mem_toFinset.mpr hx))))
  change (Code.folded (localStepRun C d L) (List.finRange n) (rawMSTRun C d L).value).value = _
  rw [folded_value]
  have hstep : (fun best v => (localStepRun C d L best v).value) =
      fun best v => min best (TerminalMST.value I.weight (augmentedVertices v L.toFinset)) := by
    funext best v
    exact localStepRun_value I C d hd L hL hLC best v
  rw [hstep, hb, Structural.localCost_eq_pointMinimum]
  let f := fun v : Fin n => TerminalMST.value I.weight (augmentedVertices v L.toFinset)
  let base := TerminalMST.value I.weight L.toFinset
  change (List.finRange n).foldl (fun best v => min best (f v)) base =
    Structural.pointMinimum I.weight L.toFinset
  apply le_antisymm
  · have hm : Structural.pointMinimum I.weight L.toFinset ∈ Structural.pointValues I.weight L.toFinset :=
      Finset.min'_mem _ _
    rcases Finset.mem_insert.mp hm with hm | hm
    · rw [hm]
      exact foldMin_le_init _ f base
    · obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hm
      rw [← hv]
      change _ ≤ f v
      exact foldMin_le_member _ f base v (List.mem_finRange v)
  · apply le_foldMin
    · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    · intro v _
      change Structural.pointMinimum I.weight L.toFinset ≤
        TerminalMST.value I.weight (augmentedVertices v L.toFinset)
      exact Finset.min'_le (Structural.pointValues I.weight L.toFinset) _ (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩))

theorem localStepRun_work (C : Vector (Fin n) m) (d : MetricTable n m)
    (L : List (Fin n)) (hL : L.length ≤ 4) (best : ℝ) (v : Fin n) :
    (localStepRun C d L best v).work ≤ 1000000100 * (m + 1) := by
  have ha := augmentRun_work L v
  have hl := augmentRun_length L v
  have hm := rawMSTRun_work_small C d (augmentRun L v).value (by omega)
  dsimp only [localStepRun, Outcome.combine, Outcome.add, Outcome.pure]
  nlinarith

theorem localCostRun_work (C : Vector (Fin n) m) (d : MetricTable n m)
    (L : List (Fin n)) (hL : L.length ≤ 4) :
    (localCostRun C d L).work ≤ 4000000000 * (n + 1) * (m + 1) := by
  have hb := rawMSTRun_work_small C d L (by omega)
  have hf := Code.folded_work (localStepRun C d L) (1000000100 * (m + 1))
    (localStepRun_work C d L hL) (List.finRange n) (rawMSTRun C d L).value
  simp only [List.length_finRange] at hf
  dsimp only [localCostRun, Outcome.combine]
  nlinarith

theorem localStepRun_resources (C : Vector (Fin n) m) (d : MetricTable n m)
    (L : List (Fin n)) (best : ℝ) (v : Fin n) :
    (localStepRun C d L best v).metricQueries = 0 ∧
      (localStepRun C d L best v).retentionQueries = 0 ∧
      (localStepRun C d L best v).positiveReplies = 0 := by
  have ha := augmentRun_resources L v
  have hm := rawMSTRun_resources C d (augmentRun L v).value
  simp only [localStepRun, Outcome.combine, Outcome.add, Outcome.pure, ha, hm, Nat.zero_add, and_self]

theorem localCostRun_resources (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    (localCostRun C d L).metricQueries = 0 ∧ (localCostRun C d L).retentionQueries = 0 ∧
      (localCostRun C d L).positiveReplies = 0 := by
  have hb := rawMSTRun_resources C d L
  have hm := Code.folded_metric_queries (localStepRun C d L) 0
    (fun best v => (localStepRun_resources C d L best v).1.le) (List.finRange n) (rawMSTRun C d L).value
  have hr := folded_retention_zero (localStepRun C d L)
    (fun best v => (localStepRun_resources C d L best v).2.1) (List.finRange n) (rawMSTRun C d L).value
  have hp := folded_positive_zero (localStepRun C d L)
    (fun best v => (localStepRun_resources C d L best v).2.2) (List.finRange n) (rawMSTRun C d L).value
  have hm' := Nat.eq_zero_of_le_zero (by simpa only [Nat.zero_mul] using hm)
  simp only [localCostRun, Outcome.combine, hb, hm', hr, hp, Nat.zero_add, and_self]

end SteinerUpperBound.BandEvaluation
