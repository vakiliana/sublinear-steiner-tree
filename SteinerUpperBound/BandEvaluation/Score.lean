module

public import SteinerUpperBound.BandEvaluation.Benefit

@[expose] public section

set_option maxHeartbeats 1500000

namespace SteinerUpperBound.BandEvaluation

open QueryProgram SmallCoverProgram
open scoped Classical

variable {M Q : Type*} {n m : ℕ}

noncomputable def candidate (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau : ℝ)
    (t : Fin ((m * m) * (m * m))) : Code M Q ℝ :=
  (tuple C t).bind (fun Y => .tick 15 (if 2 ≤ Y.length then
    (finiteBenefit C d (tau * a) (a - 2 * rho) Y).bind (fun benefit =>
      (localCost C d Y).bind (fun cost => .tick 3 (.pure (benefit - cost - 6 * rho))))
    else .pure 0))

noncomputable def candidateRun (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau : ℝ)
    (t : Fin ((m * m) * (m * m))) : Outcome ℝ :=
  let Y := tupleRun C t
  Y.combine ((if 2 ≤ Y.value.length then
    let b := finiteBenefitRun C d (tau * a) (a - 2 * rho) Y.value
    let c := localCostRun C d Y.value
    b.combine (c.combine ((Outcome.pure (b.value - c.value - 6 * rho)).add 4 0 0 0))
    else .pure 0).add 16 0 0 0)

noncomputable def scoreStep (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau best : ℝ)
    (t : Fin ((m * m) * (m * m))) : Code M Q ℝ :=
  (candidate C d a rho tau t).bind (fun x => .tick 2 (.pure (max best x)))

noncomputable def scoreStepRun (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau best : ℝ)
    (t : Fin ((m * m) * (m * m))) : Outcome ℝ :=
  (candidateRun C d a rho tau t).combine
    ((Outcome.pure (max best (candidateRun C d a rho tau t).value)).add 3 0 0 0)

noncomputable def score (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau : ℝ) : Code M Q ℝ :=
  Code.foldList (scoreStep C d a rho tau) (List.finRange ((m * m) * (m * m))) 0

noncomputable def scoreRun (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau : ℝ) : Outcome ℝ :=
  Code.folded (scoreStepRun C d a rho tau) (List.finRange ((m * m) * (m * m))) 0

theorem candidate_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau : ℝ) (t) :
    Code.Evaluates oracle bits (candidate C d a rho tau t) (candidateRun C d a rho tau t) := by
  apply Code.Evaluates.bind _ _ _ _ _ _ (tuple_evaluates _ _ _ _)
  apply Code.Evaluates.tick
  split_ifs
  · exact Code.Evaluates.bind _ _ _ _ _ _ (finiteBenefit_evaluates _ _ _ _ _ _ _)
      (Code.Evaluates.bind _ _ _ _ _ _ (localCost_evaluates _ _ _ _ _)
        (Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 3))
  · exact Code.evaluates_pure _ _ _

theorem scoreStep_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau best : ℝ) (t) :
    Code.Evaluates oracle bits (scoreStep C d a rho tau best t) (scoreStepRun C d a rho tau best t) :=
  Code.Evaluates.bind _ _ _ _ _ _ (candidate_evaluates _ _ _ _ _ _ _ _)
    (Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 2)

theorem score_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau : ℝ) :
    Code.Evaluates oracle bits (score C d a rho tau) (scoreRun C d a rho tau) :=
  Code.foldList_evaluates _ _ _ _ (scoreStep_evaluates oracle bits C d a rho tau) _ _

theorem candidateRun_valid (I : Instance (Fin n)) (C : Vector (Fin n) m)
    (hC : Function.Injective C.get) (d : MetricTable n m)
    (hd : ∀ i v, distanceAt d i v = I.distance (C.get i) v) (a rho tau : ℝ)
    (hband : tau * a ≤ a - 2 * rho) (t) (h2 : 2 ≤ (tupleRun C t).value.length) :
    (candidateRun C d a rho tau t).value =
      Band.benefit I (retained C) (tupleRun C t).value.toFinset (tau * a) (a - 2 * rho) -
        Structural.localCost I (tupleRun C t).value.toFinset - 6 * rho := by
  have hb := finiteBenefitRun_correct I C hC d hd (tau * a) (a - 2 * rho) hband
    (tupleRun C t).value (tupleRun_subset C t)
  have hc := localCostRun_correct I C d hd (tupleRun C t).value (tupleRun_nodup C t) (tupleRun_subset C t)
  simp only [candidateRun, h2, ↓reduceIte, Outcome.combine, Outcome.add, Outcome.pure, hb, hc]

theorem candidateRun_invalid (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau : ℝ)
    (t) (h2 : ¬2 ≤ (tupleRun C t).value.length) : (candidateRun C d a rho tau t).value = 0 := by
  simp only [candidateRun, h2, ↓reduceIte, Outcome.combine, Outcome.add, Outcome.pure]

theorem candidateRun_le_score (I : Instance (Fin n)) (C : Vector (Fin n) m)
    (hC : Function.Injective C.get) (d : MetricTable n m)
    (hd : ∀ i v, distanceAt d i v = I.distance (C.get i) v) (a rho tau : ℝ)
    (hband : tau * a ≤ a - 2 * rho) (t) :
    (candidateRun C d a rho tau t).value ≤ Band.score I (retained C) a rho tau := by
  by_cases h2 : 2 ≤ (tupleRun C t).value.length
  · rw [candidateRun_valid I C hC d hd a rho tau hband t h2]
    have hcard := List.toFinset_card_of_nodup (tupleRun_nodup C t)
    exact Band.score_witness I (retained C) _ a rho tau (tupleRun_subset C t)
      (by omega) (by have := tupleRun_length C t; omega)
  · rw [candidateRun_invalid C d a rho tau t h2]
    exact Band.score_nonneg _ _ _ _ _

theorem candidateRun_attains (I : Instance (Fin n)) (C : Vector (Fin n) m)
    (hC : Function.Injective C.get) (d : MetricTable n m)
    (hd : ∀ i v, distanceAt d i v = I.distance (C.get i) v) (a rho tau : ℝ)
    (hband : tau * a ≤ a - 2 * rho) (Y : Finset (Fin n))
    (hYC : Y ⊆ retained C) (h2 : 2 ≤ Y.card) (h4 : Y.card ≤ 4) :
    ∃ t, (candidateRun C d a rho tau t).value =
      Band.benefit I (retained C) Y (tau * a) (a - 2 * rho) - Structural.localCost I Y - 6 * rho := by
  obtain ⟨t, ht⟩ := tuple_surjective C Y hYC h2 h4
  have hc := List.toFinset_card_of_nodup (tupleRun_nodup C t)
  rw [ht] at hc
  refine ⟨t, ?_⟩
  rw [candidateRun_valid I C hC d hd a rho tau hband t (by omega), ht]

theorem foldMax_ge_init {A : Type*} (l : List A) (f : A → ℝ) (init : ℝ) :
    init ≤ l.foldl (fun best a => max best (f a)) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => exact (le_max_left _ _).trans (ih _)

theorem foldMax_ge_member {A : Type*} (l : List A) (f : A → ℝ) (init : ℝ)
    (a : A) (ha : a ∈ l) : f a ≤ l.foldl (fun best a => max best (f a)) init := by
  induction l generalizing init with
  | nil => simp at ha
  | cons b l ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact (le_max_right _ _).trans (foldMax_ge_init l f _)
      · exact ih _ ha

theorem foldMax_le {A : Type*} (l : List A) (f : A → ℝ) (init b : ℝ)
    (hi : init ≤ b) (hf : ∀ a ∈ l, f a ≤ b) :
    l.foldl (fun best a => max best (f a)) init ≤ b := by
  induction l generalizing init with
  | nil => exact hi
  | cons a l ih =>
      exact ih _ (max_le hi (hf a List.mem_cons_self)) (fun a ha => hf a (List.mem_cons_of_mem _ ha))

theorem scoreRun_correct (I : Instance (Fin n)) (C : Vector (Fin n) m)
    (hC : Function.Injective C.get) (d : MetricTable n m)
    (hd : ∀ i v, distanceAt d i v = I.distance (C.get i) v) (a rho tau : ℝ)
    (hband : tau * a ≤ a - 2 * rho) :
    (scoreRun C d a rho tau).value = Band.score I (retained C) a rho tau := by
  rw [scoreRun, folded_value]
  change (List.finRange ((m * m) * (m * m))).foldl
    (fun best t => max best (candidateRun C d a rho tau t).value) 0 = _
  apply le_antisymm
  · exact foldMax_le _ _ _ _ (Band.score_nonneg _ _ _ _ _)
      (fun t _ => candidateRun_le_score I C hC d hd a rho tau hband t)
  · by_cases hp : 0 < Band.score I (retained C) a rho tau
    · obtain ⟨Y, hYC, h2, h4, he⟩ := Band.score_attained_positive I (retained C) a rho tau hp
      obtain ⟨t, ht⟩ := candidateRun_attains I C hC d hd a rho tau hband Y hYC h2 h4
      rw [he, ← ht]
      exact foldMax_ge_member _ (fun t => (candidateRun C d a rho tau t).value) 0 t
        (List.mem_finRange t)
    · exact (le_of_not_gt hp).trans (foldMax_ge_init _ _ _)

theorem candidateRun_work (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau : ℝ) (t) :
    (candidateRun C d a rho tau t).work ≤ 5000000000 * (n + 1) * (m + 1) ^ 7 := by
  have ht := tupleRun_work C t
  have hl := tupleRun_length C t
  have hb := finiteBenefitRun_work C d (tau * a) (a - 2 * rho) (tupleRun C t).value hl
  have hc := localCostRun_work C d (tupleRun C t).value hl
  have hp : m + 1 ≤ (m + 1) ^ 7 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1 ≤ m + 1) (by omega : 1 ≤ 7)
  have hcp := Nat.mul_le_mul_left (4000000000 * (n + 1)) hp
  have hnp : (m + 1) ^ 7 ≤ (n + 1) * (m + 1) ^ 7 := by nlinarith
  have h1 : 1 ≤ (n + 1) * (m + 1) ^ 7 := by
    have hp : 0 < (n + 1) * (m + 1) ^ 7 := by positivity
    omega
  dsimp only [candidateRun, Outcome.combine, Outcome.add, Outcome.pure]
  split_ifs <;> nlinarith

theorem scoreRun_work (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau : ℝ) :
    (scoreRun C d a rho tau).work ≤ 6000000000 * (n + 1) * (m + 1) ^ 11 := by
  have hs (best t) : (scoreStepRun C d a rho tau best t).work ≤
      5000000000 * (n + 1) * (m + 1) ^ 7 + 3 := by
    have hh := candidateRun_work C d a rho tau t
    dsimp only [scoreStepRun, Outcome.combine, Outcome.add, Outcome.pure]
    omega
  have hf := Code.folded_work (scoreStepRun C d a rho tau)
    (5000000000 * (n + 1) * (m + 1) ^ 7 + 3) hs (List.finRange ((m * m) * (m * m))) 0
  have h1 : 1 ≤ (n + 1) * (m + 1) ^ 7 := by
    have hp : 0 < (n + 1) * (m + 1) ^ 7 := by positivity
    omega
  have hcoef : 5000000000 * (n + 1) * (m + 1) ^ 7 + 3 + 1 ≤
      6000000000 * (n + 1) * (m + 1) ^ 7 := by nlinarith
  have hm : (m * m) * (m * m) ≤ (m + 1) ^ 4 := by nlinarith
  have hh := Nat.mul_le_mul hcoef hm
  simp only [List.length_finRange] at hf
  change (scoreRun C d a rho tau).work ≤ _ at hf
  nlinarith

theorem candidateRun_resources (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau : ℝ) (t) :
    (candidateRun C d a rho tau t).metricQueries = 0 ∧
      (candidateRun C d a rho tau t).retentionQueries = 0 ∧
      (candidateRun C d a rho tau t).positiveReplies = 0 := by
  have ht := tupleRun_resources C t
  have hb := finiteBenefitRun_resources C d (tau * a) (a - 2 * rho) (tupleRun C t).value
  have hc := localCostRun_resources C d (tupleRun C t).value
  dsimp only [candidateRun]
  split_ifs <;> simp only [Outcome.combine, Outcome.add, Outcome.pure, ht, hb, hc, Nat.zero_add, and_self]

theorem scoreStepRun_resources (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau best : ℝ) (t) :
    (scoreStepRun C d a rho tau best t).metricQueries = 0 ∧
      (scoreStepRun C d a rho tau best t).retentionQueries = 0 ∧
      (scoreStepRun C d a rho tau best t).positiveReplies = 0 := by
  have hh := candidateRun_resources C d a rho tau t
  simpa only [scoreStepRun, Outcome.combine, Outcome.add, Outcome.pure, Nat.add_zero, Nat.zero_add] using hh

theorem scoreRun_resources (C : Vector (Fin n) m) (d : MetricTable n m) (a rho tau : ℝ) :
    (scoreRun C d a rho tau).metricQueries = 0 ∧ (scoreRun C d a rho tau).retentionQueries = 0 ∧
      (scoreRun C d a rho tau).positiveReplies = 0 := by
  have hm := Code.folded_metric_queries (scoreStepRun C d a rho tau) 0
    (fun best t => (scoreStepRun_resources C d a rho tau best t).1.le)
    (List.finRange ((m * m) * (m * m))) 0
  have hr := folded_retention_zero (scoreStepRun C d a rho tau)
    (fun best t => (scoreStepRun_resources C d a rho tau best t).2.1)
    (List.finRange ((m * m) * (m * m))) 0
  have hp := folded_positive_zero (scoreStepRun C d a rho tau)
    (fun best t => (scoreStepRun_resources C d a rho tau best t).2.2)
    (List.finRange ((m * m) * (m * m))) 0
  exact ⟨by simpa only [scoreRun, Nat.zero_mul, Nat.le_zero] using hm, hr, hp⟩

end SteinerUpperBound.BandEvaluation
