module

public import SteinerUpperBound.SavingScores.Partition
public import SteinerUpperBound.SetSystem.CappedMatching
public import SteinerUpperBound.Matching.Oracle
public import SteinerUpperBound.ScoreSampling

@[expose] public section

namespace SteinerUpperBound.SavingScores

open SteinerLowerBound
open scoped Classical BigOperators

theorem expect_comm {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : Law Ω) (ν : Law Γ) (w : Ω → Γ → ℝ) :
    μ.expect (fun x => ν.expect (w x)) = ν.expect (fun y => μ.expect (fun x => w x y)) := by
  simp only [Law.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem bernoulli_expect (p : Rate) (w : Bool → ℝ) :
    (CategoricalCoupling.bernoulli p).expect w =
      (p : ℝ) * w true + (1 - (p : ℝ)) * w false := by
  simp [Law.expect, CategoricalCoupling.bernoulli]

variable {A D : Type*} [Fintype D]

noncomputable def matchedValue (G : Matching.Graph A D) (rank : Matching.Rank D) (a : A) : ℝ :=
  if (G.vertexOracle rank a).value.isSome then 1 / 2 else 0

theorem matchedValue_bounds (G : Matching.Graph A D) (rank : Matching.Rank D) (a : A) :
    0 ≤ matchedValue G rank a ∧ matchedValue G rank a ≤ 1 := by
  unfold matchedValue
  split_ifs <;> norm_num

theorem matchedValue_endpoints (G : Matching.Graph A D) (rank : Matching.Rank D) (a : A) :
    matchedValue G rank a =
      if a ∈ SetSystem.matchedEndpoints G (G.greedy rank) then (1 / 2 : ℝ) else 0 := by
  classical
  by_cases ha : a ∈ SetSystem.matchedEndpoints G (G.greedy rank)
  · obtain ⟨e, he, hi⟩ := (SetSystem.mem_matchedEndpoints G _ a).mp ha
    have hv := (G.vertexOracle_eq_some_iff rank a e).mpr ⟨he, hi⟩
    simp [matchedValue, hv, ha]
  · cases hv : (G.vertexOracle rank a).value with
    | none => simp [matchedValue, hv, ha]
    | some e =>
        obtain ⟨he, hi⟩ := G.vertexOracle_eq_some rank hv
        exact (ha ((SetSystem.mem_matchedEndpoints G _ a).mpr ⟨e, he, hi⟩)).elim

theorem matchedValue_zero (G : Matching.Graph A D) (U : Finset A)
    (hends : ∀ e, G.left e ∈ U ∧ G.right e ∈ U)
    (rank : Matching.Rank D) (a : A) (ha : a ∉ U) :
    matchedValue G rank a = 0 := by
  classical
  have hn : a ∉ SetSystem.matchedEndpoints G (G.greedy rank) := by
    intro h
    obtain ⟨e, _, he⟩ := (SetSystem.mem_matchedEndpoints G _ a).mp h
    rcases he with he | he
    · exact ha (he ▸ (hends e).1)
    · exact ha (he ▸ (hends e).2)
  simp only [matchedValue_endpoints, hn, ↓reduceIte]

theorem sum_matchedValue [Fintype A] (G : Matching.Graph A D) (rank : Matching.Rank D) :
    (∑ a, matchedValue G rank a) = ((G.greedy rank).card : ℝ) := by
  classical
  have hh : (∑ a, matchedValue G rank a) =
      ((SetSystem.matchedEndpoints G (G.greedy rank)).card : ℝ) / 2 := by
    simp only [matchedValue_endpoints]
    simp [div_eq_mul_inv]
  rw [SetSystem.matchedEndpoints_card G _ (G.greedy_isMatching rank)] at hh
  push_cast at hh
  linarith

noncomputable def partWeight (covered U : Finset A) (G : Matching.Graph A D)
    (rank : Matching.Rank D) (a : A) : ℝ :=
  if a ∈ covered then 1 else if a ∈ U then matchedValue G rank a else 0

theorem sum_partWeight [Fintype A] (covered U : Finset A) (hdisj : Disjoint covered U)
    (G : Matching.Graph A D) (hends : ∀ e, G.left e ∈ U ∧ G.right e ∈ U)
    (rank : Matching.Rank D) :
    (∑ a, partWeight covered U G rank a) = (covered.card : ℝ) + (G.greedy rank).card := by
  classical
  have hp (a : A) : partWeight covered U G rank a =
      (if a ∈ covered then (1 : ℝ) else 0) + matchedValue G rank a := by
    by_cases hc : a ∈ covered
    · have hU : a ∉ U := fun h => Finset.disjoint_left.mp hdisj hc h
      simp [partWeight, hc, matchedValue_zero G U hends rank a hU]
    · by_cases hU : a ∈ U
      · simp [partWeight, hc, hU]
      · simp [partWeight, hc, hU, matchedValue_zero G U hends rank a hU]
  simp only [hp, Finset.sum_add_distrib, sum_matchedValue]
  simp

variable {X : Type*} [Fintype X]

abbrev Sample (X D : Type*) [Fintype D] := X × (Matching.Rank D × Bool)

/-- This is an analysis seed law, not an efficient full-permutation generator. -/
noncomputable def sampleLaw [Nonempty X] (part : X → A)
    (hsurj : Function.Surjective part) : Law (Sample X D) :=
  (Law.uniform X).bind (fun x =>
    (Matching.Rank.uniform (E := D)).bind (fun rank =>
      (CategoricalCoupling.bernoulli (initiationRate part hsurj (part x))).map
        (fun coin => (x, (rank, coin)))))

noncomputable def pointScore (part : X → A) (covered U : Finset A)
    (G : Matching.Graph A D) (seed : Sample X D) : ℝ :=
  if part seed.1 ∈ covered then 1 / (partSize part (part seed.1) : ℝ)
  else if part seed.1 ∈ U then
    if seed.2.2 then matchedValue G seed.2.1 (part seed.1) else 0
  else 0

theorem pointScore_bounds (part : X → A) (hsurj : Function.Surjective part)
    (covered U : Finset A) (G : Matching.Graph A D) (seed : Sample X D) :
    0 ≤ pointScore part covered U G seed ∧ pointScore part covered U G seed ≤ 1 := by
  unfold pointScore
  split_ifs
  · exact reciprocal_bounds part hsurj _
  · exact matchedValue_bounds G _ _
  · norm_num
  · norm_num

theorem coin_mean (part : X → A) (hsurj : Function.Surjective part)
    (covered U : Finset A) (G : Matching.Graph A D) (x : X) (rank : Matching.Rank D) :
    (CategoricalCoupling.bernoulli (initiationRate part hsurj (part x))).expect
      (fun coin => pointScore part covered U G (x, (rank, coin))) =
        partWeight covered U G rank (part x) / (partSize part (part x) : ℝ) := by
  classical
  rw [bernoulli_expect]
  by_cases hc : part x ∈ covered <;> by_cases hU : part x ∈ U <;>
    simp [pointScore, partWeight, hc, hU, initiationRate] <;> ring

noncomputable def expectedMatching (G : Matching.Graph A D) : ℝ :=
  (Matching.Rank.uniform (E := D)).expect (fun rank => (G.greedy rank).card)

noncomputable def scoreMean [Nonempty X] (part : X → A)
    (hsurj : Function.Surjective part) (covered U : Finset A) (G : Matching.Graph A D) : ℝ :=
  (sampleLaw (D := D) part hsurj).expect (pointScore part covered U G)

theorem scoreMean_eq [Fintype A] [Nonempty X] (part : X → A)
    (hsurj : Function.Surjective part) (covered U : Finset A) (hdisj : Disjoint covered U)
    (G : Matching.Graph A D) (hends : ∀ e, G.left e ∈ U ∧ G.right e ∈ U) :
    scoreMean part hsurj covered U G =
      ((covered.card : ℝ) + expectedMatching G) / (Nat.card X : ℝ) := by
  unfold scoreMean sampleLaw
  simp only [Law.expect_bind, Law.expect_map]
  simp_rw [coin_mean]
  rw [expect_comm (Law.uniform X) (Matching.Rank.uniform (E := D))]
  simp_rw [uniform_part_mean part hsurj, sum_partWeight covered U hdisj G hends]
  simp only [div_eq_mul_inv, Law.expect_mul_const, Law.expect_add,
    Law.expect_const, expectedMatching]

theorem scoreMean_bounds [Nonempty X] (part : X → A)
    (hsurj : Function.Surjective part) (covered U : Finset A) (G : Matching.Graph A D) :
    0 ≤ scoreMean part hsurj covered U G ∧ scoreMean part hsurj covered U G ≤ 1 :=
  ScoreSampling.mean_bounds (sampleLaw part hsurj) (pointScore part covered U G)
    (fun seed => (pointScore_bounds part hsurj covered U G seed).1)
    (fun seed => (pointScore_bounds part hsurj covered U G seed).2)

theorem iid_score_deviation [Nonempty X] (part : X → A)
    (hsurj : Function.Surjective part) (covered U : Finset A) (G : Matching.Graph A D)
    (n : ℕ) (hn : 0 < n) (xi beta : ℝ) (hxi : 0 < xi)
    (hbudget : 1 ≤ beta * ((n : ℝ) * xi ^ 2)) :
    (Covers.FiniteSampling.tape (sampleLaw (D := D) part hsurj) n).prob
      {w | xi < |ScoreSampling.empirical (pointScore part covered U G) n w -
        scoreMean part hsurj covered U G|} ≤ beta :=
  ScoreSampling.empirical_deviation_of_budget _ _
    (fun seed => (pointScore_bounds part hsurj covered U G seed).1)
    (fun seed => (pointScore_bounds part hsurj covered U G seed).2)
    n hn xi beta hxi hbudget

end SteinerUpperBound.SavingScores
