module

public import SteinerUpperBound.SavingScores.Law

@[expose] public section

namespace SteinerUpperBound.SavingScores

open SteinerLowerBound
open scoped Classical BigOperators

variable {X A D : Type*} [Fintype X] [Fintype D]

/-- The global strict-order law is an analysis parameter, not a runtime generator. -/
noncomputable def sampleLawFor [Nonempty X] (μ : Law (Matching.Rank D))
    (part : X → A) (hsurj : Function.Surjective part) : Law (Sample X D) :=
  (Law.uniform X).bind (fun x =>
    μ.bind (fun rank =>
      (CategoricalCoupling.bernoulli (initiationRate part hsurj (part x))).map
        (fun coin => (x, (rank, coin)))))

noncomputable def expectedMatchingFor (μ : Law (Matching.Rank D)) (G : Matching.Graph A D) : ℝ :=
  μ.expect (fun rank => (G.greedy rank).card)

noncomputable def scoreMeanFor [Nonempty X] (μ : Law (Matching.Rank D))
    (part : X → A) (hsurj : Function.Surjective part) (covered U : Finset A)
    (G : Matching.Graph A D) : ℝ :=
  (sampleLawFor μ part hsurj).expect (pointScore part covered U G)

theorem sampleLawFor_uniform [Nonempty X] (part : X → A) (hsurj : Function.Surjective part) :
    sampleLawFor (Matching.Rank.uniform (E := D)) part hsurj = sampleLaw (D := D) part hsurj := rfl

theorem expectedMatchingFor_uniform (G : Matching.Graph A D) :
    expectedMatchingFor (Matching.Rank.uniform (E := D)) G = expectedMatching G := rfl

theorem scoreMeanFor_uniform [Nonempty X] (part : X → A) (hsurj : Function.Surjective part)
    (covered U : Finset A) (G : Matching.Graph A D) :
    scoreMeanFor (Matching.Rank.uniform (E := D)) part hsurj covered U G =
      scoreMean part hsurj covered U G := rfl

theorem scoreMeanFor_eq [Fintype A] [Nonempty X] (μ : Law (Matching.Rank D))
    (part : X → A) (hsurj : Function.Surjective part)
    (covered U : Finset A) (hdisj : Disjoint covered U)
    (G : Matching.Graph A D) (hends : ∀ e, G.left e ∈ U ∧ G.right e ∈ U) :
    scoreMeanFor μ part hsurj covered U G =
      ((covered.card : ℝ) + expectedMatchingFor μ G) / (Nat.card X : ℝ) := by
  unfold scoreMeanFor sampleLawFor
  simp only [Law.expect_bind, Law.expect_map]
  simp_rw [coin_mean]
  rw [expect_comm (Law.uniform X) μ]
  simp_rw [uniform_part_mean part hsurj, sum_partWeight covered U hdisj G hends]
  simp only [div_eq_mul_inv, Law.expect_mul_const, Law.expect_add,
    Law.expect_const, expectedMatchingFor]

theorem scoreMeanFor_bounds [Nonempty X] (μ : Law (Matching.Rank D))
    (part : X → A) (hsurj : Function.Surjective part)
    (covered U : Finset A) (G : Matching.Graph A D) :
    0 ≤ scoreMeanFor μ part hsurj covered U G ∧ scoreMeanFor μ part hsurj covered U G ≤ 1 :=
  ScoreSampling.mean_bounds (sampleLawFor μ part hsurj) (pointScore part covered U G)
    (fun seed => (pointScore_bounds part hsurj covered U G seed).1)
    (fun seed => (pointScore_bounds part hsurj covered U G seed).2)

theorem iid_score_deviationFor [Nonempty X] (μ : Law (Matching.Rank D))
    (part : X → A) (hsurj : Function.Surjective part)
    (covered U : Finset A) (G : Matching.Graph A D)
    (n : ℕ) (hn : 0 < n) (xi beta : ℝ) (hxi : 0 < xi)
    (hbudget : 1 ≤ beta * ((n : ℝ) * xi ^ 2)) :
    (Covers.FiniteSampling.tape (sampleLawFor μ part hsurj) n).prob
      {w | xi < |ScoreSampling.empirical (pointScore part covered U G) n w -
        scoreMeanFor μ part hsurj covered U G|} ≤ beta :=
  ScoreSampling.empirical_deviation_of_budget _ _
    (fun seed => (pointScore_bounds part hsurj covered U G seed).1)
    (fun seed => (pointScore_bounds part hsurj covered U G seed).2)
    n hn xi beta hxi hbudget

end SteinerUpperBound.SavingScores
