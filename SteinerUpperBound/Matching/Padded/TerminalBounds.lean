module

public import SteinerUpperBound.Matching.Padded.TruncatedMoments

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E] (P : Parameters S)

theorem Oracle.level_moment (v : V) :
    (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).expect
        (fun ranks => Cache.levelValue S P.rankCard (Oracle.idealVertex S P v ranks).cache) ≤
      ((P.rankExponent : ℝ) + 1) * (Execution.law S P v).expect (fun x =>
        if Function.Injective x.2 then Cache.requestValue S P.rankCard (fun _ => 1)
          ((Oracle.vertex S P v).output x.1).cache else 0) +
        ((P.rankExponent : ℝ) + 1) * Fintype.card V *
          ((Fintype.card E : ℝ) ^ 2 / P.rankCard) := by
  classical
  let μ := UniformRanks.law P.rankCard P.rankCard_pos (E := E)
  have hh := expect_one_bad μ
    (fun ranks => Cache.levelValue S P.rankCard (Oracle.idealVertex S P v ranks).cache)
    (fun ranks => Cache.requestValue S P.rankCard (fun _ => 1) (Oracle.idealVertex S P v ranks).cache)
    Function.Injective ((P.rankExponent : ℝ) + 1) (((P.rankExponent : ℝ) + 1) * Fintype.card V)
    (by positivity) (by positivity)
    (fun _ => Cache.requestValue_nonneg S P (fun _ => 1) (fun _ => zero_le_one) _)
    (fun ranks => Cache.levelValue_le S P _ (Oracle.idealVertex_safe S P v ranks).invariant.legal)
    (fun ranks hn => Cache.levelValue_requests S P _ ranks
      (Oracle.idealVertex_safe S P v ranks).invariant.legal
      (Oracle.idealVertex_accounted S P v ranks hn).1)
  have hstat := Execution.expect_ideal S P v (fun r ranks => if Function.Injective ranks then
    Cache.requestValue S P.rankCard (fun _ => 1) r.cache else 0)
  have hh' :
      μ.expect (fun ranks => Cache.levelValue S P.rankCard (Oracle.idealVertex S P v ranks).cache) ≤
        ((P.rankExponent : ℝ) + 1) * (Execution.law S P v).expect (fun x =>
          if Function.Injective x.2 then Cache.requestValue S P.rankCard (fun _ => 1)
            ((Oracle.vertex S P v).output x.1).cache else 0) +
          ((P.rankExponent : ℝ) + 1) * Fintype.card V * μ.prob {ranks | ¬ Function.Injective ranks} := by
    convert hh using 1
    rw [hstat]
    congr 2
    apply congrArg μ.expect
    funext ranks
    by_cases hn : Function.Injective ranks <;> simp [hn]
  exact hh'.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left (UniformRanks.collision_bound P.rankCard P.rankCard_pos) (by positivity)))

theorem Oracle.prepared_moment (v : V) :
    (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).expect
        (fun ranks => Cache.preparedValue S P.rankCard (Oracle.idealVertex S P v ranks).cache) ≤
      (Execution.law S P v).expect (fun x =>
        if Function.Injective x.2 then Cache.requestValue S P.rankCard (fun _ => 1)
          ((Oracle.vertex S P v).output x.1).cache else 0) +
        Fintype.card V * ((Fintype.card E : ℝ) ^ 2 / P.rankCard) := by
  classical
  let μ := UniformRanks.law P.rankCard P.rankCard_pos (E := E)
  have hh := expect_one_bad μ
    (fun ranks => Cache.preparedValue S P.rankCard (Oracle.idealVertex S P v ranks).cache)
    (fun ranks => Cache.requestValue S P.rankCard (fun _ => 1) (Oracle.idealVertex S P v ranks).cache)
    Function.Injective 1 (Fintype.card V) zero_le_one (Nat.cast_nonneg _)
    (fun _ => Cache.requestValue_nonneg S P (fun _ => 1) (fun _ => zero_le_one) _)
    (fun _ => Cache.preparedValue_le S P _)
    (fun ranks hn => by simpa only [one_mul] using
      Cache.preparedValue_requests S P _ (Oracle.idealVertex_accounted S P v ranks hn).2)
  have hstat := Execution.expect_ideal S P v (fun r ranks => if Function.Injective ranks then
    Cache.requestValue S P.rankCard (fun _ => 1) r.cache else 0)
  have hh' :
      μ.expect (fun ranks => Cache.preparedValue S P.rankCard (Oracle.idealVertex S P v ranks).cache) ≤
        (Execution.law S P v).expect (fun x =>
          if Function.Injective x.2 then Cache.requestValue S P.rankCard (fun _ => 1)
            ((Oracle.vertex S P v).output x.1).cache else 0) +
          Fintype.card V * μ.prob {ranks | ¬ Function.Injective ranks} := by
    convert hh using 1
    rw [hstat]
    simp only [one_mul]
    congr 1
    apply congrArg μ.expect
    funext ranks
    by_cases hn : Function.Injective ranks <;> simp [hn]
  exact hh'.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left (UniformRanks.collision_bound P.rankCard P.rankCard_pos) (Nat.cast_nonneg _)))

end SteinerUpperBound.Matching.Padded
