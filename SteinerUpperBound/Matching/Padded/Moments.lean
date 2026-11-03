module

public import SteinerUpperBound.Matching.Padded.BucketProgram
public import SteinerUpperBound.Matching.Padded.WeightedVertices

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

namespace Program

variable {C A : Type*}

theorem expect_sub (p : Program C A) (f g : A → ℝ) :
    p.expect (fun a => f a - g a) = p.expect f - p.expect g :=
  Law.expect_sub p.law (fun leaf => f (p.output leaf)) (fun leaf => g (p.output leaf))

end Program

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E] (P : Parameters S)

theorem Oracle.expected_cache (v : V) (f : Cache S P.rankCard → ℝ) :
    (Oracle.vertex S P v).expect (fun r => f r.cache) =
      (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).expect
        (fun ranks => f (Oracle.idealVertex S P v ranks).cache) := by
  have hj := Oracle.vertex_joint S P v (fun r _ => f r.cache)
  simp only [Law.expect_const] at hj
  rw [Cache.empty_completion] at hj
  exact hj.symm

theorem Cache.boundaryValue_le_sum (A : Account S) (s : Cache S P.rankCard)
    (hs : Cache.Legal S P.rankCard s) :
    Cache.boundaryValue S P.rankCard A s ≤ ∑ v, A.W v := by
  unfold Cache.boundaryValue
  apply Finset.sum_le_sum
  intro v _
  have hQ : (0 : ℝ) < P.rankCard := by exact_mod_cast P.rankCard_pos
  apply (div_le_iff₀ hQ).mpr
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs.1 v) (A.W_nonneg v)

theorem Cache.levelValue_le (s : Cache S P.rankCard) (hs : Cache.Legal S P.rankCard s) :
    Cache.levelValue S P.rankCard s ≤ (P.rankExponent + 1 : ℝ) * Fintype.card V := by
  calc
    _ ≤ ∑ _v : V, ((P.rankExponent : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro v _
      exact_mod_cast Cache.level_le_power S P.rankExponent s v hs
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem Cache.preparedValue_le (s : Cache S P.rankCard) :
    Cache.preparedValue S P.rankCard s ≤ Fintype.card V := by
  calc
    _ ≤ ∑ _v : V, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      cases s.prepared v <;> norm_num
    _ = _ := by simp

theorem Cache.levelValue_requests (s : Cache S P.rankCard) (ranks : E → Fin P.rankCard)
    (hs : Cache.Legal S P.rankCard s) (hp : Cache.PriorCountBound S P.rankCard s ranks) :
    Cache.levelValue S P.rankCard s ≤
      (P.rankExponent + 1 : ℝ) * Cache.requestValue S P.rankCard (fun _ => 1) s := by
  unfold Cache.levelValue Cache.requestValue
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : s.level v = 0
  · simp only [hv, Nat.cast_zero, one_mul]
    positivity
  · have hl := Cache.level_le_power S P.rankExponent s v hs
    have hc := hp v (Nat.pos_of_ne_zero hv)
    have hreq : (1 : ℝ) ≤ s.requests v := by exact_mod_cast (show 1 ≤ s.requests v by omega)
    have hlev : (s.level v : ℝ) ≤ (P.rankExponent : ℝ) + 1 := by exact_mod_cast hl
    simp only [one_mul]
    have hscale := mul_le_mul_of_nonneg_left hreq
      (show (0 : ℝ) ≤ (P.rankExponent : ℝ) + 1 by positivity)
    exact hlev.trans (by simpa only [mul_one] using hscale)

theorem Cache.preparedValue_requests (s : Cache S P.rankCard) (hs : Cache.PreparedBound S P.rankCard s) :
    Cache.preparedValue S P.rankCard s ≤ Cache.requestValue S P.rankCard (fun _ => 1) s := by
  unfold Cache.preparedValue Cache.requestValue
  apply Finset.sum_le_sum
  intro v _
  cases hp : s.prepared v with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, one_mul]; positivity
  | true =>
    simp only [↓reduceIte, one_mul]
    exact_mod_cast hs v hp

theorem Oracle.bucket_moments (A : Account S) (v : V) :
    (Oracle.vertex S P v).expectedCost (Command.bucketCharge A) A.rate ≤
      2 * Parameters.bucketCoefficient S P *
          (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).expect
            (fun ranks => Cache.boundaryValue S P.rankCard A (Oracle.idealVertex S P v ranks).cache) +
        Parameters.bucketCoefficient S P * A.Cstar *
          (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).expect
            (fun ranks => Cache.levelValue S P.rankCard (Oracle.idealVertex S P v ranks).cache) +
        A.Cstar * (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).expect
          (fun ranks => Cache.preparedValue S P.rankCard (Oracle.idealVertex S P v ranks).cache) := by
  let H := P.rankExponent + 1
  let L := Parameters.bucketCoefficient S P
  have hj := Oracle.vertex_bucket S P A H L (Parameters.bucketCoefficient_bound S P) v
  simp only [Cache.reserve, Program.expect_sub, Program.expect_const_mul] at hj
  rw [Oracle.expected_cache S P v (Cache.credit S P.rankCard A H P.sortHeight),
    Oracle.expected_cache S P v (Cache.boundaryValue S P.rankCard A),
    Oracle.expected_cache S P v (Cache.levelValue S P.rankCard),
    Oracle.expected_cache S P v (Cache.preparedValue S P.rankCard)] at hj
  have hc : 0 ≤ (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).expect
      (fun ranks => Cache.credit S P.rankCard A H P.sortHeight (Oracle.idealVertex S P v ranks).cache) := by
    apply Law.expect_nonneg
    intro ranks
    have hs := Oracle.idealVertex_safe S P v ranks
    exact mul_nonneg (mul_nonneg A.rate_nonneg (Nat.cast_nonneg _))
      (Cache.sortingCredit_nonneg S P.rankCard H _ (fun u =>
        Cache.level_le_power S P.rankExponent _ u hs.invariant.legal))
  change _ ≤ 2 * (L : ℝ) * _ + (L : ℝ) * A.Cstar * _ + A.Cstar * _
  linarith

end SteinerUpperBound.Matching.Padded
