module

public import SteinerUpperBound.Matching.Padded.CollectionCredit
public import SteinerUpperBound.Matching.Padded.IteratorCorrect

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Cache

open SteinerLowerBound
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ) [Fintype V]

noncomputable def boundaryValue (A : Account S) (s : Cache S Q) : ℝ :=
  ∑ v, A.W v * (boundary S Q s v : ℝ) / Q

def levelValue (s : Cache S Q) : ℝ := ∑ v, (s.level v : ℝ)

def preparedValue (s : Cache S Q) : ℝ := ∑ v, if s.prepared v then 1 else 0

noncomputable def reserve (A : Account S) (H height L : ℕ) (s : Cache S Q) : ℝ :=
  credit S Q A H height s - 2 * L * boundaryValue S Q A s -
    L * A.Cstar * levelValue S Q s - A.Cstar * preparedValue S Q s

theorem finish_levels (height : ℕ) (v : V) (s : Cache S Q) (xs : List (Entry S Q)) :
    (finish S Q height v s xs).value.level = Function.update s.level v (s.level v + 1) := by
  simp only [finish, Kernel.commit_levels]

theorem finish_boundary (height : ℕ) (v u : V) (s : Cache S Q) (xs : List (Entry S Q)) :
    boundary S Q (finish S Q height v s xs).value u =
      if u = v then Buckets.bound (s.level v + 1) else boundary S Q s u := by
  unfold boundary
  rw [finish_levels]
  by_cases hu : u = v <;> simp only [hu, Function.update_apply, ↓reduceIte]

theorem finish_boundaryValue (A : Account S) (height : ℕ) (v : V) (s : Cache S Q)
    (xs : List (Entry S Q)) :
    boundaryValue S Q A (finish S Q height v s xs).value =
      boundaryValue S Q A s +
        A.W v * ((Buckets.bound (s.level v + 1) : ℝ) - boundary S Q s v) / Q := by
  classical
  have hp (u : V) :
      A.W u * (boundary S Q (finish S Q height v s xs).value u : ℝ) / Q =
        A.W u * (boundary S Q s u : ℝ) / Q +
          if u = v then A.W v *
            ((Buckets.bound (s.level v + 1) : ℝ) - boundary S Q s v) / Q else 0 := by
    rw [finish_boundary]
    by_cases hu : u = v
    · subst u; simp only [↓reduceIte]; ring
    · simp only [hu, ↓reduceIte, add_zero]
  unfold boundaryValue
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  simp

theorem finish_levelValue (height : ℕ) (v : V) (s : Cache S Q) (xs : List (Entry S Q)) :
    levelValue S Q (finish S Q height v s xs).value = levelValue S Q s + 1 := by
  classical
  have hp (u : V) :
      ((finish S Q height v s xs).value.level u : ℝ) =
        (s.level u : ℝ) + if u = v then 1 else 0 := by
    rw [finish_levels]
    by_cases hu : u = v
    · subst u; simp
    · simp [Function.update_of_ne hu, hu]
  unfold levelValue
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  simp

theorem finish_preparedValue (height : ℕ) (v : V) (s : Cache S Q) (xs : List (Entry S Q)) :
    preparedValue S Q (finish S Q height v s xs).value = preparedValue S Q s := by
  have hp : (finish S Q height v s xs).value.prepared = s.prepared :=
    (commit_administration S Q s xs).1
  simp only [preparedValue, hp]

theorem extend_reserve (hQ : 0 < Q) (A : Account S) (H height L : ℕ)
    (v : V) (s : Cache S Q) (hL : extensionCoefficient H height (S.length v) ≤ L) :
    (extend S Q hQ height v s).expectedCost (Command.bucketCharge A) A.rate +
        (extend S Q hQ height v s).expect (reserve S Q A H height L) ≤
      reserve S Q A H height L s := by
  classical
  by_cases hb : Buckets.bound (s.level v + 1) ≤ Q
  · let δ := A.W v * ((Buckets.bound (s.level v + 1) : ℝ) - boundary S Q s v) / Q
    have hphi :
        (extend S Q hQ height v s).expect (boundaryValue S Q A) = boundaryValue S Q A s + δ := by
      simp only [extend, hb, ↓reduceIte, Program.expect_bind, Program.expect_tick,
        Program.expect_ret, finish_boundaryValue, Program.expect_const, δ]
    have hlevel :
        (extend S Q hQ height v s).expect (levelValue S Q) = levelValue S Q s + 1 := by
      simp only [extend, hb, ↓reduceIte, Program.expect_bind, Program.expect_tick,
        Program.expect_ret, finish_levelValue, Program.expect_const]
    have hprep :
        (extend S Q hQ height v s).expect (preparedValue S Q) = preparedValue S Q s := by
      simp only [extend, hb, ↓reduceIte, Program.expect_bind, Program.expect_tick,
        Program.expect_ret, finish_preparedValue, Program.expect_const]
    have hp := Buckets.probability_le_increment Q (s.level v) hb
    have hab := Buckets.bound_mono (Nat.le_succ (s.level v))
    have hsub : ((Buckets.bound (s.level v + 1) - Buckets.bound (s.level v) : ℕ) : ℝ) =
        (Buckets.bound (s.level v + 1) : ℝ) - boundary S Q s v :=
      Nat.cast_sub hab
    rw [hsub] at hp
    have hpw := mul_le_mul_of_nonneg_right hp (A.W_nonneg v)
    have hδ :
        (Range.probability Q (boundary S Q s v) (Buckets.bound (s.level v + 1)) : ℝ) * A.W v ≤ 2 * δ := by
      dsimp only [δ, boundary] at hpw ⊢
      convert hpw using 1 <;> ring
    have ha := extend_amortized S Q hQ A H height v s hb
    have hp0 := Range.probability_bounds Q (boundary S Q s v) (Buckets.bound (s.level v + 1))
      (Buckets.bound_strictMono (Nat.lt_succ_self _)) hb
    have hbase : 0 ≤ (Range.probability Q (boundary S Q s v)
        (Buckets.bound (s.level v + 1)) : ℝ) * A.W v + A.Cstar :=
      add_nonneg (mul_nonneg (by exact_mod_cast hp0.1) (A.W_nonneg v)) A.Cstar_nonneg
    have hcoef := mul_le_mul_of_nonneg_right (show (extensionCoefficient H height (S.length v) : ℝ) ≤ L by
      exact_mod_cast hL) hbase
    have hscale := mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg L : (0 : ℝ) ≤ _)
    have he (f g : Cache S Q → ℝ) :
        (extend S Q hQ height v s).expect (fun t => f t - g t) =
          (extend S Q hQ height v s).expect f - (extend S Q hQ height v s).expect g :=
      Law.expect_sub _ _ _
    change (extend S Q hQ height v s).expectedCost (Command.bucketCharge A) A.rate +
      (extend S Q hQ height v s).expect (fun t => reserve S Q A H height L t) ≤
        reserve S Q A H height L s
    simp only [reserve, he, Program.expect_const_mul, hphi, hlevel, hprep]
    nlinarith
  · simp only [extend, hb, ↓reduceIte, Program.expectedCost_ret, Program.expect_ret, zero_add]
    exact le_rfl

end SteinerUpperBound.Matching.Padded.Cache
