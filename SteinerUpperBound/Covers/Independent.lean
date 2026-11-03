module

public import SteinerUpperBound.Covers.Balls

@[expose] public section

namespace SteinerUpperBound.Covers

open SteinerLowerBound
open scoped Classical BigOperators

noncomputable local instance {V : Type*} (I : Instance V) : DecidableEq (Terminal I) :=
  Classical.decEq _

namespace ClosedRelation

variable {U : Type*} [Fintype U]

noncomputable def reciprocalRate (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (x : U) : Rate :=
  ⟨(degree R x : ℝ)⁻¹, by
    have hd : (0 : ℝ) < degree R x := by exact_mod_cast degree_pos R hrefl x
    have h1 : (1 : ℝ) ≤ degree R x := by exact_mod_cast degree_pos R hrefl x
    exact ⟨by positivity, (inv_le_one₀ hd).mpr h1⟩⟩

noncomputable def retentionRate (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (ψ : ℕ) (x : U) : Rate :=
  ⟨1 - (1 - (reciprocalRate R hrefl x : ℝ)) ^ ψ, by
    rcases (reciprocalRate R hrefl x).property with ⟨hp0, hp1⟩
    exact ⟨sub_nonneg.mpr (pow_le_one₀ (by linarith) (by linarith)),
      by nlinarith [pow_nonneg (show 0 ≤ 1 - (reciprocalRate R hrefl x : ℝ) by
        linarith) ψ]⟩⟩

theorem retentionRate_le (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (ψ : ℕ) (x : U) :
    (retentionRate R hrefl ψ x : ℝ) ≤ (ψ : ℝ) * (degree R x : ℝ)⁻¹ := by
  rcases (reciprocalRate R hrefl x).property with ⟨hp0, hp1⟩
  change 1 - (1 - (reciprocalRate R hrefl x : ℝ)) ^ ψ ≤
    (ψ : ℝ) * (reciprocalRate R hrefl x : ℝ)
  induction ψ with
  | zero => simp
  | succ ψ ih =>
    have hpw : (1 - (reciprocalRate R hrefl x : ℝ)) ^ ψ ≤ 1 :=
      pow_le_one₀ (by linarith) (by linarith)
    rw [pow_succ, Nat.cast_succ]
    nlinarith

noncomputable def forcedRate (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (root : U) (ψ : ℕ) (x : U) : Rate :=
  if x = root then ⟨1, by norm_num⟩ else retentionRate R hrefl ψ x

noncomputable def independentBits (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (root : U) (ψ : ℕ) : Law (U → Bool) :=
  Law.pi (fun x => CategoricalCoupling.bernoulli (forcedRate R hrefl root ψ x))

theorem bernoulli_true (p : Rate) :
    (CategoricalCoupling.bernoulli p).prob {b | b = true} = (p : ℝ) := by
  simp [Law.prob, CategoricalCoupling.bernoulli]

theorem bernoulli_false (p : Rate) :
    (CategoricalCoupling.bernoulli p).prob {b | b = false} = 1 - (p : ℝ) := by
  simp [Law.prob, CategoricalCoupling.bernoulli]

theorem independent_root (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (root : U) (ψ : ℕ) :
    (independentBits R hrefl root ψ).prob {b | b root = true} = 1 := by
  calc
    _ = (CategoricalCoupling.bernoulli (forcedRate R hrefl root ψ root)).prob
        {b | b = true} := Law.prob_pi_coordinate
      (fun x => CategoricalCoupling.bernoulli (forcedRate R hrefl root ψ x))
      {b | b = true} root
    _ = (forcedRate R hrefl root ψ root : ℝ) := bernoulli_true _
    _ = 1 := by simp [forcedRate]

theorem mean_bound (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (root : U) (ψ : ℕ) :
    IndependentTrials.mean
      (fun x => CategoricalCoupling.bernoulli (forcedRate R hrefl root ψ x))
      (fun _ b => b = true) ≤
        1 + (ψ : ℝ) * ∑ x, (degree R x : ℝ)⁻¹ := by
  classical
  unfold IndependentTrials.mean
  simp_rw [bernoulli_true]
  calc
    _ ≤ ∑ x, ((if x = root then (1 : ℝ) else 0) +
        (ψ : ℝ) * (degree R x : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x = root
      · simp only [forcedRate, hx, ↓reduceIte]
        exact le_add_of_nonneg_right (by positivity)
      · simpa [forcedRate, hx] using retentionRate_le R hrefl ψ x
    _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]

theorem avoid_set (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (root : U) (ψ : ℕ) (S : Finset U) :
    (independentBits R hrefl root ψ).prob {b | ∀ x ∈ S, b x = false} ≤
      Real.exp (-(ψ : ℝ) * ∑ x ∈ S, (degree R x : ℝ)⁻¹) := by
  classical
  have hp (x : U) :
      (CategoricalCoupling.bernoulli (forcedRate R hrefl root ψ x)).prob
        {b | x ∈ S → b = false} =
          if x ∈ S then 1 - (forcedRate R hrefl root ψ x : ℝ) else 1 := by
    by_cases hx : x ∈ S
    · simpa only [hx, true_implies, ↓reduceIte] using
        bernoulli_false (forcedRate R hrefl root ψ x)
    · have he : {b : Bool | x ∈ S → b = false} = Set.univ := by ext b; simp [hx]
      rw [he, Law.prob_univ, if_neg hx]
  unfold independentBits
  rw [Law.prob_pi_all _ (fun x b => x ∈ S → b = false)]
  simp_rw [hp]
  rw [Finset.prod_ite_mem, Finset.univ_inter]
  calc
    _ ≤ ∏ x ∈ S, Real.exp (-(ψ : ℝ) * (degree R x : ℝ)⁻¹) := by
      apply Finset.prod_le_prod₀
      · intro x _
        exact sub_nonneg.mpr (forcedRate R hrefl root ψ x).property.2
      · intro x _
        by_cases hx : x = root
        · simp only [forcedRate, hx, ↓reduceIte, sub_self]
          positivity
        · simp only [forcedRate, hx, ↓reduceIte, retentionRate, sub_sub_cancel]
          have hbase : 1 - (reciprocalRate R hrefl x : ℝ) ≤
              Real.exp (-(reciprocalRate R hrefl x : ℝ)) := by
            linarith [Real.add_one_le_exp (-(reciprocalRate R hrefl x : ℝ))]
          have hpow := pow_le_pow_left₀
            (sub_nonneg.mpr (reciprocalRate R hrefl x).property.2) hbase ψ
          simpa only [← Real.exp_nat_mul, reciprocalRate, mul_neg, neg_mul] using hpow
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]

theorem miss_ball (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (root : U) (ψ h : ℕ) (hh : Fintype.card U < 2 ^ h) (x : U) :
    (independentBits R hrefl root ψ).prob
      {b | ∀ y ∈ ball R x h, b y = false} ≤ Real.exp (-(ψ : ℝ) / 2) := by
  apply (avoid_set R hrefl root ψ (ball R x h)).trans
  apply Real.exp_le_exp.mpr
  have hb := ball_reciprocal_lower R hrefl x h hh
  have hψ : (0 : ℝ) ≤ ψ := Nat.cast_nonneg ψ
  nlinarith

end ClosedRelation

def IsCover {V : Type*} (I : Instance V) (ρ : ℝ) (b : Terminal I → Bool) : Prop :=
  ∀ x : Terminal I, ∃ y : Terminal I, b y = true ∧ I.distance x.val y.val ≤ ρ

theorem independent_cover_failure {V : Type*} [Fintype V] (I : Instance V)
    (r : ℝ) (hr : 0 ≤ r) (root : Terminal I) (ψ h : ℕ)
    (hh : I.terminals.card < 2 ^ h) :
    (ClosedRelation.independentBits (near I r) (near_refl I hr) root ψ).prob
      {b | ¬ IsCover I ((h : ℝ) * r) b} ≤
        (I.terminals.card : ℝ) * Real.exp (-(ψ : ℝ) / 2) := by
  classical
  let μ := ClosedRelation.independentBits (near I r) (near_refl I hr) root ψ
  have hs : {b | ¬ IsCover I ((h : ℝ) * r) b} ⊆
      {b | ∃ x : Terminal I,
        ∀ y ∈ ClosedRelation.ball (near I r) x h, b y = false} := by
    intro b hb
    change ¬ ∀ x : Terminal I, ∃ y : Terminal I,
      b y = true ∧ I.distance x.val y.val ≤ (h : ℝ) * r at hb
    push Not at hb
    obtain ⟨x, hx⟩ := hb
    refine ⟨x, fun y hy => Bool.eq_false_iff.mpr (fun hby => ?_)⟩
    exact not_le_of_gt (hx y hby) (ball_distance I hr x h y hy)
  calc
    _ ≤ μ.prob {b | ∃ x : Terminal I,
        ∀ y ∈ ClosedRelation.ball (near I r) x h, b y = false} := μ.prob_mono hs
    _ ≤ ∑ x : Terminal I, μ.prob
        {b | ∀ y ∈ ClosedRelation.ball (near I r) x h, b y = false} :=
      Law.finite_union_bound _ _
    _ ≤ ∑ _x : Terminal I, Real.exp (-(ψ : ℝ) / 2) := by
      apply Finset.sum_le_sum
      intro x _
      apply ClosedRelation.miss_ball
      simpa using hh
    _ = _ := by simp

set_option maxHeartbeats 800000 in
theorem independent_size_tail {V : Type*} [Fintype V] (I : Instance V)
    (r : ℝ) (hr : 0 < r) (root : Terminal I) (ψ : ℕ) (v : ℝ) :
    (ClosedRelation.independentBits (near I r) (near_refl I hr.le) root ψ).prob
      {b | Real.exp 1 * (1 + (ψ : ℝ) * (1 + 2 * I.mst / r)) + v ≤
        ((CategoricalCoupling.selected b).card : ℝ)} ≤ Real.exp (-v) := by
  have hm := (ClosedRelation.mean_bound (near I r) (near_refl I hr.le) root ψ).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (reciprocal_degree_bound I r hr)
      (Nat.cast_nonneg ψ)))
  simpa only [ClosedRelation.independentBits, IndependentTrials.count,
    CategoricalCoupling.selected] using IndependentTrials.tail_mean_bound
    (fun x : Terminal I =>
      CategoricalCoupling.bernoulli
        (ClosedRelation.forcedRate (near I r) (near_refl I hr.le) root ψ x))
    (fun _ b => b = true) (1 + (ψ : ℝ) * (1 + 2 * I.mst / r)) v hm

/-- A concrete independent single-scale law, without an assumed cover or packing
certificate. The hop count may be any logarithmic integer with `k < 2^h`. -/
theorem independent_cover_and_size {V : Type*} [Fintype V] (I : Instance V)
    (r : ℝ) (hr : 0 < r) (root : Terminal I) (ψ h : ℕ)
    (hh : I.terminals.card < 2 ^ h) (v : ℝ) :
    (ClosedRelation.independentBits (near I r) (near_refl I hr.le) root ψ).prob
      {b | ¬ IsCover I ((h : ℝ) * r) b ∨
        Real.exp 1 * (1 + (ψ : ℝ) * (1 + 2 * I.mst / r)) + v ≤
          ((CategoricalCoupling.selected b).card : ℝ)} ≤
      (I.terminals.card : ℝ) * Real.exp (-(ψ : ℝ) / 2) + Real.exp (-v) := by
  exact (Law.prob_union_le _ _ _).trans
    (add_le_add (independent_cover_failure I r hr.le root ψ h hh)
      (independent_size_tail I r hr root ψ v))

end SteinerUpperBound.Covers
