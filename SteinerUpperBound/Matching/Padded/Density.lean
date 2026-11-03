module

public import SteinerUpperBound.Matching.Padded.Accounting
public import SteinerUpperBound.Matching.Padded.Potential

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E] (P : Parameters S)

def DensityGood (z : ℝ) (ranks : E → Fin P.rankCard) : Prop :=
  ∀ v (i : Fin (P.rankExponent + 2)),
    (Buckets.bound i.val : ℝ) / P.rankCard * G.degree v ≤
      2 * ((UniformRanks.Count P.rankCard G v (Buckets.bound i.val) ranks : ℝ) + z)

theorem density_failure_le (z : ℝ) :
    (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).prob {ranks | ¬ DensityGood S P z ranks} ≤
      (Fintype.card V : ℝ) * (P.rankExponent + 2) * Real.exp (-z) := by
  classical
  have he : {ranks : E → Fin P.rankCard | ¬ DensityGood S P z ranks} =
      {ranks | ∃ vi : V × Fin (P.rankExponent + 2),
        (Buckets.bound vi.2.val : ℝ) / P.rankCard * G.degree vi.1 >
          2 * ((UniformRanks.Count P.rankCard G vi.1 (Buckets.bound vi.2.val) ranks : ℝ) + z)} := by
    ext ranks
    simp only [Set.mem_ofPred_eq, DensityGood, not_forall, not_le, Prod.exists]
  rw [he]
  calc
    _ ≤ ∑ vi : V × Fin (P.rankExponent + 2),
        (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).prob {ranks |
          (Buckets.bound vi.2.val : ℝ) / P.rankCard * G.degree vi.1 >
            2 * ((UniformRanks.Count P.rankCard G vi.1 (Buckets.bound vi.2.val) ranks : ℝ) + z)} :=
      Law.finite_union_bound _ _
    _ ≤ ∑ _vi : V × Fin (P.rankExponent + 2), Real.exp (-z) := by
      apply Finset.sum_le_sum
      intro vi _
      have hi : vi.2.val ≤ P.rankExponent + 1 := by omega
      have hb : Buckets.bound vi.2.val ≤ P.rankCard :=
        (Buckets.bound_mono hi).trans_eq (by simp only [Buckets.bound_succ, Parameters.rankCard])
      exact UniformRanks.lower_tail P.rankCard P.rankCard_pos G vi.1 _ hb z
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]

theorem boundary_step_le (i : ℕ) :
    Buckets.bound (i + 1) ≤ 2 * Buckets.bound i + 1 := by
  cases i with
  | zero => simp
  | succ i => simp only [Buckets.bound_succ, pow_succ]; omega

noncomputable def densityWeight (A : Account S) (v : V) : ℝ := A.W v / ((G.degree v : ℝ) + 1)

theorem densityWeight_nonneg (A : Account S) (v : V) : 0 ≤ densityWeight S A v :=
  div_nonneg (A.W_nonneg v) (by positivity)

theorem densityWeight_le (A : Account S) (v : V) : densityWeight S A v ≤ A.W v := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (G.degree v : ℝ) + 1)).mpr
  nlinarith [A.W_nonneg v, Nat.cast_nonneg (α := ℝ) (G.degree v)]

theorem densityWeight_degree_le (A : Account S) (v : V) :
    (G.degree v : ℝ) * densityWeight S A v ≤ A.W v := by
  unfold densityWeight
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (G.degree v : ℝ) + 1)).mpr
  nlinarith [A.W_nonneg v]

theorem bucket_ratio_scalar (a b d j c z q : ℝ)
    (hq : 0 < q) (hz : 0 ≤ z) (hj : 1 ≤ j) (hd : 0 ≤ d)
    (hdq : d ≤ q) (hdensity : a / q * d ≤ 2 * (c + z))
    (hcount : c ≤ j) (hstep : b ≤ 2 * a + 1)
    (hb : 0 ≤ b) (hbq : b ≤ q) (hdiscrete : d = 0 ∨ 1 ≤ d) :
    b / q * (d + 1) ≤ (8 * z + 10) * j := by
  have hr0 : 0 ≤ d / q := div_nonneg hd hq.le
  have hr1 : d / q ≤ 1 := (div_le_one hq).mpr hdq
  have hm := mul_le_mul_of_nonneg_right hstep hr0
  have heq : b / q * d = b * (d / q) := by ring
  have heq' : 2 * a * (d / q) = 2 * (a / q * d) := by ring
  have hbase : b / q * d ≤ 4 * j + 4 * z + 1 := by
    rw [heq]
    nlinarith
  have hcharge : b / q * d ≤ (4 * z + 5) * j := by
    nlinarith [mul_nonneg hz (sub_nonneg.mpr hj)]
  rcases hdiscrete with hzero | hone
  · have hb1 : b / q ≤ 1 := (div_le_one hq).mpr hbq
    simp only [hzero, zero_add, mul_one]
    nlinarith [mul_nonneg hz (by linarith : 0 ≤ j)]
  · have hb0 : 0 ≤ b / q := div_nonneg hb hq.le
    nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hone)]

theorem boundary_ratio_le (s : Cache S P.rankCard) (ranks : E → Fin P.rankCard)
    (hn : Function.Injective ranks) (hs : Cache.Invariant S P.rankCard s)
    (hp : Cache.PriorCountBound S P.rankCard s ranks)
    (z : ℝ) (hz : 0 ≤ z) (hg : DensityGood S P z ranks) (v : V) :
    (Cache.boundary S P.rankCard s v : ℝ) / P.rankCard * ((G.degree v : ℝ) + 1) ≤
      (8 * z + 10) * s.requests v := by
  have hQ : (0 : ℝ) < P.rankCard := by exact_mod_cast P.rankCard_pos
  have hj : (0 : ℝ) ≤ s.requests v := Nat.cast_nonneg _
  by_cases hl : s.level v = 0
  · simp only [Cache.boundary, hl, Buckets.bound_zero, Nat.cast_zero, zero_div, zero_mul]
    exact mul_nonneg (by linarith) hj
  · have hpos : 0 < s.level v := Nat.pos_of_ne_zero hl
    have hcount := hp v hpos
    have hj1 : (1 : ℝ) ≤ s.requests v := by exact_mod_cast (show 1 ≤ s.requests v by omega)
    have hlev := Cache.level_le_power S P.rankExponent s v hs.legal
    let i : Fin (P.rankExponent + 2) := ⟨s.level v - 1, by omega⟩
    have hdensity := hg v i
    have hcountR : (UniformRanks.Count P.rankCard G v (Buckets.bound i.val) ranks : ℝ) ≤ s.requests v :=
      by exact_mod_cast hcount.le
    have hstep : Cache.boundary S P.rankCard s v ≤ 2 * Buckets.bound i.val + 1 := by
      have hh := boundary_step_le (s.level v - 1)
      simpa only [Nat.sub_add_cancel hpos, Cache.boundary] using hh
    have hstepR : (Cache.boundary S P.rankCard s v : ℝ) ≤ 2 * Buckets.bound i.val + 1 :=
      by exact_mod_cast hstep
    have he : G.degree v ≤ P.rankCard := by
      have hc := Fintype.card_le_of_injective ranks hn
      have hd : G.degree v ≤ Fintype.card E := by
        unfold Graph.degree
        exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)
      simpa only [Fintype.card_fin] using hd.trans hc
    have hdiscrete : (G.degree v : ℝ) = 0 ∨ 1 ≤ (G.degree v : ℝ) := by
      by_cases hd : G.degree v = 0
      · exact Or.inl (by exact_mod_cast hd)
      · exact Or.inr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd)
    exact bucket_ratio_scalar _ _ _ _ _ _ _ hQ hz hj1 (Nat.cast_nonneg _)
      (by exact_mod_cast he) hdensity hcountR hstepR (Nat.cast_nonneg _)
      (by exact_mod_cast hs.legal.1 v) hdiscrete

theorem boundaryValue_le (A : Account S) (s : Cache S P.rankCard) (ranks : E → Fin P.rankCard)
    (hn : Function.Injective ranks) (hs : Cache.Invariant S P.rankCard s)
    (hp : Cache.PriorCountBound S P.rankCard s ranks)
    (z : ℝ) (hz : 0 ≤ z) (hg : DensityGood S P z ranks) :
    Cache.boundaryValue S P.rankCard A s ≤
      (8 * z + 10) * Cache.requestValue S P.rankCard (densityWeight S A) s := by
  unfold Cache.boundaryValue Cache.requestValue
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  have hb := boundary_ratio_le S P s ranks hn hs hp z hz hg v
  have hw := densityWeight_nonneg S A v
  have hh := mul_le_mul_of_nonneg_left hb hw
  have hd : (G.degree v : ℝ) + 1 ≠ 0 := by positivity
  have hQ : (P.rankCard : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt P.rankCard_pos
  have heq : densityWeight S A v *
      ((Cache.boundary S P.rankCard s v : ℝ) / P.rankCard * ((G.degree v : ℝ) + 1)) =
      A.W v * (Cache.boundary S P.rankCard s v : ℝ) / P.rankCard := by
    unfold densityWeight
    field_simp [hd, hQ]
  rw [heq] at hh
  nlinarith

end SteinerUpperBound.Matching.Padded
