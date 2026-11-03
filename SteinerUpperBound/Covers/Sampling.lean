module

public import SteinerUpperBound.Covers.Rejection

@[expose] public section

namespace SteinerUpperBound.Covers.Rejection

open SteinerLowerBound
open scoped Classical BigOperators
open FiniteSampling

variable {U : Type*} [Fintype U] [Nonempty U]

noncomputable def poolLaw (C s : ℕ) : Law (Fin s → Fin C → U) :=
  tape (tape (Law.uniform U) C) s

def labels (b : U → Bool) (root : U) (C s : ℕ) (rows : Fin s → Fin C → U) :
    Fin s → U :=
  fun j => (first b C (rows j)).getD root

def proposals (b : U → Bool) (C s : ℕ) (rows : Fin s → Fin C → U) : ℕ :=
  ∑ j, waiting b C (rows j)

def Successful (b : U → Bool) (C s : ℕ) (rows : Fin s → Fin C → U) : Prop :=
  ∀ j, first b C (rows j) ≠ none

theorem proposals_le (b : U → Bool) (C s : ℕ) (rows : Fin s → Fin C → U) :
    proposals b C s rows ≤ s * C := by
  apply (Finset.sum_le_sum (fun j _ => waiting_le b C (rows j))).trans
  simp

theorem pool_success_atom (b : U → Bool) (hb : (retained b).Nonempty)
    (root : U) (C s : ℕ) (w : Fin s → U) :
    (poolLaw C s).prob {rows | Successful b C s rows ∧ labels b root C s rows = w} =
      (1 - (1 - hitRate b) ^ C) ^ s * (tape (uniformRetained b hb) s).mass w := by
  classical
  have he : {rows | Successful b C s rows ∧ labels b root C s rows = w} =
      {rows | ∀ j, first b C (rows j) = some (w j)} := by
    ext rows
    simp only [Set.mem_ofPred_eq, Successful, labels, funext_iff]
    constructor
    · rintro ⟨hs, hl⟩ j
      cases hx : first b C (rows j) with
      | none => exact (hs j hx).elim
      | some x => simpa [hx] using hl j
    · intro h
      exact ⟨fun j => by simp [h j], fun j => by simp [h j]⟩
  rw [he, poolLaw, prob_box (tape (Law.uniform U) C) s
    (fun j row => first b C row = some (w j))]
  simp_rw [first_success_atom b hb]
  rw [Finset.prod_mul_distrib, tape_mass]
  simp

theorem pool_failure (b : U → Bool) (hb : (retained b).Nonempty) (C s : ℕ) :
    (poolLaw C s).prob {rows | ¬ Successful b C s rows} =
      1 - (1 - (1 - hitRate b) ^ C) ^ s := by
  classical
  have hs : (tape (Law.uniform U) C).prob {w | first b C w ≠ none} =
      1 - (1 - hitRate b) ^ C := by
    have he : {w : Fin C → U | first b C w ≠ none} =
        ({w | first b C w = none} : Set (Fin C → U))ᶜ := rfl
    rw [he, Law.prob_compl, first_failure b hb]
  change (poolLaw C s).prob ({rows | Successful b C s rows}ᶜ) = _
  rw [Law.prob_compl]
  unfold poolLaw Successful
  rw [prob_all (tape (Law.uniform U) C) (fun w => first b C w ≠ none) s, hs]

theorem pool_failure_le (b : U → Bool) (hb : (retained b).Nonempty) (C s : ℕ) :
    (poolLaw C s).prob {rows | ¬ Successful b C s rows} ≤
      (s : ℝ) * (1 - hitRate b) ^ C := by
  rw [pool_failure b hb]
  let q : Rate := ⟨(1 - hitRate b) ^ C, pow_nonneg (sub_nonneg.mpr (hitRate_le_one b)) C,
    pow_le_one₀ (sub_nonneg.mpr (hitRate_le_one b)) (by linarith [hitRate_nonneg b])⟩
  have h := CategoricalCoupling.prod_complements_lower (fun _ : Fin s => q) Finset.univ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.prod_const, Finset.card_univ] at h
  dsimp [q] at h
  linarith

theorem pool_failure_exp (b : U → Bool) (hb : (retained b).Nonempty) (C s : ℕ) :
    (poolLaw C s).prob {rows | ¬ Successful b C s rows} ≤
      (s : ℝ) * Real.exp (-(C : ℝ) / Fintype.card U) := by
  apply (pool_failure_le b hb C s).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s)
  rw [← first_failure b hb]
  exact first_failure_exp b hb C

theorem close_of_mass_domination {A : Type*} [Fintype A]
    (μ ν : Law A) (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (h : ∀ a, α * ν.mass a ≤ μ.mass a) : Law.Close μ ν (1 - α) := by
  classical
  apply Law.close_of_one_sided
  intro E
  have he : α * ν.prob Eᶜ ≤ μ.prob Eᶜ := by
    unfold Law.prob
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : a ∈ Eᶜ
    · simp only [ha, ↓reduceIte]
      exact h a
    · simp [ha]
  rw [Law.prob_compl, Law.prob_compl] at he
  have hp := mul_nonneg (sub_nonneg.mpr hα1) (ν.prob_nonneg E)
  nlinarith

theorem pool_uniform_close (b : U → Bool) (hb : (retained b).Nonempty)
    (root : U) (C s : ℕ) :
    Law.Close ((poolLaw C s).map (labels b root C s)) (tape (uniformRetained b hb) s)
      ((poolLaw C s).prob {rows | ¬ Successful b C s rows}) := by
  classical
  rw [pool_failure b hb]
  apply close_of_mass_domination
  · positivity [sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr (hitRate_le_one b))
      (by linarith [hitRate_nonneg b]) : (1 - hitRate b) ^ C ≤ 1)]
  · apply pow_le_one₀
    · exact sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr (hitRate_le_one b))
        (by linarith [hitRate_nonneg b]))
    · linarith [pow_nonneg (sub_nonneg.mpr (hitRate_le_one b)) C]
  · intro w
    calc
      _ = (poolLaw C s).prob
          {rows | Successful b C s rows ∧ labels b root C s rows = w} :=
        (pool_success_atom b hb root C s w).symm
      _ ≤ (poolLaw C s).prob {rows | labels b root C s rows = w} :=
        Law.prob_mono _ (fun rows hrows => hrows.2)
      _ = ((poolLaw C s).map (labels b root C s)).mass w := by
        rw [← CategoricalCoupling.probability_atom
          ((poolLaw C s).map (labels b root C s)) w]
        exact (Law.prob_map (poolLaw C s) (labels b root C s) {w}).symm

theorem centered_waiting_second (b : U → Bool) (hb : (retained b).Nonempty) (C : ℕ) :
    (tape (Law.uniform U) C).expect
      (fun w => (hitRate b * waiting b C w - (1 - (1 - hitRate b) ^ C)) ^ 2) ≤ 2 := by
  let μ := tape (Law.uniform U) C
  let m := 1 - (1 - hitRate b) ^ C
  have he (w : Fin C → U) :
      (hitRate b * waiting b C w - m) ^ 2 =
        (hitRate b * waiting b C w) ^ 2 -
          2 * m * (hitRate b * waiting b C w) + m ^ 2 := by ring
  change μ.expect (fun w => (hitRate b * waiting b C w - m) ^ 2) ≤ 2
  simp_rw [he, Law.expect_add, Law.expect_sub, Law.expect_const]
  have hm : μ.expect (fun w => hitRate b * waiting b C w) = m := waiting_mean b hb C
  rw [Law.expect_const_mul, hm]
  have hsecond := waiting_second_moment b hb C
  change μ.expect (fun w => (hitRate b * waiting b C w) ^ 2) ≤ 2 at hsecond
  nlinarith [sq_nonneg m]

/-- Finite, row-capped negative-binomial calibration. The cap introduces only a
logarithmic proposal overhead, and the sample size uses Chebyshev. -/
theorem calibration_concentration (b : U → Bool) (hb : (retained b).Nonempty)
    (C s : ℕ) (hs : 0 < s) (ε : ℝ) (hε : 0 < ε)
    (hcap : (1 - hitRate b) ^ C ≤ ε / 2) :
    (poolLaw C s).prob
      {rows | ε * s < |hitRate b * proposals b C s rows - s|} ≤
        8 / (ε ^ 2 * s) := by
  classical
  let μ := tape (Law.uniform U) C
  let m := 1 - (1 - hitRate b) ^ C
  let f := fun w : Fin C → U => hitRate b * waiting b C w - m
  have hf : μ.expect f = 0 := by
    rw [show f = (fun w => hitRate b * waiting b C w - m) from rfl,
      Law.expect_sub, Law.expect_const, waiting_mean b hb]
    simp [m]
  have hmoment : (poolLaw C s).expect (fun rows => (∑ j, f (rows j)) ^ 2) ≤ 2 * s := by
    rw [poolLaw, centered_sum_square μ f hf s]
    have h := mul_le_mul_of_nonneg_left (centered_waiting_second b hb C) (Nat.cast_nonneg s)
    simpa only [mul_comm] using h
  have hsum (rows : Fin s → Fin C → U) :
      (∑ j, f (rows j)) = hitRate b * proposals b C s rows - (s : ℝ) * m := by
    simp only [f, proposals, Nat.cast_sum, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hthreshold : 0 < (ε * s / 2) ^ 2 := sq_pos_of_pos (by positivity)
  have hsub : {rows | ε * s < |hitRate b * proposals b C s rows - s|} ⊆
      {rows | (ε * s / 2) ^ 2 ≤ (∑ j, f (rows j)) ^ 2} := by
    intro rows hrows
    change ε * s < |hitRate b * proposals b C s rows - s| at hrows
    change (ε * s / 2) ^ 2 ≤ (∑ j, f (rows j)) ^ 2
    have htri := abs_sub_le (hitRate b * proposals b C s rows) ((s : ℝ) * m) (s : ℝ)
    have hqs : |(s : ℝ) * m - s| = (s : ℝ) * (1 - hitRate b) ^ C := by
      have hq : 0 ≤ (1 - hitRate b) ^ C := pow_nonneg (sub_nonneg.mpr (hitRate_le_one b)) C
      dsimp [m]
      rw [show (s : ℝ) * (1 - (1 - hitRate b) ^ C) - s =
        -((s : ℝ) * (1 - hitRate b) ^ C) by ring, abs_neg, abs_of_nonneg (by positivity)]
    rw [hqs] at htri
    have hbias := mul_le_mul_of_nonneg_left hcap hsR.le
    have ha : ε * s / 2 ≤ |∑ j, f (rows j)| := by
      rw [hsum]
      nlinarith
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ ε * s / 2) ha 2
    simpa only [sq_abs] using hsq
  calc
    _ ≤ (poolLaw C s).prob {rows | (ε * s / 2) ^ 2 ≤ (∑ j, f (rows j)) ^ 2} :=
      Law.prob_mono _ hsub
    _ ≤ (poolLaw C s).expect (fun rows => (∑ j, f (rows j)) ^ 2) / (ε * s / 2) ^ 2 :=
      Law.markov _ (fun _ => sq_nonneg _) hthreshold
    _ ≤ (2 * s) / (ε * s / 2) ^ 2 :=
      div_le_div_of_nonneg_right hmoment hthreshold.le
    _ = _ := by field_simp; ring

end SteinerUpperBound.Covers.Rejection
