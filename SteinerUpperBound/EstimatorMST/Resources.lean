module

public import SteinerUpperBound.EstimatorMST.Program

@[expose] public section

namespace SteinerUpperBound.EstimatorMST

open SteinerLowerBound QueryProgram
open scoped Classical

def resourceSize (n : ℕ) : ℕ :=
  EstimatorParameters.publicFactor * EstimatorParameters.ell n ^ 9 + 16

def workFactor : ℕ := 300 * (EstimatorParameters.publicFactor + 16) ^ 4
def positiveFactor : ℕ := (EstimatorParameters.publicFactor + 16) ^ 3

theorem resourceSize_positive (n : ℕ) : 1 ≤ resourceSize n := by
  unfold resourceSize
  omega

theorem public_resource_sizes (n terminals : ℕ) :
    EstimatorParameters.BM n + 2 ≤ resourceSize n ∧
      samples n ≤ resourceSize n ∧
      EstimatorParameters.heightBudget n ≤ resourceSize n ∧
      proposals n terminals ≤ terminals * resourceSize n := by
  have hcore (x : ℕ) (hx : x ∈ EstimatorParameters.coreSizes n) :
      x ≤ EstimatorParameters.publicFactor * EstimatorParameters.ell n ^ 9 :=
    EstimatorParameters.all_core_polylog n x hx
  have hB := hcore (EstimatorParameters.xiMInv n) (by simp [EstimatorParameters.coreSizes])
  change EstimatorParameters.BM n ≤ _ at hB
  have hs := hcore (samples n) (by simp [samples, EstimatorParameters.coreSizes])
  have hh := hcore (EstimatorParameters.heightBudget n) (by simp [EstimatorParameters.coreSizes])
  refine ⟨by unfold resourceSize; omega, by unfold resourceSize; omega,
    by unfold resourceSize; omega, ?_⟩
  have he : EstimatorParameters.ell n ≤ EstimatorParameters.ell n ^ 9 := by
    simpa only [pow_one] using EstimatorParameters.ell_power_le n 1 9 (by decide)
  calc
    proposals n terminals ≤ EstimatorParameters.publicFactor * terminals * EstimatorParameters.ell n :=
      (EstimatorParameters.all_sampler_caps n terminals).2.2.1
    _ = terminals * (EstimatorParameters.publicFactor * EstimatorParameters.ell n) := by ring
    _ ≤ terminals * (EstimatorParameters.publicFactor * EstimatorParameters.ell n ^ 9) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ he)
    _ ≤ terminals * resourceSize n := Nat.mul_le_mul_left _ (by unfold resourceSize; omega)

theorem resourceSize_polylog (n : ℕ) :
    resourceSize n ≤ (EstimatorParameters.publicFactor + 16) * EstimatorParameters.ell n ^ 9 := by
  have hp : 1 ≤ EstimatorParameters.ell n ^ 9 :=
    Nat.succ_le_of_lt (pow_pos (EstimatorParameters.ell_pos n) 9)
  unfold resourceSize
  nlinarith

theorem natural_resource_bound (terminals B C count intervals n P : ℕ)
    (ht : terminals ≤ n) (hB : B + 2 ≤ P) (hC : C ≤ n * P)
    (hs : count ≤ P) (hi : intervals ≤ P) (hP : 1 ≤ P) :
    MSTApproximation.loopBudget terminals B C count (List.range intervals) + 16 ≤
        300 * (n + 1) * P ^ 4 ∧
      (B + 1) * count * intervals ≤ P ^ 3 := by
  have hp2 : P ≤ P ^ 2 := by nlinarith
  have hp3 : P ^ 2 ≤ P ^ 3 := by nlinarith
  let M := (n + 1) * P ^ 3
  have hPM : P ≤ M := by
    calc
      P ≤ P ^ 3 := hp2.trans hp3
      _ = 1 * P ^ 3 := by omega
      _ ≤ M := Nat.mul_le_mul_right _ (by omega)
  have hnP : n * P ^ 2 ≤ M := Nat.mul_le_mul (by omega) hp3
  have hM : 1 ≤ M := hP.trans hPM
  have hscale : MSTApproximation.scaleBudget terminals B C count ≤ 200 * M := by
    calc
      MSTApproximation.scaleBudget terminals B C count ≤
          16 * (P * (n * P) + P + 1) + (80 * (n + 1) * P ^ 2 + 7) * P + 17 := by
        have hsampler : 16 * (count * C + count + 1) ≤ 16 * (P * (n * P) + P + 1) := by
          gcongr
        have hexplorer : (80 * (terminals + 1) * (B + 2) ^ 2 + 7) * count ≤
            (80 * (n + 1) * P ^ 2 + 7) * P := by gcongr
        simpa only [MSTApproximation.scaleBudget, MSTApproximation.continuationBudget, Nat.add_assoc]
          using Nat.add_le_add hsampler (Nat.add_le_add_right hexplorer 17)
      _ = 80 * M + 16 * (n * P ^ 2) + 23 * P + 33 := by dsimp [M]; ring
      _ ≤ 200 * M := by omega
  constructor
  · have hloop := MSTApproximation.loopBudget_range_bound terminals B C count intervals P hi
    have hstep : MSTApproximation.scaleBudget terminals B C count + 2 * P + 13 ≤ 215 * M := by omega
    have hM4 : M * P = (n + 1) * P ^ 4 := by dsimp [M]; ring
    have hM4pos : 1 ≤ (n + 1) * P ^ 4 := by
      calc
        1 ≤ M := hM
        _ = M * 1 := by omega
        _ ≤ M * P := Nat.mul_le_mul_left _ hP
        _ = _ := hM4
    calc
      MSTApproximation.loopBudget terminals B C count (List.range intervals) + 16 ≤
          (MSTApproximation.scaleBudget terminals B C count + 2 * P + 13) * P + 16 :=
        Nat.add_le_add_right hloop _
      _ ≤ (215 * M) * P + 16 := Nat.add_le_add_right (Nat.mul_le_mul_right _ hstep) _
      _ = 215 * ((n + 1) * P ^ 4) + 16 := by rw [Nat.mul_assoc, hM4]
      _ ≤ 300 * (n + 1) * P ^ 4 := by nlinarith
  · calc
      (B + 1) * count * intervals ≤ P * P * P :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) hs) hi
      _ = P ^ 3 := by ring

variable {V Q : Type*} {k : ℕ}

theorem enumeration_length (e : Fin (k + 1) → V) (hinj : Function.Injective e)
    (l : List V) (hl : l.Nodup) (he : Finset.univ.image e = l.toFinset) :
    l.length = k + 1 := by
  classical
  have hc : l.toFinset.card = k + 1 := by
    rw [← he, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  simpa only [List.toFinset_card_of_nodup hl] using hc

variable [Fintype V]

/-- Exact expected resources of the existing sampler/explorer loop plus five
operations for the public-parameter frontend. No cover or statistical event is needed. -/
theorem expected_resources (I : Instance V) (bits : Q → Bool) (n : ℕ)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q) (g : MSTApproximation.Grid)
    (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct bits cache) (he : Finset.univ.image e = l.toFinset)
    (hr : ∀ i < g.intervals, bits (key i (e root)) = true) :
    (program n e key g l root cache).evaluate I.weight bits (fun o => (o.work : ℝ)) ≤
        (MSTApproximation.loopBudget l.length (EstimatorParameters.BM n) (proposals n (k + 1))
          (samples n) (List.range g.intervals) + 16 : ℕ) ∧
      (program n e key g l root cache).evaluate I.weight bits (fun o => (o.positiveReplies : ℝ)) ≤
        ((EstimatorParameters.BM n + 1) * samples n * g.intervals : ℕ) := by
  have h := MSTApproximation.frontend_expected_resources I bits e key g EstimatorParameters.nu (accuracy n)
    (EstimatorParameters.BM n) (proposals n (k + 1)) (samples n) l root cache hc he hr
  constructor
  · change (Code.tick 4 (MSTApproximation.frontend e key g EstimatorParameters.nu (accuracy n)
      (EstimatorParameters.BM n) (proposals n (k + 1)) (samples n) l root cache)).evaluate
        I.weight bits (fun o => (o.work : ℝ)) ≤ _
    rw [MSTApproximation.evaluate_tick_work]
    push_cast
    linarith [h.1]
  · change (Code.tick 4 (MSTApproximation.frontend e key g EstimatorParameters.nu (accuracy n)
      (EstimatorParameters.BM n) (proposals n (k + 1)) (samples n) l root cache)).evaluate
        I.weight bits (fun o => (o.positiveReplies : ℝ)) ≤ _
    rw [MSTApproximation.evaluate_tick_positive]
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h.2

theorem expected_resources_explicit (I : Instance V) (bits : Q → Bool) (n : ℕ)
    (e : Fin (k + 1) → V) (hinj : Function.Injective e) (key : ℕ → V → Q)
    (g : MSTApproximation.Grid) (l : List V) (hl : l.Nodup) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct bits cache) (he : Finset.univ.image e = l.toFinset)
    (hr : ∀ i < g.intervals, bits (key i (e root)) = true)
    (hkn : k + 1 ≤ n) (hh : g.intervals ≤ EstimatorParameters.heightBudget n) :
    (program n e key g l root cache).evaluate I.weight bits (fun o => (o.work : ℝ)) ≤
        (300 * (n + 1) * resourceSize n ^ 4 : ℕ) ∧
      (program n e key g l root cache).evaluate I.weight bits (fun o => (o.positiveReplies : ℝ)) ≤
        (resourceSize n ^ 3 : ℕ) := by
  obtain ⟨hB, hs, hheight, hC⟩ := public_resource_sizes n (k + 1)
  have hlN : l.length ≤ n := (enumeration_length e hinj l hl he).le.trans hkn
  have hCN : proposals n (k + 1) ≤ n * resourceSize n :=
    hC.trans (Nat.mul_le_mul_right _ hkn)
  have hb := natural_resource_bound l.length (EstimatorParameters.BM n) (proposals n (k + 1))
    (samples n) g.intervals n (resourceSize n) hlN hB hCN hs (hh.trans hheight)
      (resourceSize_positive n)
  have h := expected_resources I bits n e key g l root cache hc he hr
  exact ⟨h.1.trans (by exact_mod_cast hb.1), h.2.trans (by exact_mod_cast hb.2)⟩

/-- Absolute fixed factors and logarithmic exponents, derived from the actual
integer configuration rather than assumed work/positive-reply certificates. -/
theorem expected_resources_polylog (I : Instance V) (bits : Q → Bool) (n : ℕ)
    (e : Fin (k + 1) → V) (hinj : Function.Injective e) (key : ℕ → V → Q)
    (g : MSTApproximation.Grid) (l : List V) (hl : l.Nodup) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct bits cache) (he : Finset.univ.image e = l.toFinset)
    (hr : ∀ i < g.intervals, bits (key i (e root)) = true)
    (hkn : k + 1 ≤ n) (hh : g.intervals ≤ EstimatorParameters.heightBudget n) :
    (program n e key g l root cache).evaluate I.weight bits (fun o => (o.work : ℝ)) ≤
        (workFactor * (n + 1) * EstimatorParameters.ell n ^ 36 : ℕ) ∧
      (program n e key g l root cache).evaluate I.weight bits (fun o => (o.positiveReplies : ℝ)) ≤
        (positiveFactor * EstimatorParameters.ell n ^ 27 : ℕ) := by
  have h := expected_resources_explicit I bits n e hinj key g l hl root cache hc he hr hkn hh
  have hP := resourceSize_polylog n
  have hw : 300 * (n + 1) * resourceSize n ^ 4 ≤
      workFactor * (n + 1) * EstimatorParameters.ell n ^ 36 := by
    calc
      _ ≤ 300 * (n + 1) *
          ((EstimatorParameters.publicFactor + 16) * EstimatorParameters.ell n ^ 9) ^ 4 := by gcongr
      _ = _ := by unfold workFactor; ring
  have hp : resourceSize n ^ 3 ≤ positiveFactor * EstimatorParameters.ell n ^ 27 := by
    calc
      _ ≤ ((EstimatorParameters.publicFactor + 16) * EstimatorParameters.ell n ^ 9) ^ 3 := by gcongr
      _ = _ := by unfold positiveFactor; ring
  exact ⟨h.1.trans (by exact_mod_cast hw), h.2.trans (by exact_mod_cast hp)⟩

end SteinerUpperBound.EstimatorMST
