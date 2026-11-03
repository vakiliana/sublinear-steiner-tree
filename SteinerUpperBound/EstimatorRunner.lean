module

public import SteinerUpperBound.EstimatorBudget
public import SteinerUpperBound.QueryProgram.Postprocess

@[expose] public section

noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace SteinerUpperBound.EstimatorRunner

open SteinerLowerBound QueryProgram EstimatorParameters
open scoped Classical

variable {n k : ℕ}

abbrev FrontendFamily (n k : ℕ) := ℕ → ℕ → EstimatorBootstrap.Frontend n k

def outerFactor (frontendFactor exponent : ℕ) : ℕ :=
  4 * (EstimatorBootstrap.preparedFactor + 25600000 * (frontendFactor + 1)) + 5 +
    Setup.setupFactor + 2 * exponent + 383

def budget (n count savingFactor frontendFactor exponent : ℕ) : EstimatorBudget.PublicBudget :=
  EstimatorBudget.canonical n count savingFactor frontendFactor (outerFactor frontendFactor exponent) exponent

def raw (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (savingFactor frontendFactor exponent : ℕ) (frontend : FrontendFamily n k) :
    Code (Sym2 (Fin n)) Empty ℝ :=
  (EstimatorBudget.program n (k + 1) savingFactor frontendFactor
    (outerFactor frontendFactor exponent) exponent).bind (fun b =>
      EstimatorBootstrap.program label root b.factory.clock.workBudget b.factory.clock.disclosureBudget
        (frontend b.savingWork b.savingPositive))

def program (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (savingFactor frontendFactor exponent : ℕ) (frontend : FrontendFamily n k) :
    Code (Sym2 (Fin n)) Empty ℝ :=
  (raw label root savingFactor frontendFactor exponent frontend).capDefault
    (budget n (k + 1) savingFactor frontendFactor exponent).outer 0

theorem scale_ge_one (n exponent : ℕ) :
    1 ≤ (n + 1) * t n * ell n ^ (exponent + 142) := by
  have hp : 0 < (n + 1) * t n * ell n ^ (exponent + 142) := by positivity [t_pos n, ell_pos n]
  exact hp

theorem raw_expected_work (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (hinj : Function.Injective label.get) (savingFactor frontendFactor exponent : ℕ)
    (frontend : FrontendFamily n k) (m : Sym2 (Fin n) → ℝ) :
    (raw label root savingFactor frontendFactor exponent frontend).evaluate m Code.emptyBits
        (fun o => (o.work : ℝ)) ≤
      (outerFactor frontendFactor exponent * (n + 1) * t n * ell n ^ (exponent + 142) : ℕ) := by
  let X := (n + 1) * t n * ell n ^ (exponent + 142)
  let b := budget n (k + 1) savingFactor frontendFactor exponent
  have hcount := PublicTerminals.length_le label hinj
  have hbody := EstimatorBootstrap.program_expected_work_factory_polylog label root
    (frontend b.savingWork b.savingPositive) hcount frontendFactor (exponent + 140)
    b.frontendWork b.frontendPositive (le_refl _) (le_refl _) m
  have hpow : exponent + 140 + 2 = exponent + 142 := by omega
  simp only [hpow] at hbody
  have hX := scale_ge_one n exponent
  have heX : ell n ≤ X := by
    calc
      ell n = 1 * ell n := by omega
      _ ≤ (n + 1) * t n * ell n ^ (exponent + 142) :=
        Nat.mul_le_mul (Nat.mul_pos (Nat.succ_pos n) (t_pos n))
          (by simpa only [pow_one] using ell_power_le n 1 (exponent + 142) (by omega))
  have hsetup : (Setup.setupPlan n (k + 1)).work + 2 * exponent + 383 ≤
      (Setup.setupFactor + 2 * exponent + 383) * X := by
    have hs := (Setup.setupPlan_work_le n (k + 1)).trans (Setup.workBudget_polylog n)
    have he := Nat.mul_le_mul_left Setup.setupFactor heX
    have ht : 2 * exponent + 383 ≤ (2 * exponent + 383) * X := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 * exponent + 383) hX
    calc
      _ ≤ Setup.setupFactor * ell n + (2 * exponent + 383) := by
        simpa only [Nat.add_assoc] using Nat.add_le_add_right hs (2 * exponent + 383)
      _ ≤ Setup.setupFactor * X + (2 * exponent + 383) * X := Nat.add_le_add he ht
      _ = _ := by simp only [Nat.add_mul, Nat.add_assoc]
  rw [raw, Code.evaluate_work_bind, EstimatorBudget.program_evaluates]
  change (((EstimatorBudget.result n (k + 1) savingFactor frontendFactor
      (outerFactor frontendFactor exponent) exponent).work : ℕ) : ℝ) +
    (EstimatorBootstrap.program label root b.factory.clock.workBudget b.factory.clock.disclosureBudget
      (frontend b.savingWork b.savingPositive)).evaluate m Code.emptyBits (fun o => (o.work : ℝ)) ≤ _
  have hs : (((EstimatorBudget.result n (k + 1) savingFactor frontendFactor
      (outerFactor frontendFactor exponent) exponent).work : ℕ) : ℝ) ≤
      ((Setup.setupFactor + 2 * exponent + 383) * X : ℕ) := by
    change (((Setup.setupPlan n (k + 1)).work + 2 * exponent + 383 : ℕ) : ℝ) ≤ _
    exact Nat.cast_le.mpr hsetup
  have hb : (EstimatorBootstrap.program label root b.factory.clock.workBudget b.factory.clock.disclosureBudget
      (frontend b.savingWork b.savingPositive)).evaluate m Code.emptyBits (fun o => (o.work : ℝ)) ≤
      ((4 * (EstimatorBootstrap.preparedFactor + 25600000 * (frontendFactor + 1)) + 5) * X : ℕ) := by
    have hbf : b.factory = EstimatorClocks.factory (k + 1) b.frontendWork b.frontendPositive :=
      EstimatorBudget.canonical_factory n (k + 1) savingFactor frontendFactor
        (outerFactor frontendFactor exponent) exponent
    rw [hbf]
    simpa only [X, Nat.mul_assoc] using hbody
  have hc := add_le_add hs hb
  convert hc using 1 <;> simp only [outerFactor, X, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] <;> ring

theorem program_success (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (hinj : Function.Injective label.get) (savingFactor frontendFactor exponent : ℕ)
    (frontend : FrontendFamily n k) (m : Sym2 (Fin n) → ℝ) (P : ℝ → Prop) :
    Code.valueProbability m Code.emptyBits (raw label root savingFactor frontendFactor exponent frontend) P -
        1 / 100 ≤
      Code.valueProbability m Code.emptyBits (program label root savingFactor frontendFactor exponent frontend) P := by
  have hw := raw_expected_work label root hinj savingFactor frontendFactor exponent frontend m
  have hc := Code.capDefault_success m Code.emptyBits
    (raw label root savingFactor frontendFactor exponent frontend)
    (budget n (k + 1) savingFactor frontendFactor exponent).outer 0 P
  have hd : (raw label root savingFactor frontendFactor exponent frontend).evaluate m Code.emptyBits
      (fun o => (o.work : ℝ)) /
        ((budget n (k + 1) savingFactor frontendFactor exponent).outer + 1 : ℕ) ≤ 1 / 100 := by
    apply (div_le_div_of_nonneg_right hw (by positivity)).trans
    exact EstimatorClocks.amplified_ratio 100
      (outerFactor frontendFactor exponent * (n + 1) * t n * ell n ^ (exponent + 142)) (by decide)
  exact (sub_le_sub_left hd _).trans hc

theorem program_resources (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (savingFactor frontendFactor exponent : ℕ) (frontend : FrontendFamily n k) (m : Sym2 (Fin n) → ℝ)
    (s : ((program label root savingFactor frontendFactor exponent frontend).compile m).Seed) :
    let o := (((program label root savingFactor frontendFactor exponent frontend).compile m).tree s).output Code.emptyBits
    o.work ≤ (budget n (k + 1) savingFactor frontendFactor exponent).outer + 1 ∧
      o.metricQueries ≤ (budget n (k + 1) savingFactor frontendFactor exponent).outer ∧
      o.retentionQueries = 0 := by
  have h := Code.capDefault_resources m Code.emptyBits
    (raw label root savingFactor frontendFactor exponent frontend)
    (budget n (k + 1) savingFactor frontendFactor exponent).outer 0 s
  exact ⟨h.1, h.2, Code.empty_retention m _ s⟩

theorem resource_bound (n count savingFactor frontendFactor exponent : ℕ) :
    (budget n count savingFactor frontendFactor exponent).outer + 1 ≤
      (100 * outerFactor frontendFactor exponent + 101) * (n + 1) * t n * ell n ^ (exponent + 142) := by
  have h := scale_ge_one n exponent
  dsimp only [budget, EstimatorBudget.canonical]
  nlinarith

end SteinerUpperBound.EstimatorRunner
