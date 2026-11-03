module

public import SteinerUpperBound.EstimatorFrontend.Analysis.World

@[expose] public section

namespace SteinerUpperBound.EstimatorFrontend.Analysis

open QueryProgram
open scoped Classical

private theorem complement {M Q Out : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q Out) (P : Out → Prop) :
    Code.valueProbability m bits p P + p.probability m bits {o | ¬ P o.value} = 1 := by
  unfold Code.valueProbability Code.probability
  rw [← Code.evaluate_add]
  calc
    _ = p.evaluate m bits (fun _ => 1) := by
      apply congrArg (p.evaluate m bits)
      funext o
      by_cases hp : P o.value <;> simp [hp]
    _ = _ := Code.evaluate_const _ _ _ _

theorem failure_of_success {M Q Out : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q Out) (P : Out → Prop) (delta : ℝ)
    (h : 1 - delta ≤ Code.valueProbability m bits p P) :
    p.probability m bits {o | ¬ P o.value} ≤ delta := by
  linarith [complement m bits p P]

theorem success_and_zero_failure {M Q Out : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q Out) (P C : Out → Prop) (delta : ℝ)
    (hP : p.probability m bits {o | ¬ P o.value} ≤ delta)
    (hC : p.probability m bits {o | ¬ C o.value} = 0) :
    1 - delta ≤ Code.valueProbability m bits p (fun r => P r ∧ C r) := by
  have hg := BandEstimator.success_of_failure m bits p P delta hP
  have he : Code.valueProbability m bits p P ≤
      Code.valueProbability m bits p (fun r => P r ∧ C r) +
        Code.valueProbability m bits p (fun r => ¬ C r) := by
    unfold Code.valueProbability
    rw [← Code.evaluate_add]
    apply Code.evaluate_mono
    intro o
    by_cases hp : P o.value <;> by_cases hc : C o.value <;> simp [hp, hc]
  have hz : Code.valueProbability m bits p (fun r => ¬ C r) = 0 := by
    rw [← hC]
    unfold Code.valueProbability Code.probability
    apply congrArg (p.evaluate m bits)
    funext o
    by_cases hc : C o.value <;> simp [hc]
  linarith

end SteinerUpperBound.EstimatorFrontend.Analysis
