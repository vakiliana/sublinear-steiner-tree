module

public import SteinerUpperBound.EstimatorParameters.Setup.Language
public import SteinerUpperBound.LargeCoverProgram.Concrete
public import SteinerUpperBound.LargeCoverProgram.CausalCache

@[expose] public section

namespace SteinerUpperBound.SavingEstimator

open SteinerLowerBound QueryProgram EstimatorParameters
open scoped Classical

def configuration (n count : ℕ) (p : PublicParameters) : LargeCoverProgram.Parameters :=
  let l := Nat.log2 (512 * p.threshold * p.confidenceDenominator) + 2
  let m := Nat.log2 (128 * (n + 1) * p.threshold * p.confidenceDenominator) + 2
  let pool := ReusableSample.integerSamples p.threshold l m
  let rowCap := count * (Nat.log2 (16 * pool * p.confidenceDenominator + 1) + 1)
  let proposals := p.savingSamples * p.savingProposalCap
  ⟨p.threshold, l, m, p.smallCutoff, 1 / (1000000000 * (p.coarseMass : ℚ)),
    1 / (p.savingAccuracyDenominator : ℚ), p.savingSamples, p.savingProposalCap,
    proposals, rowCap, pool * rowCap, p.savingSamples, p.savingProposalCap, proposals⟩

def configurationPlan (n count : ℕ) (p : PublicParameters) : Setup.Plan LargeCoverProgram.Parameters := do
  let t512 ← Setup.mul 512 p.threshold
  let arg1 ← Setup.mul t512 p.confidenceDenominator
  let log1 ← Setup.log arg1
  let l ← Setup.add log1 2
  let np ← Setup.add n 1
  let n128 ← Setup.mul 128 np
  let nt ← Setup.mul n128 p.threshold
  let arg2 ← Setup.mul nt p.confidenceDenominator
  let log2 ← Setup.log arg2
  let m ← Setup.add log2 2
  let pool0 ← Setup.mul t512 l
  let pool ← Setup.mul pool0 m
  let pool16 ← Setup.mul 16 pool
  let poolArg0 ← Setup.mul pool16 p.confidenceDenominator
  let poolArg ← Setup.add poolArg0 1
  let poolLog ← Setup.log poolArg
  let poolClock ← Setup.add poolLog 1
  let poolCap ← Setup.mul count poolClock
  let poolProposals ← Setup.mul pool poolCap
  let proposals ← Setup.mul p.savingSamples p.savingProposalCap
  pure ⟨p.threshold, l, m, p.smallCutoff, 1 / (1000000000 * (p.coarseMass : ℚ)),
    1 / (p.savingAccuracyDenominator : ℚ), p.savingSamples, p.savingProposalCap,
    proposals, poolCap, poolProposals, p.savingSamples, p.savingProposalCap, proposals⟩

theorem configurationPlan_value (n count : ℕ) (p : PublicParameters) :
    (configurationPlan n count p).value = configuration n count p := rfl

def configurationWork (n count : ℕ) (p : PublicParameters) : ℕ :=
  (configurationPlan n count p).work

def configure {M Q : Type*} (n count : ℕ) (p : PublicParameters) : Code M Q LargeCoverProgram.Parameters :=
  (configurationPlan n count p).program

theorem configure_evaluates {M Q : Type*} (m : M → ℝ) (bits : Q → Bool)
    (n count : ℕ) (p : PublicParameters) :
    Code.Evaluates m bits (configure n count p)
      ⟨configuration n count p, configurationWork n count p, 0, 0, 0⟩ :=
  Setup.Plan.evaluates m bits (configurationPlan n count p)

def poolClock (n : ℕ) : ℕ :=
  Nat.log2 (16 * NsPool n * betaDenom n + 1) + 1

def closed (n count : ℕ) : LargeCoverProgram.Parameters :=
  let samples := meanSamples n (xiSavingInv n)
  let rowCap := samplerCap n count (xiSavingInv n)
  let poolCap := count * poolClock n
  ⟨t n, Lbar n, Mbar n, B n, epsQ n, xiSavingQ n, samples, rowCap,
    samples * rowCap, poolCap, NsPool n * poolCap, samples, rowCap, samples * rowCap⟩

theorem configuration_public (n count : ℕ) :
    configuration n count (parameters n count) = closed n count := by
  simp only [configuration, closed, parameters, Lbar, Mbar, noiseK1, noiseK2, poolClock,
    NsPool, epsQ, epsInv, xiSavingQ, ReusableSample.integerSamples, Nat.cast_mul, Nat.cast_ofNat]

end SteinerUpperBound.SavingEstimator
