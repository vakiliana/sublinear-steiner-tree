module

public import SteinerUpperBound.EstimatorFrontend
public import SteinerUpperBound.EstimatorRunner
public import SteinerUpperBound.SavingEstimator.Clocked

@[expose] public section

noncomputable section

namespace SteinerUpperBound.ConcreteEstimator

open QueryProgram RuntimeGrids

variable {n k : ℕ}

def step (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (p : EstimatorParameters.PublicParameters) (inverse : Vector (Fin (k + 1)) n)
    (tables : Tables) (ordinary positive : ℕ) : EstimatorFrontend.Saving n k tables :=
  fun i cache => (BandEstimator.scaleProgram tables.coarse i.val).bind (fun a =>
    SavingEstimator.Clocked.fromParameters label root
      (RuntimeWorld.coarseKey tables inverse i.val) a p ordinary positive cache)

def frontend (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (ordinary positive : ℕ) : EstimatorBootstrap.Frontend n k :=
  fun p inverse tables cache =>
    EstimatorFrontend.program p label root tables inverse
      (step label root p inverse tables ordinary positive) cache

def family (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) :
    EstimatorRunner.FrontendFamily n k :=
  frontend label root

def program (savingFactor frontendFactor exponent : ℕ) :
    {length : ℕ} → Vector (Fin n) length → Code (Sym2 (Fin n)) Empty ℝ
  | 0, _ => .pure 0
  | 1, _ => .pure 0
  | j + 2, label =>
      EstimatorRunner.program label (0 : Fin (j + 2)) savingFactor frontendFactor exponent
        (family label 0)

end SteinerUpperBound.ConcreteEstimator
