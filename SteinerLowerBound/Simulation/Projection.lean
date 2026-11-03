module

public import SteinerLowerBound.Simulation.StopAgreement

@[expose] public section

namespace SteinerLowerBound.Simulation.Public

open HardDistribution
open MetricComparison.Public

variable {S G I C Z V : Type*}
  [Fintype S] [Fintype G] [Fintype I] [Fintype C]

def observable {d : ℕ} (r : SimReport S G I C Z d) :
    Z × List (Queries S G I C × Reply) :=
  (r.result, r.transcript.map (fun qa => (encode qa.1, qa.2)))

noncomputable def projectedTree (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (D t R : ℕ)
    (algorithm : DecisionTree (Queries S G I C) Reply Z)
    (f : Z × List (Queries S G I C × Reply) → V) :
    DecisionTree (Candidate S C d) Bool V :=
  (tree π d F D t R algorithm).map (fun r => f (observable r))

noncomputable def outputTree (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (D t R : ℕ)
    (algorithm : DecisionTree (Queries S G I C) Reply Z) :
    DecisionTree (Candidate S C d) Bool Z :=
  projectedTree π d F D t R algorithm Prod.fst

noncomputable def haltTree (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (D t R : ℕ)
    (algorithm : DecisionTree (Queries S G I C) Reply Z) :
    DecisionTree (Candidate S C d) Bool (Option Halt) :=
  (tree π d F D t R algorithm).map (fun r => r.state.stop)

theorem projectedTree_valid (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (D t R : ℕ)
    (algorithm : DecisionTree (Queries S G I C) Reply Z)
    (f : Z × List (Queries S G I C × Reply) → V) :
    Protocol.Valid (VisibleMass.region d F) (fun Q => Q.card ≤ 2 * R) ∅
      (projectedTree π d F D t R algorithm f) :=
  valid_map _ _ _ _ (tree_valid π d F D t R algorithm) _

theorem projectedTree_valid_real (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (D t R : ℕ)
    (algorithm : DecisionTree (Queries S G I C) Reply Z)
    (f : Z × List (Queries S G I C × Reply) → V) :
    Protocol.Valid (VisibleMass.region d F) (fun Q => (Q.card : ℝ) ≤ 2 * (R : ℝ)) ∅
      (projectedTree π d F D t R algorithm f) := by
  apply valid_mono_cap _ _ _ _ _ (projectedTree_valid π d F D t R algorithm f)
  intro Q hQ
  exact_mod_cast hQ

theorem haltTree_valid_real (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (D t R : ℕ)
    (algorithm : DecisionTree (Queries S G I C) Reply Z) :
    Protocol.Valid (VisibleMass.region d F) (fun Q => (Q.card : ℝ) ≤ 2 * (R : ℝ)) ∅
      (haltTree π d F D t R algorithm) := by
  apply valid_mono_cap _ _ _ _ _ (valid_map _ _ _ _ (tree_valid π d F D t R algorithm) _)
  intro Q hQ
  exact_mod_cast hQ

theorem haltTree_overflow (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (D t R : ℕ)
    (algorithm : DecisionTree (Queries S G I C) Reply Z) (o : Candidate S C d → Bool)
    (hstop : (haltTree π d F D t R algorithm).output o = some .closure) :
    R < d * retainedRead (haltTree π d F D t R algorithm) o := by
  rw [haltTree, retainedRead_map]
  apply tree_overflow_retained π d F D t R algorithm o
  simpa only [haltTree, DecisionTree.output_map] using hstop

end SteinerLowerBound.Simulation.Public
