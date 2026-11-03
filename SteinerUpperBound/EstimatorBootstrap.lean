module

public import SteinerUpperBound.RuntimeWorld
public import SteinerUpperBound.FactoryExecution
public import SteinerUpperBound.EstimatorParameters.Setup.Correctness

@[expose] public section

noncomputable section

namespace SteinerUpperBound.EstimatorBootstrap

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

variable {n k : ℕ}

noncomputable local instance bootstrapVertexDecEq : DecidableEq (Fin n) := Classical.decEq _
noncomputable local instance bootstrapLabelDecEq : DecidableEq (Fin (k + 1)) := Classical.decEq _

abbrev Frontend (n k : ℕ) :=
  PublicParameters → Vector (Fin (k + 1)) n → (t : Tables) →
    Cache (RuntimeWorld.Coordinate t k) →
      Code (Sym2 (Fin n)) (RuntimeWorld.Coordinate t k) (Option ℝ)

def atTables (p : PublicParameters) (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (W D : ℕ) (frontend : Frontend n k) (inverse : Vector (Fin (k + 1)) n) (tables : Tables) :
    Code (Sym2 (Fin n)) Empty ℝ :=
  .tick ((k + 1) * (tables.coarse.intervals + tables.fine.intervals + 2) + 5)
    ((FactoryExecution.program (RuntimeWorld.configuration p label tables)
      (LabelledFactory.initialCache root) W D
      (frontend p inverse tables (LabelledFactory.initialCache root))).map
        (fun answer => answer.join.getD 0))

def atPhase (p : PublicParameters) (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (W D : ℕ) (frontend : Frontend n k) (inverse : Vector (Fin (k + 1)) n)
    (R : ℝ) (hR : 0 < R) (phase : Fin FinitePhase.count) : Code (Sym2 (Fin n)) Empty ℝ :=
  .tick 4 ((RuntimeGrids.program (k + 1) (by omega) R hR phase).bind
    (atTables p label root W D frontend inverse))

def prepared (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (W D : ℕ) (frontend : Frontend n k) (R : ℝ) (hR : 0 < R) :
    Code (Sym2 (Fin n)) Empty ℝ :=
  (setupProgram n (k + 1)).bind (fun p =>
    (PublicTerminals.inverseProgram label root).bind (fun inverse =>
      .uniform 999999 (atPhase p label root W D frontend inverse R hR)))

def program (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (W D : ℕ) (frontend : Frontend n k) : Code (Sym2 (Fin n)) Empty ℝ :=
  normalize (label.get root) label.toList (fun R _ =>
    if hR : 0 < R then prepared label root W D frontend R hR else .pure 0)

theorem atTables_probability (p : PublicParameters) (label : Vector (Fin n) (k + 1))
    (root : Fin (k + 1)) (W D : ℕ) (frontend : Frontend n k)
    (inverse : Vector (Fin (k + 1)) n) (tables : Tables)
    (m : Sym2 (Fin n) → ℝ) (P : ℝ → Prop) :
    Code.valueProbability m Code.emptyBits (atTables p label root W D frontend inverse tables) P =
      (FactoryExecution.program (RuntimeWorld.configuration p label tables)
        (LabelledFactory.initialCache root) W D
        (frontend p inverse tables (LabelledFactory.initialCache root))).evaluate m Code.emptyBits
          (fun o => if P (o.value.join.getD 0) then (1 : ℝ) else 0) := by
  unfold Code.valueProbability
  delta atTables
  rw [Code.evaluate, Code.evaluate_map]
  rfl

theorem prepared_value (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (W D : ℕ) (frontend : Frontend n k) (R : ℝ) (hR : 0 < R)
    (m : Sym2 (Fin n) → ℝ) (F : ℝ → ℝ) :
    (prepared label root W D frontend R hR).evaluate m Code.emptyBits (fun o => F o.value) =
      FinitePhase.law.expect (fun phase =>
        let tables := (RuntimeGrids.result (k + 1) (by omega) R hR phase).value
        (FactoryExecution.program
          (RuntimeWorld.configuration (parameters n (k + 1)) label tables)
          (LabelledFactory.initialCache root) W D
          (frontend (parameters n (k + 1)) (PublicTerminals.inverseResult label root).value
            tables (LabelledFactory.initialCache root))).evaluate m Code.emptyBits
              (fun o => F (o.value.join.getD 0))) := by
  rw [prepared, Code.evaluate_bind, setupProgram_evaluates]
  dsimp only [Outcome.combine]
  rw [Code.evaluate_bind, PublicTerminals.inverse_evaluates]
  dsimp only [Outcome.combine]
  change (Law.uniform (Fin FinitePhase.count)).expect _ = _
  apply congrArg (Law.uniform (Fin FinitePhase.count)).expect
  funext phase
  change Fin FinitePhase.count at phase
  delta atPhase
  rw [Code.evaluate, Code.evaluate_bind, RuntimeGrids.program_evaluates]
  delta atTables
  rw [Code.evaluate, Code.evaluate_map]
  rfl

theorem prepared_probability (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (W D : ℕ) (frontend : Frontend n k) (R : ℝ) (hR : 0 < R)
    (m : Sym2 (Fin n) → ℝ) (P : ℝ → Prop) :
    Code.valueProbability m Code.emptyBits (prepared label root W D frontend R hR) P =
      FinitePhase.law.expect (fun phase =>
        Code.valueProbability m Code.emptyBits
          (atTables (parameters n (k + 1)) label root W D frontend
            (PublicTerminals.inverseResult label root).value
            (RuntimeGrids.result (k + 1) (by omega) R hR phase).value) P) := by
  calc
    _ = _ := prepared_value label root W D frontend R hR m (fun r => if P r then (1 : ℝ) else 0)
    _ = _ := by
      apply congrArg FinitePhase.law.expect
      funext phase
      exact (atTables_probability _ _ _ _ _ _ _ _ _ _).symm

theorem program_value (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1)) (W D : ℕ) (frontend : Frontend n k)
    (F : ℝ → ℝ) :
    let R := rowValue I.weight (label.get root) label.toList 0
    let lam := floorScale label.toList.length R
    let hR := (RuntimeGeometry.observed_geometry I (label.get root) label.toList
      (PublicTerminals.toList_nodup label hinj)
      ((PublicTerminals.toList_toFinset label).trans hT)
      (hT ▸ Finset.mem_image.mpr ⟨root, Finset.mem_univ _, rfl⟩) hk).1
    (program label root W D frontend).evaluate I.weight Code.emptyBits (fun o => F o.value) =
      (prepared label root W D frontend R hR).evaluate
        (TreeGeometry.Flooring.floored I lam).weight Code.emptyBits (fun o => F o.value) := by
  dsimp only
  rw [program, normalize_value]
  simp only [dite_true, (RuntimeGeometry.observed_geometry I (label.get root) label.toList
    (PublicTerminals.toList_nodup label hinj)
    ((PublicTerminals.toList_toFinset label).trans hT)
    (hT ▸ Finset.mem_image.mpr ⟨root, Finset.mem_univ _, rfl⟩) hk).1]

end SteinerUpperBound.EstimatorBootstrap
