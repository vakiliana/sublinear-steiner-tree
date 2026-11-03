module

public import SteinerUpperBound.PublicTerminals
public import SteinerUpperBound.Covers.OracleProgram
public import SteinerUpperBound.Covers.Product

@[expose] public section

namespace SteinerUpperBound.LabelledFactory

open SteinerLowerBound QueryProgram
open scoped Classical

variable {n k s : ℕ}

abbrev Coordinate (s k : ℕ) := Fin (s + 1) × Fin (k + 1)

noncomputable local instance : DecidableEq (Fin (k + 1)) := Classical.decEq _
noncomputable local instance : DecidableEq (Fin (s + 1)) := Classical.decEq _
noncomputable local instance : DecidableEq (Coordinate s k) := Classical.decEq _

def config (label : Vector (Fin n) (k + 1)) (radii : Vector ℝ (s + 1)) (cap trials : ℕ) :
    Covers.OracleProgram.Config (Fin n) (Coordinate s k) k :=
  ⟨label.get, Prod.snd, fun q => radii.get q.1, fun _ => cap, fun _ => trials⟩

noncomputable def initialCache (root : Fin (k + 1)) : Cache (Coordinate s k) :=
  fun q => if q.2 = root then some true else none

def key (inverse : Vector (Fin (k + 1)) n) (i : Fin (s + 1)) (x : Fin n) : Coordinate s k :=
  (i, inverse.get x)

def natKey (inverse : Vector (Fin (k + 1)) n) (i : ℕ) (x : Fin n) : Coordinate s k :=
  (⟨i % (s + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩, inverse.get x)

theorem key_label (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get)
    (root : Fin (k + 1)) (i : Fin (s + 1)) (j : Fin (k + 1)) :
    key (PublicTerminals.inverseResult label root).value i (label.get j) = (i, j) := by
  simp only [key, PublicTerminals.inverse_left label hinj]

theorem natKey_label (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get)
    (root : Fin (k + 1)) (i : ℕ) (hi : i < s + 1) (j : Fin (k + 1)) :
    natKey (PublicTerminals.inverseResult label root).value i (label.get j) = (⟨i, hi⟩, j) := by
  simp only [natKey, Nat.mod_eq_of_lt hi, PublicTerminals.inverse_left label hinj]

theorem root_cached (root : Fin (k + 1)) (i : Fin (s + 1)) :
    initialCache (s := s) root (i, root) = some true := by simp [initialCache]

noncomputable def rowRelation (label : Vector (Fin n) (k + 1))
    (radii : Vector ℝ (s + 1)) (w : Sym2 (Fin n) → ℝ) (i : Fin (s + 1))
    (x y : Fin (k + 1)) : Prop :=
  w (Sym2.mk (label.get x) (label.get y)) ≤ radii.get i

theorem bits_eq_product (label : Vector (Fin n) (k + 1)) (radii : Vector ℝ (s + 1))
    (cap trials : ℕ) (root : Fin (k + 1)) (w : Sym2 (Fin n) → ℝ) :
    Covers.OracleProgram.bits (config label radii cap trials) w (initialCache root) =
      Law.pi (fun q : Coordinate s k =>
        Covers.Factory.forcedBitLaw (rowRelation label radii w q.1) root cap trials q.2) := by
  unfold Covers.OracleProgram.bits
  congr 1
  funext q
  by_cases h : q.2 = root <;>
    simp only [Covers.Factory.cachedKernel, initialCache, Covers.Factory.coordinateLaw,
      Covers.Factory.forcedBitLaw, h, ite_true, ite_false, config,
      Covers.OracleProgram.relation, rowRelation] <;> rfl

theorem bits_eq_rows (label : Vector (Fin n) (k + 1)) (radii : Vector ℝ (s + 1))
    (cap trials : ℕ) (root : Fin (k + 1)) (w : Sym2 (Fin n) → ℝ) :
    Covers.OracleProgram.bits (config label radii cap trials) w (initialCache root) =
      (Law.pi (fun i : Fin (s + 1) =>
        Covers.Factory.privateBits (rowRelation label radii w i) root cap trials)).map
          (Equiv.curry (Fin (s + 1)) (Fin (k + 1)) Bool).symm := by
  rw [bits_eq_product]
  exact (LawOperations.pi_uncurry (fun i j =>
    Covers.Factory.forcedBitLaw (rowRelation label radii w i) root cap trials j)).symm

end SteinerUpperBound.LabelledFactory
