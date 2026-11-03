module

public import SteinerUpperBound.FactoryEquivariance
public import SteinerUpperBound.Covers.Actual
public import SteinerUpperBound.Covers.Geometry.Projection
public import SteinerUpperBound.ComponentExplore.Scan

@[expose] public section

namespace SteinerUpperBound.LabelledMetricWorld

open SteinerLowerBound Covers
open scoped Classical

variable {V : Type*} {k : ℕ}

noncomputable local instance : DecidableEq (Fin (k + 1)) := Classical.decEq _
noncomputable local instance (I : Instance V) : DecidableEq (Terminal I) := Classical.decEq _

noncomputable def terminalEquiv (I : Instance V) (label : Vector V (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals) :
    Fin (k + 1) ≃ Terminal I :=
  Equiv.ofBijective
    (fun i => ⟨label.get i, hT ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), by
      intro x
      have hx : x.val ∈ Finset.univ.image label.get := hT.symm ▸ x.property
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
      exact ⟨i, Subtype.ext hi⟩⟩

theorem terminalEquiv_val (I : Instance V) (label : Vector V (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (i : Fin (k + 1)) : (terminalEquiv I label hinj hT i).val = label.get i := rfl

noncomputable def retainedLabels (label : Vector V (k + 1)) (b : Fin (k + 1) → Bool) : Finset V :=
  (CategoricalCoupling.selected b).image label.get

theorem actualBits_relabel (I : Instance V) (label : Vector V (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (r : ℝ) (root : Fin (k + 1)) (cap psi : ℕ) :
    (actualBits I r (terminalEquiv I label hinj hT root) cap psi).map
        (FactoryEquivariance.masks (terminalEquiv I label hinj hT)) =
      Factory.privateBits (fun x y => I.weight (Sym2.mk (label.get x) (label.get y)) ≤ r)
        root cap psi := by
  let e := terminalEquiv I label hinj hT
  letI : Nonempty (Terminal I) := ⟨e root⟩
  exact FactoryEquivariance.privateBits e _ (near I r)
    (fun x y => by simp only [near, e, terminalEquiv_val, Instance.weight_mk]) root cap psi

theorem retainedLabels_masks (I : Instance V) (label : Vector V (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (b : Terminal I → Bool) :
    retainedLabels label (FactoryEquivariance.masks (terminalEquiv I label hinj hT) b) =
      (CategoricalCoupling.selected b).image Subtype.val := by
  let e := terminalEquiv I label hinj hT
  letI : Nonempty (Terminal I) := ⟨e 0⟩
  have h := congrArg (fun S : Finset (Terminal I) => S.image Subtype.val)
    (FactoryEquivariance.selected_masks e b)
  rw [Finset.image_image] at h
  exact h

theorem retainedLabels_card (I : Instance V) (label : Vector V (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (b : Terminal I → Bool) :
    (retainedLabels label (FactoryEquivariance.masks (terminalEquiv I label hinj hT) b)).card =
      (CategoricalCoupling.selected b).card := by
  rw [retainedLabels_masks I label hinj hT b]
  exact Finset.card_image_iff.mpr (fun _ _ _ _ h => Subtype.ext h)

theorem retainedLabels_subset (I : Instance V) (label : Vector V (k + 1))
    (hT : Finset.univ.image label.get = I.terminals) (b : Fin (k + 1) → Bool) :
    retainedLabels label b ⊆ I.terminals := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact hT ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem coverOn_relabel (I : Instance V) (label : Vector V (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (rho : ℝ) (b : Terminal I → Bool) (hc : IsCover I rho b) :
    Geometry.CoverOn I I.terminals
      (retainedLabels label (FactoryEquivariance.masks (terminalEquiv I label hinj hT) b)) rho := by
  rw [retainedLabels_masks I label hinj hT b]
  intro x hx
  obtain ⟨y, hy, hd⟩ := hc ⟨x, hx⟩
  exact ⟨y.val, Finset.mem_image.mpr
    ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩, hd⟩

section Matrix

variable {n s : ℕ}

noncomputable local instance : DecidableEq (Fin n) := Classical.decEq _
noncomputable local instance : DecidableEq (Fin (s + 1)) := Classical.decEq _
noncomputable local instance : DecidableEq (LabelledFactory.Coordinate s k) := Classical.decEq _

theorem retained_key (label : Vector (Fin n) (k + 1)) (inverse : Vector (Fin (k + 1)) n)
    (hleft : ∀ j, inverse.get (label.get j) = j) (i : Fin (s + 1))
    (bits : LabelledFactory.Coordinate s k → Bool) :
    ComponentExplore.retained bits (LabelledFactory.key inverse i)
        (Finset.univ.image label.get) =
      retainedLabels label (fun j => bits (i, j)) := by
  ext x
  simp only [ComponentExplore.retained, retainedLabels, CategoricalCoupling.selected,
    Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨j, rfl⟩, hb⟩
    exact ⟨j, by simpa only [LabelledFactory.key, hleft] using hb, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, rfl⟩, by simpa only [LabelledFactory.key, hleft] using hj⟩

theorem factory_bits_actual_rows (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (radii : Vector ℝ (s + 1)) (root : Fin (k + 1)) (cap psi : ℕ) :
    OracleProgram.bits (LabelledFactory.config label radii cap psi) I.weight
        (LabelledFactory.initialCache root) =
      (Law.pi (fun i : Fin (s + 1) =>
        actualBits I (radii.get i) (terminalEquiv I label hinj hT root) cap psi)).map
          (fun masks q => masks q.1 (terminalEquiv I label hinj hT q.2)) := by
  let e := terminalEquiv I label hinj hT
  have hr :
      (Law.pi (fun i : Fin (s + 1) => actualBits I (radii.get i) (e root) cap psi)).map
          (fun masks i => FactoryEquivariance.masks e (masks i)) =
        Law.pi (fun i : Fin (s + 1) =>
          Factory.privateBits (LabelledFactory.rowRelation label radii I.weight i) root cap psi) := by
    rw [LawOperations.pi_map]
    congr 1
    funext i
    exact actualBits_relabel I label hinj hT (radii.get i) root cap psi
  rw [LabelledFactory.bits_eq_rows, ← hr, LawOperations.map_comp]
  rfl

end Matrix

end SteinerUpperBound.LabelledMetricWorld
