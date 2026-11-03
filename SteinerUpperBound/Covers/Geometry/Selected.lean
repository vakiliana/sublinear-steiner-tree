module

public import SteinerUpperBound.Covers.Geometry.Projection
public import SteinerUpperBound.Covers.Independent

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry

open SteinerLowerBound
open scoped Classical

variable {V : Type*}

noncomputable def selectedTerminals (I : Instance V) (b : Terminal I → Bool) : Finset V :=
  (CategoricalCoupling.selected b).image Subtype.val

theorem selectedTerminals_subset (I : Instance V) (b : Terminal I → Bool) :
    selectedTerminals I b ⊆ I.terminals := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
  exact y.property

theorem selectedTerminals_card (I : Instance V) (b : Terminal I → Bool) :
    (selectedTerminals I b).card = (CategoricalCoupling.selected b).card :=
  Finset.card_image_of_injective _ Subtype.val_injective

theorem isCover_iff_coverOn (I : Instance V) (ρ : ℝ) (b : Terminal I → Bool) :
    IsCover I ρ b ↔ CoverOn I I.terminals (selectedTerminals I b) ρ := by
  classical
  constructor
  · intro hc x hx
    obtain ⟨y, hy, hd⟩ := hc ⟨x, hx⟩
    exact ⟨y.val, Finset.mem_image.mpr
      ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩, hd⟩
  · intro hc x
    obtain ⟨y, hy, hd⟩ := hc x.val x.property
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨z, (Finset.mem_filter.mp hz).2, hd⟩

end SteinerUpperBound.Covers.Geometry
