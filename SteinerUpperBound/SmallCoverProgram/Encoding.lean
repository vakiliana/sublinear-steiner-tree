module

public import SteinerUpperBound.SetSystem.Greedy
public import SteinerUpperBound.SetSystem.MappedForest

@[expose] public section

namespace SteinerUpperBound.SmallCoverProgram

open scoped Classical

variable {R U W : Type*} [Fintype U]

omit [Fintype U] in
theorem mapPorts_card_of_injOn (rows : R → Finset U) (f : U → W) (r : R)
    (hf : Set.InjOn f (rows r : Set U)) :
    (SetSystem.mapPorts rows f r).card = (rows r).card := by
  classical
  exact Finset.card_image_of_injOn hf

theorem claimed_support (rows : R → Finset U) (K : Finset U)
    (hrows : ∀ r, rows r ⊆ K) (S : Finset R) :
    SetSystem.claimed rows Finset.univ S ⊆ K := by
  intro x hx
  obtain ⟨r, _, hxr⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hx).2
  exact hrows r hxr

theorem claimed_image (rows : R → Finset U) (f : U → W) (B : Finset W)
    (hB : ∀ r, SetSystem.mapPorts rows f r ⊆ B) (S : Finset R) :
    (SetSystem.claimed rows Finset.univ S).image f =
      SetSystem.claimed (SetSystem.mapPorts rows f) B S := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨r, hrS, hxr⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hx).2
    have hrx : f x ∈ SetSystem.mapPorts rows f r :=
      (SetSystem.mem_mapPorts rows f r _).mpr ⟨x, hxr, rfl⟩
    exact Finset.mem_inter.mpr ⟨hB r hrx, Finset.mem_biUnion.mpr ⟨r, hrS, hrx⟩⟩
  · intro hy
    obtain ⟨r, hrS, hyr⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hy).2
    obtain ⟨x, hxr, hxy⟩ := (SetSystem.mem_mapPorts rows f r y).mp hyr
    exact Finset.mem_image.mpr ⟨x, Finset.mem_inter.mpr
      ⟨Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨r, hrS, hxr⟩⟩, hxy⟩

theorem claimed_card_rename (rows : R → Finset U) (K : Finset U)
    (hrows : ∀ r, rows r ⊆ K) (f : U → W) (hf : Set.InjOn f (K : Set U))
    (B : Finset W) (hB : ∀ r, SetSystem.mapPorts rows f r ⊆ B) (S : Finset R) :
    (SetSystem.claimed rows Finset.univ S).card =
      (SetSystem.claimed (SetSystem.mapPorts rows f) B S).card := by
  classical
  have hi : Set.InjOn f (SetSystem.claimed rows Finset.univ S : Set U) := by
    intro x hx y hy he
    exact hf (claimed_support rows K hrows S hx) (claimed_support rows K hrows S hy) he
  have hh := Finset.card_image_of_injOn hi
  rw [claimed_image rows f B hB S] at hh
  exact hh.symm

theorem fresh_card_rename (rows : R → Finset U) (K : Finset U)
    (hrows : ∀ r, rows r ⊆ K) (f : U → W) (hf : Set.InjOn f (K : Set U))
    (B : Finset W) (hB : ∀ r, SetSystem.mapPorts rows f r ⊆ B)
    (r : R) (S : Finset R) :
    (((Finset.univ : Finset U) ∩ rows r) \ SetSystem.claimed rows Finset.univ S).card =
      ((B ∩ SetSystem.mapPorts rows f r) \
        SetSystem.claimed (SetSystem.mapPorts rows f) B S).card := by
  classical
  apply Finset.card_bij (fun x _ => f x)
  · intro x hx
    obtain ⟨hxr, hxC⟩ := Finset.mem_sdiff.mp hx
    have hxrow := (Finset.mem_inter.mp hxr).2
    have hfx : f x ∈ SetSystem.mapPorts rows f r :=
      (SetSystem.mem_mapPorts rows f r _).mpr ⟨x, hxrow, rfl⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hB r hfx, hfx⟩, ?_⟩
    intro hm
    rw [← claimed_image rows f B hB S] at hm
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hm
    have hyx := hf (claimed_support rows K hrows S hy) (hrows r hxrow) he
    exact hxC (hyx ▸ hy)
  · intro x hx y hy he
    exact hf (hrows r (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx).1).2)
      (hrows r (Finset.mem_inter.mp (Finset.mem_sdiff.mp hy).1).2) he
  · intro y hy
    obtain ⟨hyr, hyC⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨x, hxr, hxy⟩ := (SetSystem.mem_mapPorts rows f r y).mp (Finset.mem_inter.mp hyr).2
    refine ⟨x, Finset.mem_sdiff.mpr
      ⟨Finset.mem_inter.mpr ⟨Finset.mem_univ _, hxr⟩, ?_⟩, hxy⟩
    intro hxC
    apply hyC
    rw [← claimed_image rows f B hB S]
    exact Finset.mem_image.mpr ⟨x, hxC, hxy⟩

theorem smallCoverAux_rename (rows : R → Finset U) (K : Finset U)
    (hrows : ∀ r, rows r ⊆ K) (f : U → W) (hf : Set.InjOn f (K : Set U))
    (B : Finset W) (hB : ∀ r, SetSystem.mapPorts rows f r ⊆ B)
    (order : List R) (S : Finset R) :
    SetSystem.smallCoverAux rows Finset.univ order S =
      SetSystem.smallCoverAux (SetSystem.mapPorts rows f) B order S := by
  classical
  induction order generalizing S with
  | nil => rfl
  | cons r l ih =>
      simp only [SetSystem.smallCoverAux]
      rw [← fresh_card_rename rows K hrows f hf B hB r S]
      split_ifs
      · exact ih _
      · exact ih _

theorem smallCoverEstimate_rename (E : Finset R) (rows : R → Finset U) (K : Finset U)
    (hrows : ∀ r, rows r ⊆ K) (f : U → W) (hf : Set.InjOn f (K : Set U))
    (B : Finset W) (hB : ∀ r, SetSystem.mapPorts rows f r ⊆ B) (order : List R) :
    SetSystem.smallCoverEstimate E rows Finset.univ order =
      SetSystem.smallCoverEstimate E (SetSystem.mapPorts rows f) B order := by
  have hs : SetSystem.smallCover E rows Finset.univ order =
      SetSystem.smallCover E (SetSystem.mapPorts rows f) B order :=
    smallCoverAux_rename rows K hrows f hf B hB _ _
  unfold SetSystem.smallCoverEstimate
  rw [← hs, claimed_card_rename rows K hrows f hf B hB]

end SteinerUpperBound.SmallCoverProgram
