module

public import SteinerUpperBound.SetSystem.MapRank

@[expose] public section

namespace SteinerUpperBound.SavingSoundness

open scoped Classical

variable {U W : Type*}

theorem rank_map_eq_of_injOn_support [Fintype U] (F : SimpleGraph U) (f : U → W)
    (hf : Set.InjOn f F.support) :
    GraphRank.rank (F.map f) = GraphRank.rank F := by
  classical
  let H := F.induce F.support
  have hmap : H.map Subtype.val = F := by
    ext x y
    constructor
    · intro h
      obtain ⟨_, a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj' _ _ x y).mp h
      exact hab
    · intro h
      have hx : x ∈ F.support := ⟨y, h⟩
      have hy : y ∈ F.support := ⟨x, h.symm⟩
      exact (SimpleGraph.map_adj' _ _ x y).mpr
        ⟨h.ne, ⟨x, hx⟩, ⟨y, hy⟩, h, rfl, rfl⟩
  have hinj : Function.Injective (fun x : F.support => f x.val) := by
    intro x y he
    exact Subtype.ext (hf x.property y.property he)
  have hr := SetSystem.rank_map_injective H (fun x : F.support => f x.val) hinj
  have hr' := SetSystem.rank_map_injective H Subtype.val Subtype.val_injective
  rw [hmap] at hr'
  have he : F.map f = H.map (fun x : F.support => f x.val) := by
    calc
      _ = (H.map Subtype.val).map f :=
        congrArg (fun G : SimpleGraph U => G.map f) hmap.symm
      _ = _ := SimpleGraph.map_map _ _ _
  rw [he]
  exact hr.trans hr'.symm

end SteinerUpperBound.SavingSoundness
