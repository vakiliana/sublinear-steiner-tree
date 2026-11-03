module

public import SteinerUpperBound.SetSystem.Rank

@[expose] public section

namespace SteinerUpperBound.SetSystem

open scoped Classical BigOperators

variable {V W : Type*}

noncomputable def pushCoordinates [Fintype V] (f : V → W) :
    (V → ℝ) →ₗ[ℝ] (W → ℝ) where
  toFun z := ∑ v, z v • Pi.single (f v) 1
  map_add' z t := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c z := by simp [Finset.smul_sum, smul_smul]

theorem pushCoordinates_single [Fintype V] (f : V → W) (x : V) :
    pushCoordinates f (Pi.single x 1) = Pi.single (f x) 1 := by
  classical
  simp [pushCoordinates, Pi.single_apply, eq_comm]

theorem pushCoordinates_delta [Fintype V] (f : V → W) (x y : V) :
    pushCoordinates f (GraphRank.delta x y) = GraphRank.delta (f x) (f y) := by
  simp only [GraphRank.delta, map_sub, pushCoordinates_single]

theorem pushCoordinates_injective [Fintype V] (f : V → W) (hf : Function.Injective f) :
    Function.Injective (pushCoordinates f) := by
  classical
  have happ (z : V → ℝ) (v : V) : pushCoordinates f z (f v) = z v := by
    simp [pushCoordinates, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, hf.eq_iff]
  intro z t he
  ext v
  have hh := congrFun he (f v)
  simpa only [happ] using hh

theorem space_map [Fintype V] (G : SimpleGraph V) (f : V → W) :
    (GraphRank.space G).map (pushCoordinates f) = GraphRank.space (G.map f) := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro z ⟨x, y, hxy, rfl⟩
    change pushCoordinates f (GraphRank.delta x y) ∈ GraphRank.space (G.map f)
    rw [pushCoordinates_delta]
    by_cases he : f x = f y
    · rw [he, GraphRank.delta_self]
      exact Submodule.zero_mem _
    · exact GraphRank.edge_mem _ (SimpleGraph.map_adj_apply' hxy he)
  · apply Submodule.span_le.mpr
    rintro z ⟨a, b, hab, rfl⟩
    obtain ⟨_, x, y, hxy, rfl, rfl⟩ := (SimpleGraph.map_adj' f G a b).mp hab
    exact Submodule.mem_map.mpr ⟨GraphRank.delta x y, GraphRank.edge_mem G hxy,
      pushCoordinates_delta f x y⟩

theorem rank_map_injective [Fintype V] (G : SimpleGraph V) (f : V → W)
    (hf : Function.Injective f) :
    GraphRank.rank (G.map f) = GraphRank.rank G := by
  have he := (Submodule.equivMapOfInjective (pushCoordinates f)
    (pushCoordinates_injective f hf) (GraphRank.space G)).finrank_eq
  rw [space_map] at he
  exact he.symm

theorem edgeCount_map_injective (G : SimpleGraph V)
    (f : V → W) (hf : Function.Injective f) :
    Nat.card (G.map f).edgeSet = Nat.card G.edgeSet := by
  classical
  let e : V ↪ W := ⟨f, hf⟩
  have he : (G.map f).edgeSet = e.sym2Map '' G.edgeSet := SimpleGraph.edgeSet_map e G
  rw [he]
  exact (Nat.card_congr (Equiv.Set.image e.sym2Map G.edgeSet e.sym2Map.injective)).symm

end SteinerUpperBound.SetSystem
