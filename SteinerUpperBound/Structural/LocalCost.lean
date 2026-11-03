module

public import SteinerUpperBound.Structural.Statistics

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V]

noncomputable def centerMap (Y : Finset V) (v x : V) : V :=
  if x ∈ Y then v else x

theorem centerMap_idempotent (Y : Finset V) (v x : V) :
    centerMap Y v (centerMap Y v x) = centerMap Y v x := by
  classical
  by_cases hx : x ∈ Y <;> by_cases hv : v ∈ Y <;> simp [centerMap, hx, hv]

noncomputable def centerStar (Y : Finset V) (v : V) : SimpleGraph V :=
  GraphCost.parentGraph (centerMap Y v)

theorem centerStar_reachable (Y : Finset V) (v : V) {x : V} (hx : x ∈ Y) :
    (centerStar Y v).Reachable x v := by
  classical
  by_cases h : x = v
  · subst x
    exact SimpleGraph.Reachable.refl v
  · apply SimpleGraph.Adj.reachable
    exact (GraphCost.parent_adj _ _ _).mpr ⟨h, Or.inl (by simp [centerMap, hx])⟩

theorem centerStar_oneCenter (Y : Finset V) (v : V) : OneCenterNetwork Y (centerStar Y v) := by
  classical
  refine ⟨?_, {v}, by simp, ?_⟩
  · intro x hx y hy
    exact (centerStar_reachable Y v hx).trans (centerStar_reachable Y v hy).symm
  · intro x y hxy
    rcases (GraphCost.parent_adj _ _ _).mp hxy with ⟨hne, h | h⟩
    · have hx : x ∈ Y := by
        by_contra hx
        have he : x = y := by simpa [centerMap, hx] using h
        exact hne he
      have hyv : y = v := by simpa [centerMap, hx] using h.symm
      exact ⟨Finset.mem_union.mpr (Or.inl hx), by simp [hyv]⟩
    · have hy : y ∈ Y := by
        by_contra hy
        have he : y = x := by simpa [centerMap, hy] using h
        exact hne he.symm
      have hxv : x = v := by simpa [centerMap, hy] using h.symm
      exact ⟨by simp [hxv], Finset.mem_union.mpr (Or.inl hy)⟩

theorem centerStar_cost (I : Instance V) (Y : Finset V) (v : V) :
    GraphCost.cost I.weight (centerStar Y v) = ∑ x ∈ Y, I.distance v x := by
  classical
  rw [centerStar, GraphCost.parent_cost_sum _ _ (centerMap_idempotent Y v)]
  have hpoint (x : V) :
      GraphCost.parentContribution I.weight (centerMap Y v) x =
        if x ∈ Y then I.distance v x else 0 := by
    by_cases hx : x ∈ Y
    · by_cases hvx : v = x
      · simp [GraphCost.parentContribution, centerMap, hx, hvx, I.distance_self]
      · simp [GraphCost.parentContribution, centerMap, hx, hvx, I.distance_comm]
    · simp [GraphCost.parentContribution, centerMap, hx]
  simp_rw [hpoint]
  simpa only [Finset.univ_inter] using Finset.sum_ite_mem Finset.univ Y (I.distance v)

theorem localCost_star_le (I : Instance V) (Y : Finset V) (v : V) :
    localCost I Y ≤ ∑ x ∈ Y, I.distance v x := by
  exact (localCost_le I Y (centerStar Y v) (centerStar_oneCenter Y v)).trans_eq
    (centerStar_cost I Y v)

theorem localCost_pair_le (I : Instance V) (x y : V) :
    localCost I {x, y} ≤ I.distance x y := by
  classical
  apply (localCost_star_le I {x, y} x).trans
  by_cases h : x = y
  · simp [h, I.distance_self]
  · simp [Finset.sum_pair h, I.distance_self]

end SteinerUpperBound.Structural
