module

public import SteinerUpperBound.Structural.CoreConstructions

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}
variable {S : TreeGeometry.TreeSolution I}

noncomputable abbrev d0 : ℝ := 2 * delta0 / b0

theorem Fan.short_parent_scaled {parent v : ↥S.vertices} (F : Fan S parent v)
    (hred : Reduced S) (hshort : I.distance parent v < delta0 * F.pair.totalLength) :
    I.distance parent v < d0 * F.pair.ell := by
  have hr := F.pair.total_le_ell hred
  calc
    _ < delta0 * F.pair.totalLength := hshort
    _ ≤ delta0 * (2 * F.pair.ell / b0) :=
      mul_le_mul_of_nonneg_left hr (by norm_num [delta0])
    _ = _ := by unfold d0; ring

theorem star_of_one_short_parent {parent v : ↥S.vertices} (F : Fan S parent v)
    (L : Limb S parent) (hst : L.stem ≠ v) (hred : Reduced S)
    (hshort : I.distance parent v < delta0 * F.pair.totalLength) :
    Nonempty (ShortStar S) := by
  let B := CoreFrame.oneFan F L hst
  let ell := F.pair.ell
  have hell : 0 < ell := F.pair.ell_pos
  have hshort' := F.short_parent_scaled hred hshort
  have hcore : GraphCost.cost I.weight B.core ≤ I.distance parent v :=
    TreeGeometry.cost_single_edge_le I parent v
  have hport := B.port_distance_le 0 2
  have hbar := B.port_barrier hred (i := 0) (j := 2) (by decide)
  change I.distance F.left.primary L.primary ≤
    F.left.length + GraphCost.cost I.weight B.core + L.length at hport
  change p * F.left.length < I.distance F.left.primary L.primary at hbar
  have hmin : ell ≤ F.left.length := min_le_left _ _
  have hmin' : ell ≤ F.right.length := min_le_right _ _
  have hmul := mul_le_mul_of_nonneg_left hmin (show 0 ≤ b0 by norm_num [b0, p, chi, e0])
  have hcost : GraphCost.cost I.weight B.core ≤ theta0 * min ell L.length := by
    by_cases h : ell ≤ L.length
    · rw [min_eq_left h]
      norm_num [d0, delta0, b0, p, chi, e0, theta0] at hshort' hmul hbar ⊢
      nlinarith
    · rw [min_eq_right (le_of_not_ge h)]
      norm_num [d0, delta0, b0, p, chi, e0, theta0] at hshort' hmul hbar ⊢
      nlinarith
  apply B.short_star (min ell L.length) _ hcost
  intro i
  fin_cases i
  · exact (min_le_left _ _).trans hmin
  · exact (min_le_left _ _).trans hmin'
  · exact min_le_right _ _

theorem star_of_two_short_parents_ordered {parent v w : ↥S.vertices}
    (F : Fan S parent v) (H : Fan S parent w) (hvw : v ≠ w)
    (hred : Reduced S)
    (hshortF : I.distance parent v < delta0 * F.pair.totalLength)
    (hshortH : I.distance parent w < delta0 * H.pair.totalLength)
    (horder : F.pair.ell ≤ H.pair.ell) : Nonempty (ShortStar S) := by
  let B := CoreFrame.twoFans F H hvw
  let ell₁ := F.pair.ell
  let ell₂ := H.pair.ell
  have hell₁ : 0 < ell₁ := F.pair.ell_pos
  have hs₁ := F.short_parent_scaled hred hshortF
  have hs₂ := H.short_parent_scaled hred hshortH
  have hcore : GraphCost.cost I.weight B.core ≤ I.distance parent v + I.distance parent w := by
    exact (TreeGeometry.cost_sup_le I.weight _ _ I.weight_nonneg).trans
      (add_le_add (TreeGeometry.cost_single_edge_le I parent v)
        (TreeGeometry.cost_single_edge_le I parent w))
  have hport := B.port_distance_le 2 0
  have hbar := B.port_barrier hred (i := 2) (j := 0) (by decide)
  change I.distance H.left.primary F.left.primary ≤
    H.left.length + GraphCost.cost I.weight B.core + F.left.length at hport
  change p * H.left.length < I.distance H.left.primary F.left.primary at hbar
  have hmin₂ : ell₂ ≤ H.left.length := min_le_left _ _
  have hmul := mul_le_mul_of_nonneg_left hmin₂ (show 0 ≤ b0 by norm_num [b0, p, chi, e0])
  have hmax := (F.pair.lengths_le_ell hred).1
  have hcost : GraphCost.cost I.weight B.core ≤ theta0 * ell₁ := by
    norm_num [d0, delta0, b0, p, chi, e0, theta0] at hs₁ hs₂ hmul hmax hbar ⊢
    nlinarith
  apply B.short_star ell₁ _ hcost
  intro i
  fin_cases i
  · exact min_le_left _ _
  · exact min_le_right _ _
  · exact horder.trans hmin₂

theorem star_of_two_short_parents {parent v w : ↥S.vertices}
    (F : Fan S parent v) (H : Fan S parent w) (hvw : v ≠ w)
    (hred : Reduced S)
    (hshortF : I.distance parent v < delta0 * F.pair.totalLength)
    (hshortH : I.distance parent w < delta0 * H.pair.totalLength) :
    Nonempty (ShortStar S) := by
  by_cases horder : F.pair.ell ≤ H.pair.ell
  · exact star_of_two_short_parents_ordered F H hvw hred hshortF hshortH horder
  · exact star_of_two_short_parents_ordered H F (Ne.symm hvw) hred hshortH hshortF (le_of_not_ge horder)

end SteinerUpperBound.Structural.Tree
