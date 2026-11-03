module

public import SteinerUpperBound.Structural.PromotionBounds

@[expose] public section

namespace SteinerUpperBound.Structural.Tree.Fan

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}
variable {S : TreeGeometry.TreeSolution I} {parent v : ↥S.vertices}

def RegularDatum (F : Fan S parent v) (a : ℝ) (D : Finset V) : Prop :=
  D ∈ components I a ∧ D ⊆ F.region ∧ sigma0 * a ≤ localAdvantage I D ∧
    F.promotionCharge < a ∧
    ∃ x ∈ D, ∃ y ∈ D, ∃ z ∈ D,
      ¬ (terminalGraph S).Reachable x y ∧
      ¬ (terminalGraph S).Reachable x z ∧ ¬ (terminalGraph S).Reachable y z

theorem regular_datum_of_left (F : Fan S parent v) (hred : Reduced S)
    (hparent : delta0 * F.pair.totalLength ≤ I.distance parent v)
    (C : Cherry S v) (hl : F.left = Limb.cherry C)
    (hlarge : alpha0 * (Limb.cherry C).length ≤ I.distance C.center C.primary)
    (a : ℝ) (hlo : F.pair.totalLength / (chi - 1) < a)
    (hhi : a ≤ omega * F.pair.totalLength / (chi - 1)) :
    ∃ D, RegularDatum F a D := by
  have hdisj : Disjoint (Limb.cherry C).region F.right.region := by
    simpa only [hl] using F.limbs_disjoint
  have hlo' : ((Limb.cherry C).length + F.right.length) / (chi - 1) < a := by
    simpa only [Fan.pair, LimbPair.totalLength, hl] using hlo
  have hhi' : a ≤ omega * ((Limb.cherry C).length + F.right.length) / (chi - 1) := by
    simpa only [Fan.pair, LimbPair.totalLength, hl] using hhi
  obtain ⟨D, hD, hY, hscore, hcharge⟩ :=
    cherry_local_evidence_explicit C F.right hdisj hred hlarge a hlo' hhi'
  have hxD : (C.primary : V) ∈ D := hY (by simp)
  have hyD : (C.secondary : V) ∈ D := hY (by simp)
  have hzD : (F.right.primary : V) ∈ D := hY (by simp)
  have hsub : D ⊆ F.region := by
    rw [component_eq_of_member I a hD hxD]
    simpa only [hl, Limb.primary] using F.regular_component_contained hred hparent a hhi
  have hcharge' : F.promotionCharge < a := by
    change F.left.longerArm + F.right.longerArm < a
    rw [hl]
    exact hcharge
  obtain ⟨hxy, hxz, hyz⟩ := cherry_permanent_separated C F.right hdisj
  exact ⟨D, hD, hsub, hscore, hcharge', C.primary, hxD, C.secondary, hyD,
    F.right.primary, hzD, hxy, hxz, hyz⟩

theorem regular_datum (F : Fan S parent v) (hred : Reduced S) (hnot : ¬ F.Small)
    (hparent : delta0 * F.pair.totalLength ≤ I.distance parent v)
    (a : ℝ) (hlo : F.pair.totalLength / (chi - 1) < a)
    (hhi : a ≤ omega * F.pair.totalLength / (chi - 1)) :
    ∃ D, RegularDatum F a D := by
  by_cases hleft : F.left.Small
  · have hright : ¬ F.right.Small := fun h => hnot ⟨hleft, h⟩
    cases hr : F.right with
    | direct x hv hx h => exact False.elim (hright (by rw [hr]; trivial))
    | cherry C =>
      have hlarge : alpha0 * (Limb.cherry C).length ≤ I.distance C.center C.primary := by
        have hbad : ¬ I.distance C.center C.primary < alpha0 * (Limb.cherry C).length := by
          simpa only [hr, Limb.Small] using hright
        exact le_of_not_gt hbad
      have hpSwap : delta0 * F.swap.pair.totalLength ≤ I.distance parent v := by
        simpa only [Fan.pair, LimbPair.totalLength, Fan.swap, add_comm] using hparent
      have hloSwap : F.swap.pair.totalLength / (chi - 1) < a := by
        simpa only [Fan.pair, LimbPair.totalLength, Fan.swap, add_comm] using hlo
      have hhiSwap : a ≤ omega * F.swap.pair.totalLength / (chi - 1) := by
        simpa only [Fan.pair, LimbPair.totalLength, Fan.swap, add_comm] using hhi
      obtain ⟨D, hD, hsub, hscore, hcharge, htriple⟩ :=
        F.swap.regular_datum_of_left hred hpSwap C hr hlarge a hloSwap hhiSwap
      refine ⟨D, hD, hsub, hscore, ?_, htriple⟩
      change F.left.longerArm + F.right.longerArm < a
      change F.right.longerArm + F.left.longerArm < a at hcharge
      linarith
  · cases hl : F.left with
    | direct x hv hx h => exact False.elim (hleft (by rw [hl]; trivial))
    | cherry C =>
      have hlarge : alpha0 * (Limb.cherry C).length ≤ I.distance C.center C.primary := by
        have hbad : ¬ I.distance C.center C.primary < alpha0 * (Limb.cherry C).length := by
          simpa only [hl, Limb.Small] using hleft
        exact le_of_not_gt hbad
      exact F.regular_datum_of_left hred hparent C hl hlarge a hlo hhi

theorem RegularDatum.not_two_groups {F : Fan S parent v} {a : ℝ} {D : Finset V}
    (h : RegularDatum F a D) : ¬ TwoGroups (terminalGraph S) D := by
  intro htwo
  obtain ⟨_, _, _, _, x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := h
  exact htwo.not_three hx hy hz hxy hxz hyz

theorem RegularDatum.promoted_two_groups (F : RootedFringe S parent v)
    (hc : S.IsClean) (hstar : ¬ Nonempty (ShortStar S)) (R : FullyPromoted F.fan)
    {a : ℝ} {D : Finset V} (h : RegularDatum F.fan a D) :
    TwoGroups (terminalGraph R.solution) D := by
  obtain ⟨hD, hsub, _, _, _⟩ := h
  have hDT : D ⊆ I.terminals := by
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hD
    intro y hy
    exact ((mem_component I a x y).mp hy).1
  refine ⟨(F.fan.left.primary : V), (F.fan.right.primary : V), ?_⟩
  intro x hx
  exact F.promoted_two_groups hc hstar R x (hsub hx) (hDT hx)

end SteinerUpperBound.Structural.Tree.Fan
