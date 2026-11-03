module

public import SteinerUpperBound.Covers.Geometry.Domination
public import SteinerUpperBound.MSTRankIntegral
public import SteinerUpperBound.SavingSoundness.SupportRank
public import SteinerUpperBound.SavingScores.Partition

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry
open scoped Classical BigOperators

variable {V : Type*} [Fintype V]

noncomputable def componentCount (I : Instance V) (S : Finset V) (a : ℝ) : ℕ :=
  (componentsOn I S a).card

noncomputable abbrev selectedGraph (I : Instance V) (S : Finset V) (a : ℝ) :
    SimpleGraph ↥S := (thresholdOn I S a).comap Subtype.val

theorem selected_reachable_iff (I : Instance V) (S : Finset V) (a : ℝ) (x y : ↥S) :
    (selectedGraph I S a).Reachable x y ↔
      (thresholdOn I S a).Reachable (x : V) (y : V) := by
  constructor
  · intro h
    exact h.map ⟨Subtype.val, fun hab => hab⟩
  · intro h
    obtain ⟨p⟩ := h
    have liftWalk : ∀ {u v : V}, (thresholdOn I S a).Walk u v →
        ∀ (hu : u ∈ S) (hv : v ∈ S),
          (selectedGraph I S a).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
      intro u v w
      induction w with
      | nil => intro _ _; exact SimpleGraph.Reachable.refl _
      | @cons u z v huz w ih =>
        intro hu hv
        have hz := ((thresholdOn_adj I S a u z).mp huz).2.2.1
        exact (show (selectedGraph I S a).Adj ⟨u, hu⟩ ⟨z, hz⟩ from huz).reachable.trans
          (ih hz hv)
    exact liftWalk p x.property y.property

noncomputable abbrev selectedComponent (I : Instance V) (S : Finset V) (a : ℝ)
    (C : (selectedGraph I S a).ConnectedComponent) : ↥(componentsOn I S a) :=
  ⟨componentOn I S a (GraphRank.representative (selectedGraph I S a) C).val,
    componentOn_mem_componentsOn I S a
      (GraphRank.representative (selectedGraph I S a) C).property⟩

theorem selectedComponent_bijective (I : Instance V) (S : Finset V) (a : ℝ) :
    Function.Bijective (selectedComponent I S a) := by
  constructor
  · intro C D he
    have hset := congrArg Subtype.val he
    have hreach := (componentOn_eq_iff I S a
      (GraphRank.representative (selectedGraph I S a) D).property).mp hset
    have hquot := SimpleGraph.ConnectedComponent.sound
      ((selected_reachable_iff I S a _ _).mpr hreach)
    simpa only [GraphRank.representative_component] using hquot
  · intro C
    obtain ⟨x, hx⟩ := componentsOn_nonempty I S a C.property
    let x' : ↥S := ⟨x, componentsOn_subset I S a C.property hx⟩
    refine ⟨(selectedGraph I S a).connectedComponentMk x', ?_⟩
    apply Subtype.ext
    have hrep := GraphRank.representative_component (selectedGraph I S a)
      ((selectedGraph I S a).connectedComponentMk x')
    have hr := (selected_reachable_iff I S a _ _).mp
      (SimpleGraph.ConnectedComponent.eq.mp hrep)
    exact (componentOn_eq_of_reachable I S a hr).trans
      (componentOn_eq_of_mem I S a C.property hx)

theorem rank_add_componentCount (I : Instance V) (S : Finset V) (a : ℝ) :
    GraphRank.rank (thresholdOn I S a) + componentCount I S a = S.card := by
  classical
  let G := selectedGraph I S a
  have hmap : G.map (Subtype.val : ↥S → V) = thresholdOn I S a := by
    ext x y
    constructor
    · intro hxy
      obtain ⟨_, u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj' Subtype.val G x y).mp hxy
      exact huv
    · intro hxy
      obtain ⟨hne, hx, hy, _⟩ := (thresholdOn_adj I S a x y).mp hxy
      exact (SimpleGraph.map_adj' Subtype.val G x y).mpr
        ⟨hne, ⟨x, hx⟩, ⟨y, hy⟩, hxy, rfl, rfl⟩
  have hr := SavingSoundness.rank_map_eq_of_injOn_support G (Subtype.val : ↥S → V)
    (Set.injOn_of_injective Subtype.val_injective)
  rw [hmap] at hr
  have he := Nat.card_congr (Equiv.ofBijective (selectedComponent I S a)
    (selectedComponent_bijective I S a))
  have hc : Nat.card G.ConnectedComponent = componentCount I S a := by
    simpa only [componentCount, Nat.card_eq_fintype_card, Fintype.card_coe] using he
  have hs : Nat.card ↥S = S.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have h := GraphRank.rank_add_components G
  rw [hc, hs, ← hr] at h
  exact h

theorem below_eq_thresholdOn (I : Instance V) (S : Finset V) (a : ℝ) :
    TerminalMST.below I.weight S a = thresholdOn I S a := by
  ext x y
  simp only [TerminalMST.below_adj, thresholdOn_adj, Instance.weight_mk]

theorem componentCount_pos (I : Instance V) (S : Finset V) (a : ℝ) (hS : S.Nonempty) :
    0 < componentCount I S a := by
  obtain ⟨x, hx⟩ := hS
  exact Finset.card_pos.mpr ⟨componentOn I S a x, componentOn_mem_componentsOn I S a hx⟩

theorem curve_eq_componentCount (I : Instance V) (S : Finset V) (a : ℝ) (hS : S.Nonempty) :
    TerminalMST.curve I.weight S a = (componentCount I S a : ℝ) - 1 := by
  have hnat := rank_add_componentCount I S a
  have hr : (GraphRank.rank (thresholdOn I S a) : ℝ) + componentCount I S a = S.card := by
    exact_mod_cast hnat
  have hS1 : 1 ≤ S.card := Finset.card_pos.mpr hS
  unfold TerminalMST.curve
  rw [below_eq_thresholdOn, Nat.cast_sub hS1]
  norm_num only [Nat.cast_one]
  linarith

theorem cover_componentCount_sandwich (I : Instance V) (T N : Finset V)
    (delta a : ℝ) (hd : 0 ≤ delta) (hd1 : delta < 1) (ha : 0 < a)
    (hc : CoverOn I T N (delta * a)) (hNT : N ⊆ T) :
    componentCount I T a ≤ componentCount I N a ∧
      componentCount I N a ≤ componentCount I T ((1 - 2 * delta) * a) := by
  have hh := components_card_sandwich I T N (delta * a) hc hNT (mul_nonneg hd ha.le)
    a (by nlinarith)
  simpa only [componentCount, show a - 2 * (delta * a) = (1 - 2 * delta) * a by ring] using hh

end SteinerUpperBound.MSTApproximation
