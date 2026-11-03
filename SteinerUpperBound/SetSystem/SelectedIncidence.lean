module

public import SteinerUpperBound.SetSystem.Basic
public import SteinerUpperBound.SetSystem.Incidence

@[expose] public section

namespace SteinerUpperBound.SetSystem

open scoped Classical BigOperators

variable {R U : Type*}

noncomputable def coveredElements (F : Finset R) (rows : R → Finset U)
    (A : Finset U) : Finset U := A ∩ F.biUnion rows

noncomputable def selectedPorts (F : Finset R) (rows : R → Finset U)
    (A : Finset U) (r : ↥F) : Finset ↥(coveredElements F rows A) :=
  Finset.univ.filter (fun x => x.val ∈ rows r.val)

theorem selectedPorts_card (F : Finset R) (rows : R → Finset U)
    (A : Finset U) (r : ↥F) :
    (selectedPorts F rows A r).card = (A ∩ rows r.val).card := by
  classical
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp x.property).1,
      (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro x hx
    have hxB : x ∈ coveredElements F rows A := Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hx).1, Finset.mem_biUnion.mpr
        ⟨r.val, r.property, (Finset.mem_inter.mp hx).2⟩⟩
    exact ⟨⟨x, hxB⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_inter.mp hx).2⟩, rfl⟩

theorem selectedIncidence_component_has_row (F : Finset R) (rows : R → Finset U)
    (A : Finset U)
    (c : (incidenceGraph (selectedPorts F rows A)).ConnectedComponent) :
    ∃ r : ↥F, (incidenceGraph (selectedPorts F rows A)).connectedComponentMk
      (Sum.inr r) = c := by
  classical
  let G := incidenceGraph (selectedPorts F rows A)
  have hr := GraphRank.representative_component G c
  cases he : GraphRank.representative G c with
  | inl x =>
      rw [he] at hr
      obtain ⟨r, hrF, hxr⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp x.property).2
      let r' : ↥F := ⟨r, hrF⟩
      have ha : G.Adj (Sum.inl x) (Sum.inr r') :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxr⟩
      exact ⟨r', (SimpleGraph.ConnectedComponent.sound ha.symm.reachable).trans hr⟩
  | inr r => exact ⟨r, he ▸ hr⟩

theorem selectedIncidence_components_bound (E F : Finset R) (rows : R → Finset U)
    (A : Finset U) (hFE : F ⊆ E)
    (hlarge : ∀ r ∈ E, 3 ≤ (A ∩ rows r).card) :
    2 * (Nat.card (incidenceGraph (selectedPorts F rows A)).ConnectedComponent : ℝ) ≤
      saving E rows A := by
  classical
  let G := incidenceGraph (selectedPorts F rows A)
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  choose rep hrep using selectedIncidence_component_has_row F rows A
  let Q : G.ConnectedComponent → Finset U := fun c => A ∩ rows (rep c).val
  have hrep_inj : Function.Injective (fun c : G.ConnectedComponent => (rep c).val) := by
    intro c d h
    have hh : rep c = rep d := Subtype.ext h
    exact (hrep c).symm.trans ((congrArg (fun r => G.connectedComponentMk (Sum.inr r)) hh).trans
      (hrep d))
  have hdisjoint :
      ((Finset.univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent).PairwiseDisjoint Q := by
    intro c _ d _ hcd
    apply Finset.disjoint_left.mpr
    intro x hxc hxd
    have hxA := (Finset.mem_inter.mp hxc).1
    have hxB : x ∈ coveredElements F rows A :=
      Finset.mem_inter.mpr ⟨hxA, Finset.mem_biUnion.mpr
        ⟨(rep c).val, (rep c).property, (Finset.mem_inter.mp hxc).2⟩⟩
    let x' : ↥(coveredElements F rows A) := ⟨x, hxB⟩
    have hc : G.Adj (Sum.inl x') (Sum.inr (rep c)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_inter.mp hxc).2⟩
    have hd : G.Adj (Sum.inl x') (Sum.inr (rep d)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_inter.mp hxd).2⟩
    have heq : G.connectedComponentMk (Sum.inr (rep c)) =
        G.connectedComponentMk (Sum.inr (rep d)) :=
      SimpleGraph.ConnectedComponent.sound (hc.symm.reachable.trans hd.reachable)
    exact hcd ((hrep c).symm.trans (heq.trans (hrep d)))
  let S : Finset R := Finset.univ.image (fun c : G.ConnectedComponent => (rep c).val)
  have hSE : S ⊆ E := by
    intro r hr
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hr
    exact hFE (rep c).property
  have hScard : S.card = Nat.card G.ConnectedComponent := by
    rw [Finset.card_image_of_injective _ hrep_inj, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hcover : A ∩ S.biUnion rows = Finset.univ.biUnion Q := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_biUnion, S, Finset.mem_image,
      Finset.mem_univ, true_and, Q]
    aesop
  have hc : 3 * Nat.card G.ConnectedComponent ≤ (A ∩ S.biUnion rows).card := by
    rw [hcover, Finset.card_biUnion hdisjoint]
    calc
      _ = ∑ _c : G.ConnectedComponent, 3 := by
        simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, smul_eq_mul]
        omega
      _ ≤ ∑ c, (Q c).card := Finset.sum_le_sum (fun c _ => hlarge (rep c).val
        (hFE (rep c).property))
  have hw := saving_witness E rows A S hSE
  rw [hScard] at hw
  have hc' : 3 * (Nat.card G.ConnectedComponent : ℝ) ≤ (A ∩ S.biUnion rows).card := by
    exact_mod_cast hc
  linarith

end SteinerUpperBound.SetSystem
