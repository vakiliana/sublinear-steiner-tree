module

public import SteinerUpperBound.SetSystem.Basic
public import SteinerUpperBound.SetSystem.Incidence

@[expose] public section

namespace SteinerUpperBound.SetSystem

open scoped Classical BigOperators

variable {R U J : Type*}

theorem saving_ge_ports_union [Fintype J] (E : Finset R) (rows : R → Finset U)
    (A : Finset U) (center : J → R) (ports : J → Finset U)
    (heligible : ∀ j, center j ∈ E)
    (hsound : ∀ j, ports j ⊆ A ∩ rows (center j)) :
    ((Finset.univ.biUnion ports).card : ℝ) - Nat.card J ≤ saving E rows A := by
  classical
  let F := Finset.univ.image center
  have hFE : F ⊆ E := by
    intro r hr
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
    exact heligible j
  have hsub : Finset.univ.biUnion ports ⊆ A ∩ F.biUnion rows := by
    intro x hx
    obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp hx
    have hs := hsound j hxj
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hs).1,
      Finset.mem_biUnion.mpr ⟨center j,
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩,
        (Finset.mem_inter.mp hs).2⟩⟩
  have hc : ((Finset.univ.biUnion ports).card : ℝ) ≤ (A ∩ F.biUnion rows).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hf : (F.card : ℝ) ≤ Nat.card J := by
    have hh : F.card ≤ Nat.card J := by
      simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using
        (Finset.card_image_le (s := (Finset.univ : Finset J)) (f := center))
    exact_mod_cast hh
  have hw := saving_witness E rows A F hFE
  linarith

theorem portGraph_rank_le_union_card [Fintype U] [Fintype J] (ports : J → Finset U) :
    GraphRank.rank (portGraph ports) ≤ (Finset.univ.biUnion ports).card := by
  classical
  have hle : portGraph ports ≤ Network.completeOn (Finset.univ.biUnion ports) := by
    intro x y hxy
    obtain ⟨hne, j, hx, hy⟩ := hxy
    exact (Network.completeOn_adj _ x y).mpr ⟨hne,
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hx⟩,
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hy⟩⟩
  exact (GraphRank.rank_mono hle).trans
    ((GraphRank.rank_completeOn _).le.trans (Nat.sub_le _ _))

/-- Event labels may map to the same eligible center. -/
theorem port_rank_saving [Fintype U] [Fintype J] (E : Finset R)
    (rows : R → Finset U) (A : Finset U) (center : J → R)
    (ports : J → Finset U) (heligible : ∀ j, center j ∈ E)
    (hsound : ∀ j, ports j ⊆ A ∩ rows (center j)) :
    (GraphRank.rank (portGraph ports) : ℝ) - Nat.card J ≤ saving E rows A := by
  have hr : (GraphRank.rank (portGraph ports) : ℝ) ≤ (Finset.univ.biUnion ports).card := by
    exact_mod_cast portGraph_rank_le_union_card ports
  have hs := saving_ge_ports_union E rows A center ports heligible hsound
  linarith

theorem incidence_forest_events_le_saving [Fintype U] [Fintype J]
    (E : Finset R) (rows : R → Finset U) (A : Finset U)
    (center : J → R) (ports : J → Finset U)
    (heligible : ∀ j, center j ∈ E)
    (hsound : ∀ j, ports j ⊆ A ∩ rows (center j))
    (hdegree : ∀ j, 3 ≤ (ports j).card)
    (hforest : (incidenceGraph ports).IsAcyclic) :
    (Nat.card J : ℝ) ≤ saving E rows A := by
  have hr := incidence_forest_port_rank ports
    (fun j => Finset.card_pos.mp (by have := hdegree j; omega)) hforest
  have hd : 3 * Nat.card J ≤ ∑ j, (ports j).card := by
    calc
      _ = ∑ _j : J, 3 := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hdegree j)
  have hr' : (GraphRank.rank (portGraph ports) : ℝ) + Nat.card J =
      ∑ j, ((ports j).card : ℝ) := by exact_mod_cast hr
  have hd' : 3 * (Nat.card J : ℝ) ≤ ∑ j, ((ports j).card : ℝ) := by exact_mod_cast hd
  have hs := port_rank_saving E rows A center ports heligible hsound
  linarith

end SteinerUpperBound.SetSystem
