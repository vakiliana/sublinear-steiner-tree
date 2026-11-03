module

public import SteinerUpperBound.Covers.Geometry.Domination
public import SteinerUpperBound.LocalAccess.Slot
public import SteinerUpperBound.SetSystem.MutualCapping
public import SteinerUpperBound.Matching.Padded.Basic

@[expose] public section

namespace SteinerUpperBound.PortGraph

open scoped Classical BigOperators
open Covers.Geometry

variable {n k : ℕ} {Q : Type}

noncomputable def retained (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) : Finset (Fin n) :=
  I.terminals.filter (fun x => bits (cfg.key x) = true)

noncomputable def removed (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k) :
    Finset (Fin n) :=
  I.terminals.filter (fun x => cfg.covered.get x = true)

noncomputable def radius (cfg : LocalAccess.SlotConfig Q n k) : ℝ := 5 * cfg.scale / 8

noncomputable def parts (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) : Finset (Finset (Fin n)) :=
  componentsOn I (retained I bits cfg) cfg.scale

noncomputable def rows (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (v : Fin n) : Finset (Finset (Fin n)) :=
  rowOn I (retained I bits cfg) cfg.scale (radius cfg) v

noncomputable def eligible (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) : Finset (Fin n) :=
  eligibleOn I (retained I bits cfg) cfg.scale (radius cfg)

noncomputable def smallParts (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ) : Finset (Finset (Fin n)) :=
  (parts I bits cfg).filter (fun C => C.card ≤ B ∧ Disjoint C (removed I cfg))

abbrev Vertex (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ) :=
  ↥(smallParts I bits cfg B)

noncomputable def incidentList {R U : Type*} (order : List R) (row : R → Finset U)
    (b : ℕ) (C : U) : List R :=
  (order.filter (fun v => C ∈ row v)).take b

noncomputable def centerList (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b : ℕ) (C : Finset (Fin n)) : List (Fin n) :=
  incidentList (List.finRange n) (rows I bits cfg) b C

noncomputable def lists (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b : ℕ) (C : Finset (Fin n)) : Finset (Fin n) :=
  SetSystem.firstIncident (List.finRange n) (rows I bits cfg) b C

theorem retained_subset (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) : retained I bits cfg ⊆ I.terminals :=
  Finset.filter_subset _ _

theorem removed_subset (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k) :
    removed I cfg ⊆ I.terminals := Finset.filter_subset _ _

theorem mem_retained (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (x : Fin n) :
    x ∈ retained I bits cfg ↔ x ∈ I.terminals ∧ bits (cfg.key x) = true := by
  classical
  exact Finset.mem_filter

theorem not_mem_removed (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    {x : Fin n} (hx : x ∈ I.terminals) :
    x ∉ removed I cfg ↔ cfg.covered.get x = false := by
  classical
  cases he : cfg.covered.get x <;> simp [removed, hx, he]

theorem componentsOn_card_le {V : Type*} (I : Instance V) (N : Finset V) (a : ℝ) :
    (componentsOn I N a).card ≤ N.card := by
  classical
  exact Finset.card_image_le

theorem parts_card_le (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) :
    (parts I bits cfg).card ≤ (retained I bits cfg).card :=
  componentsOn_card_le I _ _

/-- Uniform graph roots are components in the residual small-component
universe, not ambient terminal vertices or arbitrary finite sets. -/
theorem vertices_card_le (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ) :
    Fintype.card (Vertex I bits cfg B) ≤ (retained I bits cfg).card := by
  classical
  rw [Fintype.card_coe]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (parts_card_le I bits cfg)

theorem vertex_part (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ) (C : Vertex I bits cfg B) :
    C.val ∈ parts I bits cfg := (Finset.mem_filter.mp C.property).1

theorem vertex_nonempty (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ) (C : Vertex I bits cfg B) :
    C.val.Nonempty := componentsOn_nonempty I _ _ (vertex_part I bits cfg B C)

theorem vertex_subset (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ) (C : Vertex I bits cfg B) :
    C.val ⊆ retained I bits cfg := componentsOn_subset I _ _ (vertex_part I bits cfg B C)

theorem vertex_card_le (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ) (C : Vertex I bits cfg B) :
    C.val.card ≤ B := (Finset.mem_filter.mp C.property).2.1

theorem vertex_disjoint (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ) (C : Vertex I bits cfg B) :
    Disjoint C.val (removed I cfg) := (Finset.mem_filter.mp C.property).2.2

theorem parts_disjoint (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) {C C' : Finset (Fin n)}
    (hC : C ∈ parts I bits cfg) (hC' : C' ∈ parts I bits cfg) (hne : C ≠ C') :
    Disjoint C C' := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  exact hne ((componentOn_eq_of_mem I _ _ hC hx).symm.trans
    (componentOn_eq_of_mem I _ _ hC' hx'))

theorem lists_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b : ℕ) (C : Finset (Fin n)) :
    lists I bits cfg b C = (centerList I bits cfg b C).toFinset := by
  classical
  ext v
  simp only [lists, SetSystem.firstIncident, centerList, incidentList, List.mem_toFinset]

theorem centerList_nodup (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b : ℕ) (C : Finset (Fin n)) :
    (centerList I bits cfg b C).Nodup :=
  ((List.nodup_finRange n).filter _).take

theorem centerList_length (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b : ℕ) (C : Finset (Fin n)) :
    (centerList I bits cfg b C).length ≤ b := List.length_take_le _ _

theorem lists_card_le (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b : ℕ) (C : Finset (Fin n)) :
    (lists I bits cfg b C).card ≤ b := by
  classical
  rw [lists_eq]
  exact (List.toFinset_card_le _).trans (centerList_length I bits cfg b C)

theorem lists_sound (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b : ℕ) (C : Finset (Fin n))
    {v : Fin n} (hv : v ∈ lists I bits cfg b C) : C ∈ rows I bits cfg v := by
  classical
  rw [lists_eq] at hv
  have h := List.mem_of_mem_take (List.mem_toFinset.mp hv)
  have hh := (List.mem_filter.mp h).2
  simpa only [decide_eq_true_eq] using hh

/-- Eligibility is always measured in the original retained partition, before
deleting covered or large components. The witness may lie in either kind. -/
theorem eligible_iff_third {V : Type*} [Fintype V] (I : Instance V) (N : Finset V)
    (a r : ℝ) (v : V) {C C' : Finset V}
    (hC : C ∈ rowOn I N a r v) (hC' : C' ∈ rowOn I N a r v) (hne : C ≠ C') :
    v ∈ eligibleOn I N a r ↔
      ∃ z ∈ N, z ∉ C ∧ z ∉ C' ∧ I.distance v z ≤ r := by
  classical
  have hCp := (mem_rowOn I N a r v C).mp hC
  have hC'p := (mem_rowOn I N a r v C').mp hC'
  constructor
  · intro hv
    have hcard : 3 ≤ (rowOn I N a r v).card := (Finset.mem_filter.mp hv).2
    by_contra hn
    have hsub : rowOn I N a r v ⊆ {C, C'} := by
      intro D hD
      by_cases hDC : D = C
      · simp [hDC]
      by_cases hDC' : D = C'
      · simp [hDC']
      obtain ⟨hDp, z, hz, hd⟩ := (mem_rowOn I N a r v D).mp hD
      have hzC : z ∉ C := fun h =>
        hDC ((componentOn_eq_of_mem I N a hDp hz).symm.trans
          (componentOn_eq_of_mem I N a hCp.1 h))
      have hzC' : z ∉ C' := fun h =>
        hDC' ((componentOn_eq_of_mem I N a hDp hz).symm.trans
          (componentOn_eq_of_mem I N a hC'p.1 h))
      exact (hn ⟨z, componentsOn_subset I N a hDp hz, hzC, hzC', hd⟩).elim
    have hc := Finset.card_le_card hsub
    have hp : ({C, C'} : Finset (Finset V)).card = 2 := by simp [hne]
    omega
  · rintro ⟨z, hz, hzC, hzC', hd⟩
    let D := componentOn I N a z
    have hD : D ∈ rowOn I N a r v := (mem_rowOn I N a r v D).mpr
      ⟨componentOn_mem_componentsOn I N a hz, z, componentOn_self I N a hz, hd⟩
    have hDC : D ≠ C := fun h => hzC (h ▸ componentOn_self I N a hz)
    have hDC' : D ≠ C' := fun h => hzC' (h ▸ componentOn_self I N a hz)
    have hsub : {C, C', D} ⊆ rowOn I N a r v := by
      intro X hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl <;> assumption
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hc := Finset.card_le_card hsub
    have ht : ({C, C', D} : Finset (Finset V)).card = 3 := by
      simp [hne, hDC, hDC', Ne.symm hDC, Ne.symm hDC']
    omega

end SteinerUpperBound.PortGraph
