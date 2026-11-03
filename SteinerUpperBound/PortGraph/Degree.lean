module

public import SteinerUpperBound.PortGraph.Program
public import SteinerUpperBound.LocalAccess.SlotResources

@[expose] public section

namespace SteinerUpperBound.PortGraph

open scoped Classical BigOperators
open Covers.Geometry Matching

variable {n k b B : ℕ} {Q : Type}

noncomputable def residualNeighbors (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (v : Fin n) : Finset (Fin n) :=
  ((retained I bits cfg).filter (fun y => I.distance v y ≤ radius cfg)) \ removed I cfg

theorem mem_residualNeighbors (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (v y : Fin n) :
    y ∈ residualNeighbors I bits cfg v ↔
      y ∈ retained I bits cfg ∧ y ∉ removed I cfg ∧ I.distance v y ≤ radius cfg := by
  classical
  simp only [residualNeighbors, Finset.mem_sdiff, Finset.mem_filter]
  tauto

theorem residualNeighbors_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (v : Fin n) :
    residualNeighbors I bits cfg v =
      ((retained I bits cfg) ∩ Finset.univ.filter (fun y => I.distance v y ≤ radius cfg)) \ removed I cfg := by
  classical
  ext y
  simp only [residualNeighbors, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_inter,
    Finset.mem_univ, true_and]

noncomputable def heavySlots (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b : ℕ) (C : Vertex I bits cfg B) :
    Finset (LocalAccess.PortSlot b B k) :=
  Finset.univ.filter (LocalAccess.Heavy I.weight bits cfg (canonicalFrame I cfg b B C.val))

noncomputable def trueSlots (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) : Finset (LocalAccess.PortSlot b B k) :=
  Finset.univ.filter (fun s => ∃ r, slotSpec I bits cfg hT hnd C s = some r)

theorem slotSpec_heavy (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (s : LocalAccess.PortSlot b B k)
    (r : LocalAccess.PortReply n k b B) (hr : slotSpec I bits cfg hT hnd C s = some r) :
    LocalAccess.Heavy I.weight bits cfg (canonicalFrame I cfg b B C.val) s := by
  obtain ⟨v, x, D, hx, hy, hv, hrow, hpoint, hne, he, hvC, hdX, hdY, hr'⟩ :=
    slotSpec_success I bits cfg hT hnd C s r hr
  have hyN := vertex_subset I bits cfg B D hy
  have hyT := retained_subset I bits cfg hyN
  have hnotD : cfg.terminals.get s.2.2 ∉ removed I cfg := fun h =>
    Finset.disjoint_left.mp (vertex_disjoint I bits cfg B D) hy h
  have hnotC : cfg.terminals.get s.2.2 ∉ C.val := fun h =>
    Finset.disjoint_left.mp (parts_disjoint I bits cfg
      (vertex_part I bits cfg B C) (vertex_part I bits cfg B D) hne) h hy
  simp only [LocalAccess.Heavy, hrow, hpoint]
  refine ⟨(not_mem_removed I cfg hyT).mp hnotD, ?_, ?_, ?_, ((mem_retained I bits cfg _).mp hyN).2⟩
  · rw [canonicalFrame_points]
    exact fun h => hnotC ((pointList_mem I cfg hT C.val
      ((vertex_subset I bits cfg B C).trans (retained_subset I bits cfg)) _).mp h)
  · simpa only [Instance.weight_mk, radius] using hdX
  · simpa only [Instance.weight_mk, radius] using hdY

theorem heavy_fiber_card (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (P : ℕ)
    (hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P) (i : Fin b) (j : Fin B) :
    (Finset.univ.filter (fun t : Fin k =>
      LocalAccess.Heavy I.weight bits cfg (canonicalFrame I cfg b B C.val) (i, j, t))).card ≤ P := by
  classical
  let F : Finset (Fin k) := Finset.univ.filter (fun t =>
    LocalAccess.Heavy I.weight bits cfg (canonicalFrame I cfg b B C.val) (i, j, t))
  cases hv : (canonicalFrame I cfg b B C.val).rows.slots.get i with
  | none => simp [LocalAccess.Heavy, hv]
  | some v =>
    have hsub : F.image cfg.terminals.get ⊆ residualNeighbors I bits cfg v := by
      intro y hy
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
      have hh := (Finset.mem_filter.mp ht).2
      simp only [LocalAccess.Heavy, hv] at hh
      cases hx : (canonicalFrame I cfg b B C.val).pointSlots.get j with
      | none => simp [hx] at hh
      | some x =>
        simp only [hx] at hh
        have hyT := terminal_get_mem I cfg hT t
        apply (mem_residualNeighbors I bits cfg v _).mpr
        refine ⟨(mem_retained I bits cfg _).mpr ⟨hyT, hh.2.2.2.2⟩,
          (not_mem_removed I cfg hyT).mpr hh.1, ?_⟩
        simpa only [Instance.weight_mk, radius] using hh.2.2.2.1
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (vector_get_injective cfg.terminals hnd)] at hc
    exact hc.trans (hres v)

/-- Every retained near candidate is charged, even when its later component is
large, covered, nonmutual, or originally ineligible. -/
theorem heavySlots_card_le (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (P : ℕ)
    (hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P) :
    (heavySlots I bits cfg b C).card ≤ b * B * P := by
  classical
  calc
    _ = ∑ i : Fin b, ∑ j : Fin B,
        (Finset.univ.filter (fun t : Fin k =>
          LocalAccess.Heavy I.weight bits cfg (canonicalFrame I cfg b B C.val) (i, j, t))).card := by
      simp only [heavySlots, LocalAccess.PortSlot, Finset.card_eq_sum_ones, Finset.sum_filter,
        Fintype.sum_prod_type]
    _ ≤ ∑ _i : Fin b, ∑ _j : Fin B, P :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        heavy_fiber_card I bits cfg hT hnd C P hres i j))
    _ = _ := by simp [Nat.mul_assoc]

theorem trueSlots_card_le (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (P : ℕ)
    (hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P) :
    (trueSlots I bits cfg b hT hnd C).card ≤ b * B * P := by
  apply (Finset.card_le_card (show trueSlots I bits cfg b hT hnd C ⊆ heavySlots I bits cfg b C from ?_)).trans
    (heavySlots_card_le I bits cfg b hT hnd C P hres)
  intro s hs
  obtain ⟨r, hr⟩ := (Finset.mem_filter.mp hs).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, slotSpec_heavy I bits cfg hT hnd C s r hr⟩

theorem incident_card_eq_degree {V E : Type*} [Fintype E] (G : Matching.Graph V E) (v : V) :
    Fintype.card {e : E // G.Incident e v} = G.degree v := by
  classical
  simp only [Graph.degree, Fintype.card_subtype]

theorem degree_le (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (P : ℕ)
    (hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P) :
    (graph I bits cfg b B).degree C ≤ b * B * P := by
  classical
  let G := graph I bits cfg b B
  let f : {e : Copy I bits cfg b B // G.Incident e C} → ↥(heavySlots I bits cfg b C) := fun e =>
    let d := G.away C e.val
    have ht : (rawPlace I bits cfg hT hnd d).1 = C :=
      (place_vertex I bits cfg hT hnd d).trans (G.tail_away e.property)
    ⟨(rawPlace I bits cfg hT hnd d).2, by
      obtain ⟨r, hr⟩ := rawPlace_success I bits cfg hT hnd d
      have hh := slotSpec_heavy I bits cfg hT hnd (rawPlace I bits cfg hT hnd d).1
        (rawPlace I bits cfg hT hnd d).2 r hr
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa only [ht] using hh⟩⟩
  have hf : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    have hs := congrArg Subtype.val he
    have hv : (rawPlace I bits cfg hT hnd (G.away C e.val)).1 =
        (rawPlace I bits cfg hT hnd (G.away C e'.val)).1 :=
      ((place_vertex I bits cfg hT hnd _).trans (G.tail_away e.property)).trans
        ((place_vertex I bits cfg hT hnd _).trans (G.tail_away e'.property)).symm
    have hp : place I bits cfg hT hnd (G.away C e.val) = place I bits cfg hT hnd (G.away C e'.val) := by
      apply Sigma.ext hv
      exact heq_of_eq (congrArg (slotEquiv b B k) hs)
    exact congrArg Prod.fst (place_injective I bits cfg hT hnd hp)
  have hc := Fintype.card_le_of_injective f hf
  rw [incident_card_eq_degree] at hc
  have hcard : Fintype.card ↥(heavySlots I bits cfg b C) = (heavySlots I bits cfg b C).card :=
    Fintype.card_coe _
  rw [hcard] at hc
  exact hc.trans (heavySlots_card_le I bits cfg b hT hnd C P hres)

end SteinerUpperBound.PortGraph
