module

public import SteinerUpperBound.PortGraph.SlotSpec

@[expose] public section

namespace SteinerUpperBound.PortGraph

open scoped Classical BigOperators
open Covers.Geometry Matching

variable {n k b B : ℕ} {Q : Type}

def HasName (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (C : Finset (Fin n)) (s : LocalAccess.PortSlot b B k) (nm : Name n) : Prop :=
  ∃ v x, (canonicalFrame I cfg b B C).rows.slots.get s.1 = some v ∧
    (canonicalFrame I cfg b B C).pointSlots.get s.2.1 = some x ∧
    x ∈ C ∧ cfg.terminals.get s.2.2 ∉ C ∧
    nm = (v, s(x, cfg.terminals.get s.2.2))

theorem hasName_functional (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (C : Finset (Fin n)) (s : LocalAccess.PortSlot b B k) {nm nm' : Name n}
    (h : HasName I cfg C s nm) (h' : HasName I cfg C s nm') : nm = nm' := by
  obtain ⟨v, x, hv, hx, _, _, he⟩ := h
  obtain ⟨v', x', hv', hx', _, _, he'⟩ := h'
  have hvv := Option.some.inj (hv.symm.trans hv')
  have hxx := Option.some.inj (hx.symm.trans hx')
  rw [he, he', hvv, hxx]

theorem hasName_unique (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) {s t : LocalAccess.PortSlot b B k} {nm : Name n}
    (hs : HasName I cfg C.val s nm) (ht : HasName I cfg C.val t nm) : s = t := by
  obtain ⟨v, x, hvs, hxs, hxC, hyC, he⟩ := hs
  obtain ⟨w, z, hwt, hzt, hzC, huC, he'⟩ := ht
  have hn := he.symm.trans he'
  have hvw := congrArg Prod.fst hn
  have hp := congrArg Prod.snd hn
  simp only [Prod.fst] at hvw
  simp only [Prod.snd, Sym2.eq_iff] at hp
  rcases hp with ⟨hxz, hyu⟩ | ⟨hxu, hyz⟩
  · have hi : s.1 = t.1 := rowSlot_unique I bits cfg b B hT (vertex_part I bits cfg B C)
      hvs (hvw ▸ hwt)
    have hj : s.2.1 = t.2.1 := pointSlot_unique I cfg b B hnd C.val hxs (hxz ▸ hzt)
    have hk : s.2.2 = t.2.2 := vector_get_injective cfg.terminals hnd hyu
    exact Prod.ext hi (Prod.ext hj hk)
  · exact (huC (hxu ▸ hxC)).elim

noncomputable def rawPlace (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup) :
    Graph.Directed (Copy I bits cfg b B) → Vertex I bits cfg B × LocalAccess.PortSlot b B k
  | (e, false) =>
    ((graph I bits cfg b B).right e,
      centerPosition I bits cfg b B hT ((graph I bits cfg b B).right e) e.val.1 e.property.right_list,
      pointPosition I bits cfg b B hT hnd ((graph I bits cfg b B).right e) (rightPort cfg e.val)
        (componentOn_self I _ _ e.property.right_retained),
      e.val.2.1)
  | (e, true) =>
    ((graph I bits cfg b B).left e,
      centerPosition I bits cfg b B hT ((graph I bits cfg b B).left e) e.val.1 e.property.left_list,
      pointPosition I bits cfg b B hT hnd ((graph I bits cfg b B).left e) (leftPort cfg e.val)
        (componentOn_self I _ _ e.property.left_retained),
      e.val.2.2)

noncomputable def place (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (d : Graph.Directed (Copy I bits cfg b B)) :
    Matching.Padded.Slot (fun _ : Vertex I bits cfg B => b * B * k) :=
  ⟨(rawPlace I bits cfg hT hnd d).1, slotEquiv b B k (rawPlace I bits cfg hT hnd d).2⟩

theorem place_vertex (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (d : Graph.Directed (Copy I bits cfg b B)) :
    (place I bits cfg hT hnd d).1 = (graph I bits cfg b B).tail d := by
  rcases d with ⟨e, d⟩
  cases d <;> rfl

theorem rawPlace_name (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (d : Graph.Directed (Copy I bits cfg b B)) :
    HasName I cfg (rawPlace I bits cfg hT hnd d).1.val
      (rawPlace I bits cfg hT hnd d).2 (name cfg d.1) := by
  rcases d with ⟨e, d⟩
  cases d with
  | false =>
    refine ⟨e.val.1, rightPort cfg e.val,
      centerPosition_get I bits cfg b B hT ((graph I bits cfg b B).right e) e.val.1 e.property.right_list,
      pointPosition_get I bits cfg b B hT hnd ((graph I bits cfg b B).right e) (rightPort cfg e.val)
        (componentOn_self I _ _ e.property.right_retained),
      componentOn_self I _ _ e.property.right_retained,
      ?_, ?_⟩
    · intro hx
      exact e.property.different (portComponent_eq I bits cfg
        (vertex_part I bits cfg B ((graph I bits cfg b B).right e)) hx)
    · simp [name, rawPlace, Sym2.eq_iff, leftPort, rightPort]
  | true =>
    refine ⟨e.val.1, leftPort cfg e.val,
      centerPosition_get I bits cfg b B hT ((graph I bits cfg b B).left e) e.val.1 e.property.left_list,
      pointPosition_get I bits cfg b B hT hnd ((graph I bits cfg b B).left e) (leftPort cfg e.val)
        (componentOn_self I _ _ e.property.left_retained),
      componentOn_self I _ _ e.property.left_retained,
      ?_, rfl⟩
    intro hy
    exact e.property.different (portComponent_eq I bits cfg
      (vertex_part I bits cfg B ((graph I bits cfg b B).left e)) hy).symm

theorem place_injective (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup) :
    Function.Injective (place I bits cfg hT hnd : Graph.Directed (Copy I bits cfg b B) → _) := by
  intro d d' he
  have hv := congrArg Sigma.fst he
  change (rawPlace I bits cfg hT hnd d).1 = (rawPlace I bits cfg hT hnd d').1 at hv
  have hi := congrArg (fun s : Matching.Padded.Slot
      (fun _ : Vertex I bits cfg B => b * B * k) => s.2) he
  have hs := (slotEquiv b B k).injective hi
  have hn := rawPlace_name I bits cfg hT hnd d
  have hn' := rawPlace_name I bits cfg hT hnd d'
  have hnm : name cfg d.1 = name cfg d'.1 := by
    apply hasName_functional I cfg (rawPlace I bits cfg hT hnd d).1.val
      (rawPlace I bits cfg hT hnd d).2 hn
    rwa [← hv, ← hs] at hn'
  have hedge := name_injective I bits cfg b B hnd hnm
  apply (graph I bits cfg b B).directed_eq_of_tail hedge
  rw [← place_vertex I bits cfg hT hnd d, ← place_vertex I bits cfg hT hnd d', he]

/-- Proof-only inverse placement. The runtime never enumerates true copies. -/
noncomputable def staticTest (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (s : Matching.Padded.Slot (fun _ : Vertex I bits cfg B => b * B * k)) :
    Option (Copy I bits cfg b B × Matching.Padded.Slot
      (fun _ : Vertex I bits cfg B => b * B * k)) :=
  if h : ∃ d, place I bits cfg hT hnd d = s then
    let d := Classical.choose h
    some (d.1, place I bits cfg hT hnd (Matching.Padded.reverse d))
  else none

noncomputable def slots (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup) :
    Matching.Padded.Slots (graph I bits cfg b B) where
  length _ := b * B * k
  test := staticTest I bits cfg hT hnd
  place := place I bits cfg hT hnd
  place_vertex := place_vertex I bits cfg hT hnd
  test_place := by
    intro d
    have hd : ∃ d', place I bits cfg hT hnd d' = place I bits cfg hT hnd d := ⟨d, rfl⟩
    rw [staticTest, dite_eq_left hd]
    have he := place_injective I bits cfg hT hnd (Classical.choose_spec hd)
    rw [he]
  test_complete := by
    intro s e r hr
    by_cases h : ∃ d, place I bits cfg hT hnd d = s
    · rw [staticTest, dite_eq_left h] at hr
      have he := Option.some.inj hr
      exact ⟨Classical.choose h, Classical.choose_spec h, congrArg Prod.fst he, congrArg Prod.snd he⟩
    · simp only [staticTest, dite_eq_right h] at hr
      cases hr

end SteinerUpperBound.PortGraph
