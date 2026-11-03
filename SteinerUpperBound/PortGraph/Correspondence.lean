module

public import SteinerUpperBound.PortGraph.Placement

@[expose] public section

namespace SteinerUpperBound.PortGraph

open scoped Classical BigOperators
open Covers.Geometry Matching

variable {n k b B : ℕ} {Q : Type}

theorem exists_copy_ports (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C D : Vertex I bits cfg B) (hne : C.val ≠ D.val) (v x y : Fin n)
    (hx : x ∈ C.val) (hy : y ∈ D.val) (hv : v ∈ eligible I bits cfg)
    (hvC : v ∈ lists I bits cfg b C.val) (hvD : v ∈ lists I bits cfg b D.val)
    (hdx : I.distance v x ≤ radius cfg) (hdy : I.distance v y ≤ radius cfg) :
    ∃ e : Copy I bits cfg b B, name cfg e = (v, s(x, y)) ∧
      (((graph I bits cfg b B).left e = C ∧ (graph I bits cfg b B).right e = D) ∨
        ((graph I bits cfg b B).left e = D ∧ (graph I bits cfg b B).right e = C)) := by
  have hxN := vertex_subset I bits cfg B C hx
  have hyN := vertex_subset I bits cfg B D hy
  obtain ⟨i, hi⟩ := terminal_index I cfg hT (retained_subset I bits cfg hxN)
  obtain ⟨j, hj⟩ := terminal_index I cfg hT (retained_subset I bits cfg hyN)
  have hc := portComponent_eq I bits cfg (vertex_part I bits cfg B C) hx
  have hd := portComponent_eq I bits cfg (vertex_part I bits cfg B D) hy
  have hij : i ≠ j := by
    intro he
    have hxy : x = y := hi.symm.trans (he ▸ hj)
    exact hne (hc.symm.trans (hxy ▸ hd))
  rcases lt_or_gt_of_ne hij with hij | hji
  · let e : Copy I bits cfg b B := ⟨(v, i, j),
      ⟨hij, by simpa [leftPort, hi] using hxN, by simpa [rightPort, hj] using hyN,
        by simpa [leftPort, hi, hc] using C.property,
        by simpa [rightPort, hj, hd] using D.property,
        by simpa [leftPort, rightPort, hi, hj, hc, hd] using hne,
        hv, by simpa [leftPort, hi, hc] using hvC, by simpa [rightPort, hj, hd] using hvD,
        by simpa [leftPort, hi] using hdx, by simpa [rightPort, hj] using hdy⟩⟩
    refine ⟨e, by simp [name, e, leftPort, rightPort, hi, hj], Or.inl ⟨?_, ?_⟩⟩
    · exact Subtype.ext (by simpa [graph, e, leftPort, hi] using hc)
    · exact Subtype.ext (by simpa [graph, e, rightPort, hj] using hd)
  · let e : Copy I bits cfg b B := ⟨(v, j, i),
      ⟨hji, by simpa [leftPort, hj] using hyN, by simpa [rightPort, hi] using hxN,
        by simpa [leftPort, hj, hd] using D.property,
        by simpa [rightPort, hi, hc] using C.property,
        by simpa [leftPort, rightPort, hi, hj, hc, hd] using hne.symm,
        hv, by simpa [leftPort, hj, hd] using hvD, by simpa [rightPort, hi, hc] using hvC,
        by simpa [leftPort, hj] using hdy, by simpa [rightPort, hi] using hdx⟩⟩
    refine ⟨e, by simp [name, e, leftPort, rightPort, hi, hj, Sym2.eq_iff], Or.inr ⟨?_, ?_⟩⟩
    · exact Subtype.ext (by simpa [graph, e, leftPort, hj] using hd)
    · exact Subtype.ext (by simpa [graph, e, rightPort, hi] using hc)

theorem slotSpec_success (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (s : LocalAccess.PortSlot b B k)
    (r : LocalAccess.PortReply n k b B) (hr : slotSpec I bits cfg hT hnd C s = some r) :
    ∃ (v x : Fin n) (D : Vertex I bits cfg B),
      ∃ (hx : x ∈ C.val) (hy : cfg.terminals.get s.2.2 ∈ D.val)
        (hv : v ∈ lists I bits cfg b D.val),
      (canonicalFrame I cfg b B C.val).rows.slots.get s.1 = some v ∧
      (canonicalFrame I cfg b B C.val).pointSlots.get s.2.1 = some x ∧
      C.val ≠ D.val ∧ v ∈ eligible I bits cfg ∧ v ∈ lists I bits cfg b C.val ∧
      I.distance v x ≤ radius cfg ∧ I.distance v (cfg.terminals.get s.2.2) ≤ radius cfg ∧
      r = reply I bits cfg hT hnd D v x (cfg.terminals.get s.2.2)
        ((vertex_subset I bits cfg B C).trans (retained_subset I bits cfg) hx) hy
        (centerPosition I bits cfg b B hT D v hv) := by
  classical
  cases hrow : (canonicalFrame I cfg b B C.val).rows.slots.get s.1 with
  | none => simp [slotSpec, hrow] at hr
  | some v =>
    cases hpoint : (canonicalFrame I cfg b B C.val).pointSlots.get s.2.1 with
    | none => simp [slotSpec, hrow, hpoint] at hr
    | some x =>
      simp only [slotSpec, hrow, hpoint] at hr
      split_ifs at hr with hx hy hcond
      unfold partnerSpec at hr
      dsimp only at hr
      split_ifs at hr with hD hv he
      let D : Vertex I bits cfg B := ⟨portComponent I bits cfg (cfg.terminals.get s.2.2), hD⟩
      have hyD : cfg.terminals.get s.2.2 ∈ D.val := componentOn_self I _ _ hy
      have hne : C.val ≠ D.val := fun h =>
        hcond.2.1 (h.symm ▸ hyD)
      refine ⟨v, x, D, hx, hyD, hv, rfl, rfl, hne, he,
        rowSlot_mem I bits cfg b B hT (vertex_part I bits cfg B C) hrow,
        hcond.2.2.1, hcond.2.2.2, (Option.some.inj hr).symm⟩

theorem slotSpec_positive (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C D : Vertex I bits cfg B) (s : LocalAccess.PortSlot b B k) (v x : Fin n)
    (hx : x ∈ C.val) (hy : cfg.terminals.get s.2.2 ∈ D.val) (hne : C.val ≠ D.val)
    (hv : v ∈ eligible I bits cfg) (hvD : v ∈ lists I bits cfg b D.val)
    (hdx : I.distance v x ≤ radius cfg) (hdy : I.distance v (cfg.terminals.get s.2.2) ≤ radius cfg)
    (hrow : (canonicalFrame I cfg b B C.val).rows.slots.get s.1 = some v)
    (hpoint : (canonicalFrame I cfg b B C.val).pointSlots.get s.2.1 = some x) :
    slotSpec I bits cfg hT hnd C s =
      some (reply I bits cfg hT hnd D v x (cfg.terminals.get s.2.2)
        ((vertex_subset I bits cfg B C).trans (retained_subset I bits cfg) hx) hy
        (centerPosition I bits cfg b B hT D v hvD)) := by
  classical
  have hyN := vertex_subset I bits cfg B D hy
  have hyC : cfg.terminals.get s.2.2 ∉ C.val := fun h =>
    Finset.disjoint_left.mp (parts_disjoint I bits cfg
      (vertex_part I bits cfg B C) (vertex_part I bits cfg B D) hne) h hy
  have hyD : cfg.terminals.get s.2.2 ∉ removed I cfg := fun h =>
    Finset.disjoint_left.mp (vertex_disjoint I bits cfg B D) hy h
  have heq := portComponent_eq I bits cfg (vertex_part I bits cfg B D) hy
  have hcond : cfg.terminals.get s.2.2 ∉ removed I cfg ∧ cfg.terminals.get s.2.2 ∉ C.val ∧
      I.distance v x ≤ radius cfg ∧ I.distance v (cfg.terminals.get s.2.2) ≤ radius cfg :=
    ⟨hyD, hyC, hdx, hdy⟩
  simp only [slotSpec, hrow, hpoint, dite_eq_left hx, dite_eq_left hyN,
    ite_eq_left hcond]
  unfold partnerSpec
  simp only [heq, dite_eq_left D.property, dite_eq_left hvD, ite_eq_left hv]

theorem reply_reverse_name (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (D : Vertex I bits cfg B) (v x y : Fin n) (hx : x ∈ I.terminals)
    (hy : y ∈ D.val) (hxD : x ∉ D.val) (hv : v ∈ lists I bits cfg b D.val) :
    HasName I cfg D.val
      (reply I bits cfg hT hnd D v x y hx hy (centerPosition I bits cfg b B hT D v hv)).reverse
      (v, s(x, y)) := by
  refine ⟨v, y, centerPosition_get I bits cfg b B hT D v hv,
    pointPosition_get I bits cfg b B hT hnd D y hy, hy, ?_, ?_⟩
  · simpa only [reply, terminalPosition_get] using hxD
  · simp [reply, terminalPosition_get, Sym2.eq_iff]

theorem slotSpec_name (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (s : LocalAccess.PortSlot b B k)
    (r : LocalAccess.PortReply n k b B) (hr : slotSpec I bits cfg hT hnd C s = some r) :
    HasName I cfg C.val s r.name := by
  obtain ⟨v, x, D, hx, hy, hv, hrow, hpoint, hne, he, hvC, hdX, hdY, rfl⟩ :=
    slotSpec_success I bits cfg hT hnd C s r hr
  refine ⟨v, x, hrow, hpoint, hx, ?_, rfl⟩
  intro hyC
  exact Finset.disjoint_left.mp (parts_disjoint I bits cfg
    (vertex_part I bits cfg B C) (vertex_part I bits cfg B D) hne) hyC hy

theorem slotSpec_copy (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (s : LocalAccess.PortSlot b B k)
    (r : LocalAccess.PortReply n k b B) (hr : slotSpec I bits cfg hT hnd C s = some r) :
    ∃ (e : Copy I bits cfg b B) (D : Vertex I bits cfg B),
      name cfg e = r.name ∧
      (((graph I bits cfg b B).left e = C ∧ (graph I bits cfg b B).right e = D) ∨
        ((graph I bits cfg b B).left e = D ∧ (graph I bits cfg b B).right e = C)) ∧
      r.other = canonicalFrame I cfg b B D.val ∧ r.otherRoot = rootEmbedding I bits cfg B hT D ∧
      HasName I cfg D.val r.reverse r.name := by
  obtain ⟨v, x, D, hx, hy, hv, hrow, hpoint, hne, he, hvC, hdX, hdY, rfl⟩ :=
    slotSpec_success I bits cfg hT hnd C s r hr
  obtain ⟨e, hname, hends⟩ := exists_copy_ports I bits cfg hT C D hne v x
    (cfg.terminals.get s.2.2) hx hy he hvC hv hdX hdY
  refine ⟨e, D, hname, hends, rfl, rfl, ?_⟩
  apply reply_reverse_name I bits cfg hT hnd D v x _ _ hy _ hv
  intro hxD
  exact Finset.disjoint_left.mp (parts_disjoint I bits cfg
    (vertex_part I bits cfg B C) (vertex_part I bits cfg B D) hne) hx hxD

theorem rawPlace_success (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (d : Graph.Directed (Copy I bits cfg b B)) :
    ∃ r, slotSpec I bits cfg hT hnd (rawPlace I bits cfg hT hnd d).1
      (rawPlace I bits cfg hT hnd d).2 = some r := by
  rcases d with ⟨e, d⟩
  cases d with
  | false =>
    have h := slotSpec_positive I bits cfg hT hnd
      ((graph I bits cfg b B).right e) ((graph I bits cfg b B).left e)
      (rawPlace I bits cfg hT hnd (e, false)).2 e.val.1 (rightPort cfg e.val)
      (componentOn_self I _ _ e.property.right_retained)
      (componentOn_self I _ _ e.property.left_retained)
      e.property.different.symm e.property.eligible e.property.left_list
      e.property.near_right e.property.near_left
      (centerPosition_get I bits cfg b B hT ((graph I bits cfg b B).right e) e.val.1 e.property.right_list)
      (pointPosition_get I bits cfg b B hT hnd ((graph I bits cfg b B).right e)
        (rightPort cfg e.val) (componentOn_self I _ _ e.property.right_retained))
    exact ⟨_, h⟩
  | true =>
    have h := slotSpec_positive I bits cfg hT hnd
      ((graph I bits cfg b B).left e) ((graph I bits cfg b B).right e)
      (rawPlace I bits cfg hT hnd (e, true)).2 e.val.1 (leftPort cfg e.val)
      (componentOn_self I _ _ e.property.left_retained)
      (componentOn_self I _ _ e.property.right_retained)
      e.property.different e.property.eligible e.property.right_list
      e.property.near_left e.property.near_right
      (centerPosition_get I bits cfg b B hT ((graph I bits cfg b B).left e) e.val.1 e.property.left_list)
      (pointPosition_get I bits cfg b B hT hnd ((graph I bits cfg b B).left e)
        (leftPort cfg e.val) (componentOn_self I _ _ e.property.left_retained))
    exact ⟨_, h⟩

theorem away_head_eq {V E : Type*} (G : Matching.Graph V E) (e : E) (C D : V)
    (h : (G.left e = C ∧ G.right e = D) ∨ (G.left e = D ∧ G.right e = C)) :
    G.head (G.away C e) = D := by
  rcases h with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · simp [Graph.away, Graph.head, hl, hr]
  · have hn : G.left e ≠ C := fun he => G.loopless e (he.trans hr.symm)
    have hn' : D ≠ C := by simpa only [hl] using hn
    simp [Graph.away, Graph.head, hl, hn']

/-- Every genuine successful runtime reply is the unique placement of one
actual directed copy, and its reverse address and canonical root are exact. -/
theorem slot_reply_sound (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (s : LocalAccess.PortSlot b B k)
    (r : LocalAccess.PortReply n k b B) (hr : slotSpec I bits cfg hT hnd C s = some r) :
    ∃ d : Graph.Directed (Copy I bits cfg b B),
      place I bits cfg hT hnd d = ⟨C, slotEquiv b B k s⟩ ∧
      name cfg d.1 = r.name ∧
      r.other = canonicalFrame I cfg b B ((graph I bits cfg b B).head d).val ∧
      r.otherRoot = rootEmbedding I bits cfg B hT ((graph I bits cfg b B).head d) ∧
      slotEquiv b B k r.reverse = (place I bits cfg hT hnd (Matching.Padded.reverse d)).2 := by
  obtain ⟨e, D, hn, he, hf, hroot, hrev⟩ := slotSpec_copy I bits cfg hT hnd C s r hr
  let d := (graph I bits cfg b B).away C e
  have hi : (graph I bits cfg b B).Incident e C := by
    rcases he with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2
  have ht : (rawPlace I bits cfg hT hnd d).1 = C :=
    (place_vertex I bits cfg hT hnd d).trans ((graph I bits cfg b B).tail_away hi)
  have hh : (graph I bits cfg b B).head d = D := away_head_eq _ e C D he
  have hp := rawPlace_name I bits cfg hT hnd d
  have hpn : HasName I cfg C.val (rawPlace I bits cfg hT hnd d).2 r.name := by
    simpa only [ht, Graph.away_edge, d, hn] using hp
  have hs : s = (rawPlace I bits cfg hT hnd d).2 :=
    hasName_unique I bits cfg hT hnd C (slotSpec_name I bits cfg hT hnd C s r hr) hpn
  have htr : (rawPlace I bits cfg hT hnd (Matching.Padded.reverse d)).1 = D :=
    (place_vertex I bits cfg hT hnd (Matching.Padded.reverse d)).trans
      ((Matching.Padded.tail_reverse _ d).trans hh)
  have hpr := rawPlace_name I bits cfg hT hnd (Matching.Padded.reverse d)
  have hprn : HasName I cfg D.val
      (rawPlace I bits cfg hT hnd (Matching.Padded.reverse d)).2 r.name := by
    simpa only [htr, Matching.Padded.reverse_edge, Graph.away_edge, d, hn] using hpr
  have hsrev := hasName_unique I bits cfg hT hnd D hrev hprn
  refine ⟨d, ?_, hn, ?_, ?_, ?_⟩
  · apply Sigma.ext ht
    change HEq (slotEquiv b B k (rawPlace I bits cfg hT hnd d).2) (slotEquiv b B k s)
    rw [hs]
  · simpa only [hh] using hf
  · simpa only [hh] using hroot
  · exact congrArg (slotEquiv b B k) hsrev

end SteinerUpperBound.PortGraph
