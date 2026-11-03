module

public import SteinerUpperBound.PortGraph.Frames

@[expose] public section

namespace SteinerUpperBound.PortGraph

open scoped Classical BigOperators
open Covers.Geometry
open QueryProgram

variable {n k : ℕ} {Q : Type}

theorem vertex_points_ne_nil (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (C : Vertex I bits cfg B) :
    pointList cfg C.val ≠ [] := by
  obtain ⟨x, hx⟩ := vertex_nonempty I bits cfg B C
  have hm := (pointList_mem I cfg hT C.val
    ((vertex_subset I bits cfg B C).trans (retained_subset I bits cfg)) x).mpr hx
  intro he
  simpa only [he, List.not_mem_nil] using hm

noncomputable def componentRoot (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (C : Vertex I bits cfg B) : Fin n :=
  (pointList cfg C.val).head (vertex_points_ne_nil I bits cfg B hT C)

theorem componentRoot_mem (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (C : Vertex I bits cfg B) :
    componentRoot I bits cfg B hT C ∈ C.val :=
  (pointList_mem I cfg hT C.val
    ((vertex_subset I bits cfg B C).trans (retained_subset I bits cfg)) _).mp
      (List.head_mem (vertex_points_ne_nil I bits cfg B hT C))

noncomputable def rootEmbedding (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) : Vertex I bits cfg B ↪ Fin n where
  toFun := componentRoot I bits cfg B hT
  inj' := by
    intro C D he
    apply Subtype.ext
    exact (portComponent_eq I bits cfg (vertex_part I bits cfg B C)
      (componentRoot_mem I bits cfg B hT C)).symm.trans
        (he ▸ portComponent_eq I bits cfg (vertex_part I bits cfg B D)
          (componentRoot_mem I bits cfg B hT D))

theorem frame_head (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (C : Vertex I bits cfg B) :
    (canonicalFrame I cfg b B C.val).points.head? = some (rootEmbedding I bits cfg B hT C) :=
  List.head?_eq_some_head _

def slotEquiv (b B k : ℕ) : LocalAccess.PortSlot b B k ≃ Fin (b * B * k) :=
  (Equiv.prodCongr (Equiv.refl (Fin b)) finProdFinEquiv).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_assoc b B k).symm))

theorem slots_card (b B k : ℕ) :
    Fintype.card (LocalAccess.PortSlot b B k) = b * B * k := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (slotEquiv b B k)

/-- This is the runtime address shape. It contains an ambient root, not a
proof that a counterfactual metric reply denotes a genuine graph vertex. -/
noncomputable def ambientAddress (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) :
    Matching.Padded.Slot (fun _ : Vertex I bits cfg B => b * B * k) ↪
      Fin n × Fin (b * B * k) where
  toFun s := (rootEmbedding I bits cfg B hT s.1, s.2)
  inj' := by
    intro s t he
    have hv := (rootEmbedding I bits cfg B hT).injective (congrArg Prod.fst he)
    cases s with
    | mk C i =>
      cases t with
      | mk D j =>
        dsimp only at hv
        subst D
        exact congrArg (Sigma.mk C) (congrArg Prod.snd he)

theorem list_pad_exists {V : Type*} (l : List V) (d : ℕ) (hlen : l.length ≤ d)
    {x : V} (hx : x ∈ l) : ∃ i : Fin d, l[i.val]? = some x := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  have hb := (List.getElem?_eq_some_iff.mp hi).choose
  exact ⟨⟨i, hb.trans_le hlen⟩, hi⟩

theorem list_pad_unique {V : Type*} {d : ℕ} (l : List V) (hnd : l.Nodup)
    {i j : Fin d} {x : V} (hi : l[i.val]? = some x) (hj : l[j.val]? = some x) : i = j := by
  obtain ⟨hi', hxi⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', hxj⟩ := List.getElem?_eq_some_iff.mp hj
  exact Fin.ext ((hnd.getElem_inj_iff (hi := hi') (hj := hj')).mp (hxi.trans hxj.symm))

theorem index_eq_some_iff {V : Type*} {d : ℕ} (get : Fin d → Option V) (x : V)
    (huniq : ∀ i j, get i = some x → get j = some x → i = j) (i : Fin d) :
    (LocalAccess.indexResult get x).value = some i ↔ get i = some x := by
  constructor
  · exact LocalAccess.index_some get x
  · intro hi
    obtain ⟨j, hj⟩ := LocalAccess.index_exists get x ⟨i, hi⟩
    have he := huniq j i (LocalAccess.index_some get x hj) hi
    simpa only [he] using hj

theorem pointSlot_unique (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (b B : ℕ) (hnd : cfg.terminals.toList.Nodup) (C : Finset (Fin n))
    {i j : Fin B} {x : Fin n}
    (hi : (canonicalFrame I cfg b B C).pointSlots.get i = some x)
    (hj : (canonicalFrame I cfg b B C).pointSlots.get j = some x) : i = j := by
  rw [canonicalFrame_pointSlot] at hi hj
  exact list_pad_unique _ (pointList_nodup cfg hnd C) hi hj

theorem rowSlot_unique (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) {C : Finset (Fin n)}
    (hC : C ∈ parts I bits cfg) {i j : Fin b} {v : Fin n}
    (hi : (canonicalFrame I cfg b B C).rows.slots.get i = some v)
    (hj : (canonicalFrame I cfg b B C).rows.slots.get j = some v) : i = j := by
  rw [canonicalFrame_rowSlot I bits cfg b B hT hC] at hi hj
  exact list_pad_unique _ (centerList_nodup I bits cfg b C) hi hj

theorem pointSlot_exists (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) {x : Fin n} (hx : x ∈ C.val) :
    ∃ i : Fin B, (canonicalFrame I cfg b B C.val).pointSlots.get i = some x := by
  have hsub := (vertex_subset I bits cfg B C).trans (retained_subset I bits cfg)
  have hlen : (pointList cfg C.val).length ≤ B := by
    rw [pointList_length I cfg hT hnd C.val hsub]
    exact vertex_card_le I bits cfg B C
  obtain ⟨i, hi⟩ := list_pad_exists (pointList cfg C.val) B hlen
    ((pointList_mem I cfg hT C.val hsub x).mpr hx)
  exact ⟨i, by rwa [canonicalFrame_pointSlot]⟩

theorem rowSlot_exists (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Vertex I bits cfg B) {v : Fin n} (hv : v ∈ lists I bits cfg b C.val) :
    ∃ i : Fin b, (canonicalFrame I cfg b B C.val).rows.slots.get i = some v := by
  have hm : v ∈ centerList I bits cfg b C.val := by
    rw [lists_eq] at hv
    exact List.mem_toFinset.mp hv
  obtain ⟨i, hi⟩ := list_pad_exists _ b (centerList_length I bits cfg b C.val) hm
  exact ⟨i, by rwa [canonicalFrame_rowSlot I bits cfg b B hT (vertex_part I bits cfg B C)]⟩

noncomputable def pointPosition (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (x : Fin n) (hx : x ∈ C.val) : Fin B :=
  Classical.choose (LocalAccess.index_exists _ x (pointSlot_exists I bits cfg b B hT hnd C hx))

theorem pointPosition_index (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (x : Fin n) (hx : x ∈ C.val) :
    (LocalAccess.indexResult (canonicalFrame I cfg b B C.val).pointSlots.get x).value =
      some (pointPosition I bits cfg b B hT hnd C x hx) :=
  Classical.choose_spec (LocalAccess.index_exists
    (canonicalFrame I cfg b B C.val).pointSlots.get x
    (pointSlot_exists I bits cfg b B hT hnd C hx))

theorem pointPosition_get (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (x : Fin n) (hx : x ∈ C.val) :
    (canonicalFrame I cfg b B C.val).pointSlots.get (pointPosition I bits cfg b B hT hnd C x hx) =
      some x :=
  LocalAccess.index_some _ x (pointPosition_index I bits cfg b B hT hnd C x hx)

noncomputable def centerPosition (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Vertex I bits cfg B) (v : Fin n) (hv : v ∈ lists I bits cfg b C.val) : Fin b :=
  Classical.choose (LocalAccess.index_exists _ v (rowSlot_exists I bits cfg b B hT C hv))

theorem centerPosition_index (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Vertex I bits cfg B) (v : Fin n) (hv : v ∈ lists I bits cfg b C.val) :
    (LocalAccess.indexResult (canonicalFrame I cfg b B C.val).rows.slots.get v).value =
      some (centerPosition I bits cfg b B hT C v hv) :=
  Classical.choose_spec (LocalAccess.index_exists
    (canonicalFrame I cfg b B C.val).rows.slots.get v
    (rowSlot_exists I bits cfg b B hT C hv))

theorem centerPosition_get (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Vertex I bits cfg B) (v : Fin n) (hv : v ∈ lists I bits cfg b C.val) :
    (canonicalFrame I cfg b B C.val).rows.slots.get (centerPosition I bits cfg b B hT C v hv) =
      some v :=
  LocalAccess.index_some _ v (centerPosition_index I bits cfg b B hT C v hv)

theorem terminal_index_value (cfg : LocalAccess.SlotConfig Q n k)
    (hnd : cfg.terminals.toList.Nodup) (i : Fin k) :
    (LocalAccess.indexResult (fun j => some (cfg.terminals.get j)) (cfg.terminals.get i)).value = some i := by
  apply (index_eq_some_iff (fun j => some (cfg.terminals.get j)) (cfg.terminals.get i) ?_ i).mpr rfl
  intro j j' hj hj'
  exact vector_get_injective cfg.terminals hnd
    ((Option.some.inj hj).trans (Option.some.inj hj').symm)

theorem pointSlot_mem (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (b B : ℕ) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Finset (Fin n)) (hC : C ⊆ I.terminals) {i : Fin B} {x : Fin n}
    (hi : (canonicalFrame I cfg b B C).pointSlots.get i = some x) : x ∈ C := by
  rw [canonicalFrame_pointSlot] at hi
  exact (pointList_mem I cfg hT C hC x).mp (List.mem_iff_getElem?.mpr ⟨i.val, hi⟩)

theorem rowSlot_mem (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) {C : Finset (Fin n)}
    (hC : C ∈ parts I bits cfg) {i : Fin b} {v : Fin n}
    (hi : (canonicalFrame I cfg b B C).rows.slots.get i = some v) :
    v ∈ lists I bits cfg b C := by
  rw [canonicalFrame_rowSlot I bits cfg b B hT hC] at hi
  rw [lists_eq]
  exact List.mem_toFinset.mpr (List.mem_iff_getElem?.mpr ⟨i.val, hi⟩)

noncomputable def terminalPosition (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (x : Fin n) (hx : x ∈ I.terminals) : Fin k :=
  Classical.choose (terminal_index I cfg hT hx)

theorem terminalPosition_get (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (x : Fin n) (hx : x ∈ I.terminals) :
    cfg.terminals.get (terminalPosition I cfg hT x hx) = x :=
  Classical.choose_spec (terminal_index I cfg hT hx)

theorem terminalPosition_index (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (x : Fin n) (hx : x ∈ I.terminals) :
    (LocalAccess.indexResult (fun j => some (cfg.terminals.get j)) x).value =
      some (terminalPosition I cfg hT x hx) := by
  have h := terminal_index_value cfg hnd (terminalPosition I cfg hT x hx)
  rwa [terminalPosition_get] at h

theorem locate_root (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (c : Cache Q) (hc : Cache.Correct bits c) :
    (LocalAccess.locateResult I.weight bits cfg.key cfg.scale b B (List.finRange n)
      cfg.terminals.toList (rootEmbedding I bits cfg B hT C) c).value.frame =
      some (canonicalFrame I cfg b B C.val) := by
  have hx := componentRoot_mem I bits cfg B hT C
  have hxN := vertex_subset I bits cfg B C hx
  have he := portComponent_eq I bits cfg (vertex_part I bits cfg B C) hx
  have h := locate_frame I bits cfg b B hT hnd hxN c hc
  rw [he, ite_eq_left (vertex_card_le I bits cfg B C)] at h
  exact h

end SteinerUpperBound.PortGraph
