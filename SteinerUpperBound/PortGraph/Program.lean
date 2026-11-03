module

public import SteinerUpperBound.PortGraph.Correspondence

@[expose] public section

namespace SteinerUpperBound.PortGraph

open QueryProgram
open scoped Classical BigOperators
open Matching

variable {n k b B : ℕ} {Q : Type}

abbrev AmbientSlot (n b B k : ℕ) := Fin n × Fin (b * B * k)

def encodeReply (r : LocalAccess.PortReply n k b B) : Name n × AmbientSlot n b B k :=
  (r.name, (r.otherRoot, slotEquiv b B k r.reverse))

noncomputable def nameEmbedding (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ) (hnd : cfg.terminals.toList.Nodup) :
    Copy I bits cfg b B ↪ Name n :=
  ⟨name cfg, name_injective I bits cfg b B hnd⟩

noncomputable def encodeTest (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals)
    (value : Copy I bits cfg b B × Matching.Padded.Slot
      (fun _ : Vertex I bits cfg B => b * B * k)) : Name n × AmbientSlot n b B k :=
  (name cfg value.1, ambientAddress I bits cfg b B hT value.2)

/-- Exact ambient presentation of the static `Slots` test. Counterfactual
runtime replies need no proof-valued vertex or edge subtype. -/
theorem slot_encoded (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (s : LocalAccess.PortSlot b B k) :
    (slotSpec I bits cfg hT hnd C s).map encodeReply =
      (staticTest I bits cfg hT hnd ⟨C, slotEquiv b B k s⟩).map
        (encodeTest I bits cfg hT) := by
  classical
  cases hr : slotSpec I bits cfg hT hnd C s with
  | none =>
    have hn : ¬ ∃ d, place I bits cfg hT hnd d = ⟨C, slotEquiv b B k s⟩ := by
      rintro ⟨d, hd⟩
      have hv := congrArg Sigma.fst hd
      have hi := congrArg (fun t : Matching.Padded.Slot
        (fun _ : Vertex I bits cfg B => b * B * k) => t.2) hd
      change (rawPlace I bits cfg hT hnd d).1 = C at hv
      have hs := (slotEquiv b B k).injective hi
      obtain ⟨r, hsuc⟩ := rawPlace_success I bits cfg hT hnd d
      rw [hv, hs, hr] at hsuc
      cases hsuc
    simp only [staticTest, dite_eq_right hn, Option.map_none]
  | some r =>
    obtain ⟨d, hd, hn, hf, hroot, hrev⟩ := slot_reply_sound I bits cfg hT hnd C s r hr
    have ht :
        staticTest I bits cfg hT hnd (place I bits cfg hT hnd d) =
          some (d.1, place I bits cfg hT hnd (Matching.Padded.reverse d)) :=
      (slots I bits cfg hT hnd).test_place d
    rw [hd] at ht
    rw [ht]
    simp only [Option.map_some]
    apply congrArg some
    change (r.name, (r.otherRoot, slotEquiv b B k r.reverse)) =
      (name cfg d.1,
        (rootEmbedding I bits cfg B hT (place I bits cfg hT hnd (Matching.Padded.reverse d)).1,
          (place I bits cfg hT hnd (Matching.Padded.reverse d)).2))
    apply Prod.ext hn.symm
    apply Prod.ext
    · rw [place_vertex, Matching.Padded.tail_reverse]
      exact hroot
    · exact hrev

theorem slot_result_encoded (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (s : LocalAccess.PortSlot b B k)
    (c : Cache Q) (hc : Cache.Correct bits c) :
    ((LocalAccess.slotResult I.weight bits cfg (canonicalFrame I cfg b B C.val) s c).value.1).map encodeReply =
      ((slots I bits cfg hT hnd).test ⟨C, slotEquiv b B k s⟩).map (encodeTest I bits cfg hT) := by
  rw [slot_value I bits cfg hT hnd C s c hc]
  exact slot_encoded I bits cfg hT hnd C s

theorem slot_program_value (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (s : LocalAccess.PortSlot b B k)
    (c : Cache Q) (hc : Cache.Correct bits c)
    (F : Option (Name n × AmbientSlot n b B k) → ℝ) :
    (LocalAccess.slotProgram cfg (canonicalFrame I cfg b B C.val) s c).evaluate I.weight bits
      (fun o => F (o.value.1.map encodeReply)) =
      F (((slots I bits cfg hT hnd).test ⟨C, slotEquiv b B k s⟩).map (encodeTest I bits cfg hT)) := by
  calc
    _ = F (((LocalAccess.slotResult I.weight bits cfg (canonicalFrame I cfg b B C.val) s c).value.1).map
        encodeReply) := (LocalAccess.slot_evaluates I.weight bits cfg _ s c) _
    _ = _ := congrArg F (slot_result_encoded I bits cfg hT hnd C s c hc)

theorem slot_result_frame (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (s : LocalAccess.PortSlot b B k)
    (c : Cache Q) (hc : Cache.Correct bits c) (r : LocalAccess.PortReply n k b B)
    (hr : (LocalAccess.slotResult I.weight bits cfg (canonicalFrame I cfg b B C.val) s c).value.1 = some r) :
    ∃ D : Vertex I bits cfg B,
      r.other = canonicalFrame I cfg b B D.val ∧ r.otherRoot = rootEmbedding I bits cfg B hT D := by
  rw [slot_value I bits cfg hT hnd C s c hc] at hr
  obtain ⟨e, D, _, _, hf, hroot, _⟩ := slotSpec_copy I bits cfg hT hnd C s r hr
  exact ⟨D, hf, hroot⟩

theorem slot_result_frame_exact (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (s : LocalAccess.PortSlot b B k)
    (c : Cache Q) (hc : Cache.Correct bits c) (r : LocalAccess.PortReply n k b B)
    (hr : (LocalAccess.slotResult I.weight bits cfg (canonicalFrame I cfg b B C.val) s c).value.1 = some r)
    (e : Copy I bits cfg b B)
    (t : Matching.Padded.Slot (fun _ : Vertex I bits cfg B => b * B * k))
    (ht : (slots I bits cfg hT hnd).test ⟨C, slotEquiv b B k s⟩ = some (e, t)) :
    r.other = canonicalFrame I cfg b B t.1.val := by
  have he := slot_result_encoded I bits cfg hT hnd C s c hc
  rw [hr, ht] at he
  have hh := congrArg (fun p : Name n × AmbientSlot n b B k => p.2.1) (Option.some.inj he)
  obtain ⟨D, hframe, hroot⟩ := slot_result_frame I bits cfg hT hnd C s c hc r hr
  have hD : D = t.1 := (rootEmbedding I bits cfg B hT).injective (hroot.symm.trans hh)
  simpa only [hD] using hframe

theorem slot_result_unique (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (s t : LocalAccess.PortSlot b B k)
    (c c' : Cache Q) (hc : Cache.Correct bits c) (hc' : Cache.Correct bits c')
    (r r' : LocalAccess.PortReply n k b B)
    (hr : (LocalAccess.slotResult I.weight bits cfg (canonicalFrame I cfg b B C.val) s c).value.1 = some r)
    (hr' : (LocalAccess.slotResult I.weight bits cfg (canonicalFrame I cfg b B C.val) t c').value.1 = some r')
    (hn : r.name = r'.name) : s = t := by
  rw [slot_value I bits cfg hT hnd C s c hc] at hr
  rw [slot_value I bits cfg hT hnd C t c' hc'] at hr'
  apply hasName_unique I bits cfg hT hnd C (slotSpec_name I bits cfg hT hnd C s r hr)
  rw [hn]
  exact slotSpec_name I bits cfg hT hnd C t r' hr'

theorem slot_result_cache_independent (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (s : LocalAccess.PortSlot b B k)
    (c c' : Cache Q) (hc : Cache.Correct bits c) (hc' : Cache.Correct bits c') :
    (LocalAccess.slotResult I.weight bits cfg (canonicalFrame I cfg b B C.val) s c).value.1 =
      (LocalAccess.slotResult I.weight bits cfg (canonicalFrame I cfg b B C.val) s c').value.1 :=
  (slot_value I bits cfg hT hnd C s c hc).trans (slot_value I bits cfg hT hnd C s c' hc').symm

end SteinerUpperBound.PortGraph
