module

public import SteinerUpperBound.PortGraph.RuntimeAdapter.Invariant
public import SteinerUpperBound.Matching.Padded.PrimitiveDomination

@[expose] public section

namespace SteinerUpperBound.PortGraph.RuntimeAdapter

open QueryProgram
open scoped Classical

variable {n k b B : ℕ} {Q : Type}

abbrev TrueSlot (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ) :=
  Matching.Padded.Slot (fun _ : Vertex I bits cfg B => b * B * k)

noncomputable def source (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (s : TrueSlot I bits cfg b B) : Slot n b B k :=
  ⟨rootEmbedding I bits cfg B hT s.1, s.2⟩

noncomputable def modelResponse (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) (s : TrueSlot I bits cfg b B) : Option (Hit n b B k) :=
  ((PortGraph.slots I bits cfg hT hnd).test s).map
    (fun hit => (PortGraph.name cfg hit.1, source I bits cfg hT hit.2))

def toRuntimeHit (hit : Name n × AmbientSlot n b B k) : Hit n b B k :=
  (hit.1, ⟨hit.2.1, hit.2.2⟩)

theorem raw_encoding (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) (C : Vertex I bits cfg B) (i : Fin (b * B * k))
    (cache : Cache Q) (hc : Cache.Correct bits cache) :
    ((LocalAccess.slotResult I.weight bits cfg (canonicalFrame I cfg b B C.val)
      ((slotEquiv b B k).symm i) cache).value.1).map encode =
        modelResponse I bits cfg hT hnd ⟨C, i⟩ := by
  have he := PortGraph.slot_result_encoded I bits cfg hT hnd C ((slotEquiv b B k).symm i) cache hc
  simp only [Equiv.apply_symm_apply] at he
  let actual := (LocalAccess.slotResult I.weight bits cfg (canonicalFrame I cfg b B C.val)
    ((slotEquiv b B k).symm i) cache).value.1
  let tested := (PortGraph.slots (b := b) I bits cfg hT hnd).test ⟨C, i⟩
  change actual.map PortGraph.encodeReply = tested.map (PortGraph.encodeTest I bits cfg hT) at he
  change actual.map encode = tested.map (fun hit => (PortGraph.name cfg hit.1, source I bits cfg hT hit.2))
  cases ha : actual with
  | none =>
    cases ht : tested with
    | none => rfl
    | some hit => simp only [ha, ht, Option.map_none, Option.map_some] at he; cases he
  | some reply =>
    cases ht : tested with
    | none => simp only [ha, ht, Option.map_none, Option.map_some] at he; cases he
    | some hit =>
      simp only [ha, ht, Option.map_some] at he
      have hh := Option.some.inj he
      apply congrArg some
      apply Prod.ext
      · exact congrArg (fun p : Name n × AmbientSlot n b B k => p.1) hh
      · apply Sigma.ext (congrArg (fun p : Name n × AmbientSlot n b B k => p.2.1) hh)
        exact heq_of_eq (congrArg (fun p : Name n × AmbientSlot n b B k => p.2.2) hh)

theorem slot_correct (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) (s : TrueSlot I bits cfg b B)
    (memory : Memory Q n b B) (hm : Inv I bits cfg hT memory)
    (hr : Ready I bits cfg hT memory s.1) :
    let result := slotResult I.weight bits cfg (source I bits cfg hT s) memory
    result.value.1 = modelResponse I bits cfg hT hnd s ∧
      Inv I bits cfg hT result.value.2 ∧
      ∀ C, Ready I bits cfg hT memory C → Ready I bits cfg hT result.value.2 C := by
  rcases s with ⟨C, i⟩
  obtain ⟨table, hframes, hget⟩ := hr
  let answer := LocalAccess.slotResult I.weight bits cfg (canonicalFrame I cfg b B C.val)
    ((slotEquiv b B k).symm i) memory.cache
  have hcache := LocalAccess.slot_cache_correct I.weight bits cfg (canonicalFrame I cfg b B C.val)
    ((slotEquiv b B k).symm i) memory.cache hm.1
  have hvalue := raw_encoding I bits cfg hT hnd C i memory.cache hm.1
  simp only [slotResult, source, hframes, hget, Outcome.add, Outcome.combine, Outcome.pure]
  change (finishSlot memory table answer.value).1 = modelResponse I bits cfg hT hnd ⟨C, i⟩ ∧
    Inv I bits cfg hT (finishSlot memory table answer.value).2 ∧
    ∀ D, Ready I bits cfg hT memory D → Ready I bits cfg hT (finishSlot memory table answer.value).2 D
  refine ⟨hvalue, ?_⟩
  cases he : answer.value.1 with
  | none =>
    simp only [finishSlot, he]
    refine ⟨⟨hcache, hm.2.1, ?_⟩, ?_⟩
    · intro t ht
      have h := Option.some.inj ht
      rw [← h]
      exact hm.2.2 table hframes
    · intro D hD
      exact ⟨table, rfl, ready_table I bits cfg hT memory table hframes D hD⟩
  | some reply =>
    obtain ⟨D, hf, hroot⟩ := PortGraph.slot_result_frame I bits cfg hT hnd C
      ((slotEquiv b B k).symm i) memory.cache hm.1 reply he
    simp only [finishSlot, he]
    simp only [hf, hroot]
    refine ⟨⟨hcache, hm.2.1, ?_⟩, ?_⟩
    · intro t ht
      have h := Option.some.inj ht
      rw [← h]
      exact table_set_valid I bits cfg hT table (hm.2.2 table hframes) D
    · intro E hE
      exact ⟨_, rfl, table_set_preserves I bits cfg hT table D E
        (ready_table I bits cfg hT memory table hframes E hE)⟩

noncomputable def presentation (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup)
    (P : Matching.Padded.Parameters (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd))
    (Nstar : ℕ) (hN : P.Nstar = Nstar) :
    Matching.Padded.Presentation (Label := Name n) (PortGraph.slots I bits cfg hT hnd) P
      (config n b B k Nstar) where
  vertex := rootEmbedding I bits cfg B hT
  label := nameEmbedding I bits cfg b B hnd
  length_eq _ := rfl
  size_eq := hN

noncomputable def contract (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup)
    (P : Matching.Padded.Parameters (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd))
    (Nstar : ℕ) (hN : P.Nstar = Nstar)
    (frame : Frame n b B) (cache : Cache Q) (C0 : Vertex I bits cfg B)
    (hf : frame = canonicalFrame I cfg b B C0.val) (hc : Cache.Correct bits cache) :
    Matching.Padded.Presentation.Contract (presentation I bits cfg hT hnd P Nstar hN)
      (primitives cfg frame cache) I.weight bits where
  Inv := Inv I bits cfg hT
  Ready := Ready I bits cfg hT
  initial := initial_inv I bits cfg hT C0 frame hf cache hc
  prepare := by
    intro C memory hm
    exact Matching.Padded.Causal.ensures_of_evaluates I.weight bits _ _
      (prepare_evaluates I.weight bits cfg (rootEmbedding I bits cfg B hT C) memory) _
      (prepare_correct I bits cfg hT hnd memory hm C)
  slot := by
    intro s memory hm hr
    exact Matching.Padded.Causal.ensures_of_evaluates I.weight bits _ _
      (slot_evaluates I.weight bits cfg (source I bits cfg hT s) memory) _
      (slot_correct I bits cfg hT hnd s memory hm hr)

theorem deterministic (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup)
    (P : Matching.Padded.Parameters (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd))
    (Nstar : ℕ) (hN : P.Nstar = Nstar)
    (frame : Frame n b B) (cache : Cache Q) (C0 : Vertex I bits cfg B)
    (hf : frame = canonicalFrame I cfg b B C0.val) (hc : Cache.Correct bits cache) :
    Matching.Padded.Presentation.Deterministic (presentation I bits cfg hT hnd P Nstar hN)
      (primitives cfg frame cache) I.weight bits
      (contract I bits cfg hT hnd P Nstar hN frame cache C0 hf hc) where
  prepare C memory _ := ⟨_, prepare_evaluates I.weight bits cfg (rootEmbedding I bits cfg B hT C) memory⟩
  slot s memory _ _ := ⟨_, slot_evaluates I.weight bits cfg (source I bits cfg hT s) memory⟩

end SteinerUpperBound.PortGraph.RuntimeAdapter
