module

public import SteinerUpperBound.PortGraph.RuntimeAdapter.Resources

@[expose] public section

namespace SteinerUpperBound.PortGraph.RuntimeAdapter

open QueryProgram
open scoped Classical

variable {n k b B : ℕ} {Q : Type}

theorem prepare_ready_evaluates (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Vertex I bits cfg B) (memory : Memory Q n b B) (hr : Ready I bits cfg hT memory C) :
    Code.Evaluates I.weight bits (prepare cfg (rootEmbedding I bits cfg B hT C) memory)
      (.add 4 0 0 0 (.pure memory)) := by
  obtain ⟨table, hframes, hget⟩ := hr
  have h := prepare_evaluates I.weight bits cfg (rootEmbedding I bits cfg B hT C) memory
  simpa only [prepareResult, hframes, prepareLoadedResult, hget] using h

theorem seedTable_get (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Vertex I bits cfg B) :
    (seedTable (canonicalFrame I cfg b B C.val)).get (rootEmbedding I bits cfg B hT C) =
      some (canonicalFrame I cfg b B C.val) := by
  rw [seedTable, frame_head I bits cfg b B hT C]
  exact table_set_self _ _ _

/-- First preparation only initializes the public-root array and reuses the
supplied canonical frame. It makes ZERO metric/retention queries or positives. -/
theorem prepare_initial_evaluates (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Vertex I bits cfg B) (cache : Cache Q) :
    Code.Evaluates I.weight bits
      (prepare cfg (rootEmbedding I bits cfg B hT C) (initial (canonicalFrame I cfg b B C.val) cache))
      (.add (n + 12) 0 0 0 (.pure (initialized (initial (canonicalFrame I cfg b B C.val) cache)))) := by
  have h := prepare_evaluates I.weight bits cfg (rootEmbedding I bits cfg B hT C)
    (initial (canonicalFrame I cfg b B C.val) cache)
  have he :
      prepareResult I.weight bits cfg (rootEmbedding I bits cfg B hT C)
          (initial (canonicalFrame I cfg b B C.val) cache) =
        .add (n + 12) 0 0 0 (.pure (initialized (initial (canonicalFrame I cfg b B C.val) cache))) := by
    simp only [prepareResult, initial, prepareLoadedResult, seedTable_get]
    simp only [Outcome.add, Outcome.pure]
    congr 1 <;> omega
  rwa [he] at h

/-- An accepted partner already has its prepared canonical frame in the table;
the generic runtime's later prepare request is a four-work cache hit. -/
theorem slot_partner_ready (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) (s : TrueSlot I bits cfg b B)
    (memory : Memory Q n b B) (hm : Inv I bits cfg hT memory) (hr : Ready I bits cfg hT memory s.1)
    (e : Copy I bits cfg b B) (t : TrueSlot I bits cfg b B)
    (ht : (PortGraph.slots I bits cfg hT hnd).test s = some (e, t)) :
    Ready I bits cfg hT (slotResult I.weight bits cfg (source I bits cfg hT s) memory).value.2 t.1 := by
  rcases s with ⟨C, i⟩
  obtain ⟨table, hframes, hget⟩ := hr
  let raw := (slotEquiv b B k).symm i
  let answer := LocalAccess.slotResult I.weight bits cfg (canonicalFrame I cfg b B C.val) raw memory.cache
  have ht' : (PortGraph.slots I bits cfg hT hnd).test ⟨C, slotEquiv b B k raw⟩ = some (e, t) := by
    have hi : slotEquiv b B k raw = i := (slotEquiv b B k).apply_symm_apply i
    rw [hi]
    exact ht
  have he := PortGraph.slot_result_encoded I bits cfg hT hnd C raw memory.cache hm.1
  rw [ht'] at he
  cases hanswer : answer.value.1 with
  | none =>
    change answer.value.1.map PortGraph.encodeReply = _ at he
    simp only [hanswer, Option.map_none, Option.map_some] at he
    cases he
  | some reply =>
    have hf := PortGraph.slot_result_frame_exact I bits cfg hT hnd C raw memory.cache hm.1 reply hanswer e t ht'
    change answer.value.1.map PortGraph.encodeReply = _ at he
    simp only [hanswer, Option.map_some] at he
    have hroot := congrArg (fun p : Name n × AmbientSlot n b B k => p.2.1) (Option.some.inj he)
    change reply.otherRoot = rootEmbedding I bits cfg B hT t.1 at hroot
    simp only [slotResult, source, hframes, hget, Outcome.add, Outcome.combine, Outcome.pure]
    change Ready I bits cfg hT (finishSlot memory table answer.value).2 t.1
    simp only [finishSlot, hanswer, hf, hroot]
    exact ⟨_, rfl, table_set_self _ _ _⟩

theorem prepare_partner_evaluates (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) (s : TrueSlot I bits cfg b B)
    (memory : Memory Q n b B) (hm : Inv I bits cfg hT memory) (hr : Ready I bits cfg hT memory s.1)
    (e : Copy I bits cfg b B) (t : TrueSlot I bits cfg b B)
    (ht : (PortGraph.slots I bits cfg hT hnd).test s = some (e, t)) :
    let m' := (slotResult I.weight bits cfg (source I bits cfg hT s) memory).value.2
    Code.Evaluates I.weight bits (prepare cfg (rootEmbedding I bits cfg B hT t.1) m')
      (.add 4 0 0 0 (.pure m')) :=
  prepare_ready_evaluates I bits cfg hT t.1 _
    (slot_partner_ready I bits cfg hT hnd s memory hm hr e t ht)

theorem workCap_le (n k b B : ℕ) (hk : k ≤ n) (hb : b ^ 2 ≤ 50 * (n + 1)) :
    workCap n k b B ≤ 2100 * (n + 1) * (B + 2) ^ 2 := by
  have hp := AccessAccounts.partnerBudget_le n k b B hk hb
  have hl : LocalAccess.locateBudget n k b B ≤ LocalAccess.partnerBudget n k b B := by
    unfold LocalAccess.partnerBudget
    omega
  have hsmall : n + 2 * B + 97 ≤ 100 * (n + 1) * (B + 2) ^ 2 := by
    nlinarith [Nat.zero_le (n * B ^ 2), Nat.zero_le (n * B)]
  unfold workCap preparationBudget
  nlinarith

end SteinerUpperBound.PortGraph.RuntimeAdapter
