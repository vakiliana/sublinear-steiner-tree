module

public import SteinerUpperBound.PortGraph.RuntimeAdapter.Correct
public import SteinerUpperBound.AccessAccounts

@[expose] public section

namespace SteinerUpperBound.PortGraph.RuntimeAdapter

open QueryProgram
open scoped Classical

variable {n k b B : ℕ} {Q : Type}

def preparationBudget (n k b B : ℕ) : ℕ := n + 20 + LocalAccess.locateBudget n k b B

noncomputable def isHeavy (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (s : TrueSlot I bits cfg b B) : Prop :=
  LocalAccess.Heavy I.weight bits cfg (canonicalFrame I cfg b B s.1.val) ((slotEquiv b B k).symm s.2)

noncomputable def workCharge (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (s : TrueSlot I bits cfg b B) : ℕ :=
  2 * B + 76 + if isHeavy I bits cfg s then LocalAccess.partnerBudget n k b B else 0

noncomputable def positiveCharge (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (s : TrueSlot I bits cfg b B) : ℕ :=
  if isHeavy I bits cfg s then B + 2 else 0

def workCap (n k b B : ℕ) : ℕ :=
  preparationBudget n k b B + 2 * B + 76 + LocalAccess.partnerBudget n k b B + 1

theorem prepareLoaded_resources (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) (C : Vertex I bits cfg B)
    (memory : Memory Q n b B) (hc : Cache.Correct bits memory.cache) (table : Table n b B) :
    let o := prepareLoadedResult I.weight bits cfg (rootEmbedding I bits cfg B hT C) memory table
    o.work ≤ LocalAccess.locateBudget n k b B + 8 ∧ o.positiveReplies ≤ B := by
  have hxN := vertex_subset I bits cfg B C (componentRoot_mem I bits cfg B hT C)
  have hx : rootEmbedding I bits cfg B hT C ∈ exploreSet bits cfg.key cfg.terminals.toList := by
    rw [exploreSet_eq I bits cfg hT]
    exact hxN
  have hw := LocalAccess.locate_work I.weight bits cfg.key cfg.scale b B (List.finRange n)
    cfg.terminals.toList (rootEmbedding I bits cfg B hT C) memory.cache hc hnd hx
  have hp := LocalAccess.locate_positive I.weight bits cfg.key cfg.scale b B (List.finRange n)
    cfg.terminals.toList (rootEmbedding I bits cfg B hT C) memory.cache
  simp only [List.length_finRange, Vector.length_toList] at hw
  cases he : table.get (rootEmbedding I bits cfg B hT C) with
  | some frame => simp [prepareLoadedResult, he, Outcome.pure]
  | none =>
    simp only [prepareLoadedResult, he, Outcome.combine, Outcome.add, Outcome.pure]
    omega

theorem prepare_resources (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) (C : Vertex I bits cfg B)
    (memory : Memory Q n b B) (hc : Cache.Correct bits memory.cache) :
    let o := prepareResult I.weight bits cfg (rootEmbedding I bits cfg B hT C) memory
    o.work ≤ preparationBudget n k b B ∧ o.positiveReplies ≤ B := by
  cases he : memory.frames with
  | none =>
    have hr := prepareLoaded_resources I bits cfg hT hnd C (initialized memory) hc (seedTable memory.seed)
    simp only [prepareResult, he, Outcome.add, preparationBudget]
    omega
  | some table =>
    have hr := prepareLoaded_resources I bits cfg hT hnd C memory hc table
    simp only [prepareResult, he, Outcome.add, preparationBudget]
    omega

theorem slot_resources (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) (s : TrueSlot I bits cfg b B)
    (memory : Memory Q n b B) (hm : Inv I bits cfg hT memory) (hr : Ready I bits cfg hT memory s.1) :
    let o := slotResult I.weight bits cfg (source I bits cfg hT s) memory
    o.work ≤ workCharge I bits cfg s ∧ o.positiveReplies ≤ positiveCharge I bits cfg s := by
  rcases s with ⟨C, i⟩
  obtain ⟨table, hframes, hget⟩ := hr
  have hlen : (canonicalFrame I cfg b B C.val).points.length ≤ B := by
    rw [canonicalFrame_points, pointList_length I cfg hT hnd C.val
      ((vertex_subset I bits cfg B C).trans (retained_subset I bits cfg))]
    exact vertex_card_le I bits cfg B C
  have hw := LocalAccess.slot_work I.weight bits cfg (canonicalFrame I cfg b B C.val)
    ((slotEquiv b B k).symm i) memory.cache hm.1 hlen hnd
  have hp := LocalAccess.slot_positive I.weight bits cfg (canonicalFrame I cfg b B C.val)
    ((slotEquiv b B k).symm i) memory.cache hm.1
  simp only [slotResult, source, hframes, hget, Outcome.add, Outcome.combine, Outcome.pure,
    workCharge, positiveCharge, isHeavy]
  by_cases hh : LocalAccess.Heavy I.weight bits cfg (canonicalFrame I cfg b B C.val) ((slotEquiv b B k).symm i)
  · simp only [hh, ite_true] at hw hp ⊢
    omega
  · simp only [hh, ite_false] at hw hp ⊢
    omega

noncomputable def workCounter : Matching.Padded.Causal.Counter :=
  ⟨1, 0, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩

noncomputable def positiveCounter : Matching.Padded.Causal.Counter :=
  ⟨0, 0, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem workCounter_value {R : Type*} (o : Outcome R) :
    workCounter.value o = (o.work : ℝ) := by
  simp [workCounter, Matching.Padded.Causal.Counter.value]

theorem positiveCounter_value {R : Type*} (o : Outcome R) :
    positiveCounter.value o = (o.positiveReplies : ℝ) := by
  simp [positiveCounter, Matching.Padded.Causal.Counter.value]

noncomputable def workAccount (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) :
    Matching.Padded.Account (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd) where
  Cstar := workCap n k b B
  rate := 1
  slot s := workCharge I bits cfg s
  preparation _ := preparationBudget n k b B
  rate_nonneg := by norm_num
  rate_le_Cstar := by
    have h : 1 ≤ workCap n k b B := by unfold workCap; omega
    exact_mod_cast h
  rate_le_slot s := by
    have h : 1 ≤ workCharge I bits cfg s := by unfold workCharge; omega
    exact_mod_cast h
  slot_le s := by
    have h : workCharge I bits cfg s ≤ workCap n k b B := by
      unfold workCharge workCap
      split_ifs <;> omega
    exact_mod_cast h
  preparation_nonneg _ := Nat.cast_nonneg _
  preparation_le _ := by
    have h : preparationBudget n k b B ≤ workCap n k b B := by unfold workCap; omega
    exact_mod_cast h
  Cstar_nonneg := Nat.cast_nonneg _

noncomputable def positiveAccount (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) :
    Matching.Padded.Account (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd) where
  Cstar := B + 2
  rate := 0
  slot s := positiveCharge I bits cfg s
  preparation _ := B + 2
  rate_nonneg := le_rfl
  rate_le_Cstar := by positivity
  rate_le_slot _ := Nat.cast_nonneg _
  slot_le s := by
    have h : positiveCharge I bits cfg s ≤ B + 2 := by
      unfold positiveCharge
      split_ifs <;> omega
    exact_mod_cast h
  preparation_nonneg _ := by positivity
  preparation_le _ := le_rfl
  Cstar_nonneg := by positivity

section PresentationResources

variable (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
  (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
  (P : Matching.Padded.Parameters (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd))
  (Nstar : ℕ) (hN : P.Nstar = Nstar) (frame : Frame n b B) (cache : Cache Q)
  (C0 : Vertex I bits cfg B) (hf : frame = canonicalFrame I cfg b B C0.val) (hc : Cache.Correct bits cache)

theorem workResources :
    Matching.Padded.Presentation.Resources (presentation I bits cfg hT hnd P Nstar hN)
      (primitives cfg frame cache) I.weight bits (contract I bits cfg hT hnd P Nstar hN frame cache C0 hf hc)
      (workAccount I bits cfg hT hnd) workCounter where
  rate := rfl
  prepare := by
    intro C memory hm
    have h : (prepare cfg (rootEmbedding I bits cfg B hT C) memory).evaluate I.weight bits workCounter.value ≤
        (preparationBudget n k b B : ℝ) := by
      rw [prepare_evaluates I.weight bits cfg (rootEmbedding I bits cfg B hT C) memory, workCounter_value]
      exact_mod_cast (prepare_resources I bits cfg hT hnd C memory hm.1).1
    exact h
  slot := by
    intro s memory hm hr
    have h : (slot cfg (source I bits cfg hT s) memory).evaluate I.weight bits workCounter.value ≤
        (workCharge I bits cfg s : ℝ) := by
      rw [slot_evaluates I.weight bits cfg (source I bits cfg hT s) memory, workCounter_value]
      exact_mod_cast (slot_resources I bits cfg hT hnd s memory hm hr).1
    exact h

theorem positiveResources :
    Matching.Padded.Presentation.Resources (presentation I bits cfg hT hnd P Nstar hN)
      (primitives cfg frame cache) I.weight bits (contract I bits cfg hT hnd P Nstar hN frame cache C0 hf hc)
      (positiveAccount I bits cfg hT hnd) positiveCounter where
  rate := rfl
  prepare := by
    intro C memory hm
    have h : (prepare cfg (rootEmbedding I bits cfg B hT C) memory).evaluate I.weight bits positiveCounter.value ≤
        ((B : ℝ) + 2) := by
      rw [prepare_evaluates I.weight bits cfg (rootEmbedding I bits cfg B hT C) memory, positiveCounter_value]
      have h := (prepare_resources I bits cfg hT hnd C memory hm.1).2
      exact_mod_cast h.trans (Nat.le_add_right B 2)
    exact h
  slot := by
    intro s memory hm hr
    have h : (slot cfg (source I bits cfg hT s) memory).evaluate I.weight bits positiveCounter.value ≤
        (positiveCharge I bits cfg s : ℝ) := by
      rw [slot_evaluates I.weight bits cfg (source I bits cfg hT s) memory, positiveCounter_value]
      exact_mod_cast (slot_resources I bits cfg hT hnd s memory hm hr).2
    exact h

end PresentationResources

end SteinerUpperBound.PortGraph.RuntimeAdapter
