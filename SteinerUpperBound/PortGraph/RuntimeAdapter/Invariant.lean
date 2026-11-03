module

public import SteinerUpperBound.PortGraph.RuntimeAdapter.Basic

@[expose] public section

namespace SteinerUpperBound.PortGraph.RuntimeAdapter

open QueryProgram
open scoped Classical

variable {n k b B : ℕ} {Q : Type}

def TableValid (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (table : Table n b B) : Prop :=
  ∀ root frame, table.get root = some frame →
    ∃ C : Vertex I bits cfg B, rootEmbedding I bits cfg B hT C = root ∧
      frame = canonicalFrame I cfg b B C.val

def Inv (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (memory : Memory Q n b B) : Prop :=
  Cache.Correct bits memory.cache ∧
    (∃ C : Vertex I bits cfg B, memory.seed = canonicalFrame I cfg b B C.val) ∧
    ∀ table, memory.frames = some table → TableValid I bits cfg hT table

def Ready (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (memory : Memory Q n b B) (C : Vertex I bits cfg B) : Prop :=
  ∃ table, memory.frames = some table ∧
    table.get (rootEmbedding I bits cfg B hT C) = some (canonicalFrame I cfg b B C.val)

theorem table_set_self (table : Table n b B) (root : Fin n) (frame : Frame n b B) :
    (table.set root.val (some frame) root.isLt).get root = some frame := by
  simp only [Vector.get_eq_getElem, Vector.getElem_set_self]

theorem table_set_ne (table : Table n b B) (root other : Fin n) (frame : Frame n b B)
    (hne : other ≠ root) :
    (table.set root.val (some frame) root.isLt).get other = table.get other := by
  have hn : root.val ≠ other.val := fun h => hne (Fin.ext h.symm)
  simp only [Vector.get_eq_getElem, Vector.getElem_set_ne root.isLt other.isLt hn]

theorem table_set_valid (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (table : Table n b B) (ht : TableValid I bits cfg hT table) (C : Vertex I bits cfg B) :
    TableValid I bits cfg hT
      (table.set (rootEmbedding I bits cfg B hT C).val (some (canonicalFrame I cfg b B C.val))
        (rootEmbedding I bits cfg B hT C).isLt) := by
  intro root frame hget
  by_cases he : root = rootEmbedding I bits cfg B hT C
  · subst root
    rw [table_set_self] at hget
    exact ⟨C, rfl, (Option.some.inj hget).symm⟩
  · rw [table_set_ne _ _ _ _ he] at hget
    exact ht root frame hget

theorem table_set_preserves (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (table : Table n b B) (C D : Vertex I bits cfg B)
    (hD : table.get (rootEmbedding I bits cfg B hT D) = some (canonicalFrame I cfg b B D.val)) :
    (table.set (rootEmbedding I bits cfg B hT C).val (some (canonicalFrame I cfg b B C.val))
      (rootEmbedding I bits cfg B hT C).isLt).get (rootEmbedding I bits cfg B hT D) =
        some (canonicalFrame I cfg b B D.val) := by
  by_cases he : rootEmbedding I bits cfg B hT D = rootEmbedding I bits cfg B hT C
  · have hDC := (rootEmbedding I bits cfg B hT).injective he
    subst D
    exact table_set_self _ _ _
  · rw [table_set_ne _ _ _ _ he]
    exact hD

theorem table_lookup_canonical (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (table : Table n b B) (ht : TableValid I bits cfg hT table) (C : Vertex I bits cfg B)
    (frame : Frame n b B) (hf : table.get (rootEmbedding I bits cfg B hT C) = some frame) :
    frame = canonicalFrame I cfg b B C.val := by
  obtain ⟨D, hd, hframe⟩ := ht _ frame hf
  have hD := (rootEmbedding I bits cfg B hT).injective hd
  simpa only [hD] using hframe

theorem initial_inv (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Vertex I bits cfg B) (frame : Frame n b B) (hf : frame = canonicalFrame I cfg b B C.val)
    (cache : Cache Q) (hc : Cache.Correct bits cache) :
    Inv I bits cfg hT (initial frame cache) := by
  refine ⟨hc, ⟨C, hf⟩, ?_⟩
  intro table he
  cases he

theorem seedTable_valid (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (frame : Frame n b B) (hf : ∃ C : Vertex I bits cfg B, frame = canonicalFrame I cfg b B C.val) :
    TableValid I bits cfg hT (seedTable frame) := by
  obtain ⟨C, rfl⟩ := hf
  rw [seedTable, frame_head I bits cfg b B hT C]
  apply table_set_valid
  intro root frame hget
  simp only [Vector.get_eq_getElem, Vector.getElem_replicate] at hget
  cases hget

theorem initialized_inv (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (memory : Memory Q n b B) (hm : Inv I bits cfg hT memory) :
    Inv I bits cfg hT (initialized memory) := by
  refine ⟨hm.1, hm.2.1, ?_⟩
  intro table he
  have ht : seedTable memory.seed = table := Option.some.inj he
  rw [← ht]
  exact seedTable_valid I bits cfg hT memory.seed hm.2.1

theorem ready_table (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (memory : Memory Q n b B) (table : Table n b B) (hf : memory.frames = some table)
    (C : Vertex I bits cfg B) (hr : Ready I bits cfg hT memory C) :
    table.get (rootEmbedding I bits cfg B hT C) = some (canonicalFrame I cfg b B C.val) := by
  obtain ⟨t, ht, hget⟩ := hr
  have he : t = table := Option.some.inj (ht.symm.trans hf)
  simpa only [he] using hget

theorem prepareLoaded_correct (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (memory : Memory Q n b B) (hm : Inv I bits cfg hT memory) (table : Table n b B)
    (hf : memory.frames = some table) (C : Vertex I bits cfg B) :
    let result := prepareLoadedResult I.weight bits cfg (rootEmbedding I bits cfg B hT C) memory table
    Inv I bits cfg hT result.value ∧ Ready I bits cfg hT result.value C ∧
      ∀ D, Ready I bits cfg hT memory D → Ready I bits cfg hT result.value D := by
  dsimp only
  cases he : table.get (rootEmbedding I bits cfg B hT C) with
  | some frame =>
    have hcanon := table_lookup_canonical I bits cfg hT table (hm.2.2 table hf) C frame he
    simp only [prepareLoadedResult, he, Outcome.pure]
    exact ⟨hm, ⟨table, hf, he.trans (congrArg some hcanon)⟩, fun _ h => h⟩
  | none =>
    let located := LocalAccess.locateResult I.weight bits cfg.key cfg.scale b B (List.finRange n)
      cfg.terminals.toList (rootEmbedding I bits cfg B hT C) memory.cache
    have hl := locate_root I bits cfg b B hT hnd C memory.cache hm.1
    change located.value.frame = some (canonicalFrame I cfg b B C.val) at hl
    have hc := LocalAccess.locate_cache_correct I.weight bits cfg.key cfg.scale b B (List.finRange n)
      cfg.terminals.toList (rootEmbedding I bits cfg B hT C) memory.cache hm.1
    simp only [prepareLoadedResult, he, Outcome.combine, Outcome.add, Outcome.pure]
    change Inv I bits cfg hT (finishPrepare memory table _ located.value) ∧
      Ready I bits cfg hT (finishPrepare memory table _ located.value) C ∧
      ∀ D, Ready I bits cfg hT memory D → Ready I bits cfg hT (finishPrepare memory table _ located.value) D
    simp only [finishPrepare, hl]
    refine ⟨⟨hc, hm.2.1, ?_⟩, ?_, ?_⟩
    · intro t ht
      have heq := Option.some.inj ht
      rw [← heq]
      exact table_set_valid I bits cfg hT table (hm.2.2 table hf) C
    · exact ⟨_, rfl, table_set_self _ _ _⟩
    · intro D hD
      exact ⟨_, rfl, table_set_preserves I bits cfg hT table C D
        (ready_table I bits cfg hT memory table hf D hD)⟩

theorem prepare_correct (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (memory : Memory Q n b B) (hm : Inv I bits cfg hT memory) (C : Vertex I bits cfg B) :
    let result := prepareResult I.weight bits cfg (rootEmbedding I bits cfg B hT C) memory
    Inv I bits cfg hT result.value ∧ Ready I bits cfg hT result.value C ∧
      ∀ D, Ready I bits cfg hT memory D → Ready I bits cfg hT result.value D := by
  dsimp only
  cases he : memory.frames with
  | some table =>
    simp only [prepareResult, he, Outcome.add]
    exact prepareLoaded_correct I bits cfg hT hnd memory hm table he C
  | none =>
    have hi := initialized_inv I bits cfg hT memory hm
    have hloaded := prepareLoaded_correct I bits cfg hT hnd (initialized memory) hi (seedTable memory.seed) rfl C
    simp only [prepareResult, he, Outcome.add]
    refine ⟨hloaded.1, hloaded.2.1, ?_⟩
    intro D hD
    obtain ⟨table, htable, _⟩ := hD
    rw [he] at htable
    cases htable

end SteinerUpperBound.PortGraph.RuntimeAdapter
