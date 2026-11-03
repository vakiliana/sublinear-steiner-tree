module

public import SteinerUpperBound.PortGraph
public import SteinerUpperBound.Matching.Padded.Presentation

@[expose] public section

namespace SteinerUpperBound.PortGraph.RuntimeAdapter

open QueryProgram
open scoped Classical

variable {n k b B : ℕ} {Q : Type}

abbrev Frame (n b B : ℕ) := LocalAccess.Frame (Fin n) b B
abbrev Table (n b B : ℕ) := Vector (Option (Frame n b B)) n

structure Memory (Q : Type) (n b B : ℕ) where
  frames : Option (Table n b B)
  seed : Frame n b B
  cache : Cache Q

/-- No root-indexed array is allocated here. Its linear initialization is
performed and charged by the first actual `prepare` call. -/
def initial (frame : Frame n b B) (cache : Cache Q) : Memory Q n b B :=
  ⟨none, frame, cache⟩

def seedTable (frame : Frame n b B) : Table n b B :=
  match frame.points.head? with
  | none => Vector.replicate n none
  | some root => (Vector.replicate n none).set root.val (some frame) root.isLt

def initialized (memory : Memory Q n b B) : Memory Q n b B :=
  { memory with frames := some (seedTable memory.seed) }

def finishPrepare (memory : Memory Q n b B) (table : Table n b B) (root : Fin n)
    (located : LocalAccess.Located (Fin n) Q b B) : Memory Q n b B :=
  { memory with
    frames := some (match located.frame with
      | none => table
      | some frame => table.set root.val (some frame) root.isLt)
    cache := located.cache }

abbrev length (n b B k : ℕ) : Fin n → ℕ := fun _ => b * B * k
abbrev Slot (n b B k : ℕ) := Matching.Padded.Slot (length n b B k)
abbrev Hit (n b B k : ℕ) := Name n × Slot n b B k

def encode (reply : LocalAccess.PortReply n k b B) : Hit n b B k :=
  (reply.name, ⟨reply.otherRoot, slotEquiv b B k reply.reverse⟩)

def finishSlot (memory : Memory Q n b B) (table : Table n b B)
    (answer : Option (LocalAccess.PortReply n k b B) × Cache Q) :
    Option (Hit n b B k) × Memory Q n b B :=
  (answer.1.map encode,
    { memory with
      frames := some (match answer.1 with
        | none => table
        | some reply => table.set reply.otherRoot.val (some reply.other) reply.otherRoot.isLt)
      cache := answer.2 })

noncomputable def prepareLoaded (cfg : LocalAccess.SlotConfig Q n k) (root : Fin n)
    (memory : Memory Q n b B) (table : Table n b B) : Code (Sym2 (Fin n)) Q (Memory Q n b B) :=
  match table.get root with
  | some _ => .pure memory
  | none =>
    (LocalAccess.locateProgram cfg.key cfg.scale b B (List.finRange n) cfg.terminals.toList root memory.cache).bind
      (fun located => .tick 7 (.pure (finishPrepare memory table root located)))

noncomputable def prepare (cfg : LocalAccess.SlotConfig Q n k) (root : Fin n)
    (memory : Memory Q n b B) : Code (Sym2 (Fin n)) Q (Memory Q n b B) :=
  .tick 3 (match memory.frames with
    | none => .tick (n + 7) (prepareLoaded cfg root (initialized memory) (seedTable memory.seed))
    | some table => prepareLoaded cfg root memory table)

/-- A slot never prepares a frame. Successful heavy replies already carry the
partner's canonical frame, which is inserted in the indexed table. -/
noncomputable def slot (cfg : LocalAccess.SlotConfig Q n k) (s : Slot n b B k)
    (memory : Memory Q n b B) :
    Code (Sym2 (Fin n)) Q (Option (Hit n b B k) × Memory Q n b B) :=
  .tick 3 (match memory.frames with
    | none => .pure (none, memory)
    | some table =>
      match table.get s.1 with
      | none => .pure (none, memory)
      | some frame =>
        (LocalAccess.slotProgram cfg frame ((slotEquiv b B k).symm s.2) memory.cache).bind
          (fun answer => .tick 7 (.pure (finishSlot memory table answer))))

noncomputable def prepareLoadedResult (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (root : Fin n)
    (memory : Memory Q n b B) (table : Table n b B) : Outcome (Memory Q n b B) :=
  match table.get root with
  | some _ => .pure memory
  | none =>
    let located := LocalAccess.locateResult w bits cfg.key cfg.scale b B (List.finRange n)
      cfg.terminals.toList root memory.cache
    located.combine (.add 8 0 0 0 (.pure (finishPrepare memory table root located.value)))

noncomputable def prepareResult (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (root : Fin n)
    (memory : Memory Q n b B) : Outcome (Memory Q n b B) :=
  .add 4 0 0 0 (match memory.frames with
    | none => .add (n + 8) 0 0 0
        (prepareLoadedResult w bits cfg root (initialized memory) (seedTable memory.seed))
    | some table => prepareLoadedResult w bits cfg root memory table)

noncomputable def slotResult (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (s : Slot n b B k)
    (memory : Memory Q n b B) : Outcome (Option (Hit n b B k) × Memory Q n b B) :=
  .add 4 0 0 0 (match memory.frames with
    | none => .pure (none, memory)
    | some table =>
      match table.get s.1 with
      | none => .pure (none, memory)
      | some frame =>
        let answer := LocalAccess.slotResult w bits cfg frame ((slotEquiv b B k).symm s.2) memory.cache
        answer.combine (.add 8 0 0 0 (.pure (finishSlot memory table answer.value))))

theorem prepareLoaded_evaluates (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (root : Fin n)
    (memory : Memory Q n b B) (table : Table n b B) :
    Code.Evaluates w bits (prepareLoaded cfg root memory table)
      (prepareLoadedResult w bits cfg root memory table) := by
  intro F
  cases he : table.get root with
  | some frame => simp only [prepareLoaded, prepareLoadedResult, he, Code.evaluate]
  | none =>
    simp only [prepareLoaded, prepareLoadedResult, he]
    rw [Code.evaluate_bind, LocalAccess.locate_evaluates]
    rfl

theorem prepare_evaluates (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (root : Fin n) (memory : Memory Q n b B) :
    Code.Evaluates w bits (prepare cfg root memory) (prepareResult w bits cfg root memory) := by
  intro F
  cases he : memory.frames with
  | none =>
    simp only [prepare, prepareResult, he, Code.evaluate]
    exact prepareLoaded_evaluates w bits cfg root _ _ _
  | some table =>
    simp only [prepare, prepareResult, he, Code.evaluate]
    exact prepareLoaded_evaluates w bits cfg root _ _ _

theorem slot_evaluates (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (s : Slot n b B k) (memory : Memory Q n b B) :
    Code.Evaluates w bits (slot cfg s memory) (slotResult w bits cfg s memory) := by
  intro F
  cases he : memory.frames with
  | none => simp only [slot, slotResult, he, Code.evaluate]
  | some table =>
    cases hf : table.get s.1 with
    | none => simp only [slot, slotResult, he, hf, Code.evaluate]
    | some frame =>
      simp only [slot, slotResult, he, hf, Code.evaluate]
      rw [Code.evaluate_bind, LocalAccess.slot_evaluates]
      rfl

def config (n b B k Nstar : ℕ) : Matching.Padded.Runtime.Config (Fin n) :=
  ⟨length n b B k, Nstar⟩

noncomputable def primitives (cfg : LocalAccess.SlotConfig Q n k)
    (frame : Frame n b B) (cache : Cache Q) :
    Matching.Padded.Runtime.Primitives (length n b B k) (Name n) (Sym2 (Fin n)) Q where
  Memory := Memory Q n b B
  initial := initial frame cache
  prepare := prepare cfg
  slot := slot cfg

/-- Concrete VO entrypoint. Matching/rank memo is fresh per call; primitive
frame/cache memory is returned. The generic VO law/accounting is separate. -/
noncomputable def oracle (cfg : LocalAccess.SlotConfig Q n k) (Nstar : ℕ)
    (frame : Frame n b B) (cache : Cache Q) : Code (Sym2 (Fin n)) Q (Bool × Cache Q) :=
  .tick 7 (match frame.points.head? with
    | none => .pure (false, cache)
    | some root =>
      (Matching.Padded.Runtime.answer (config n b B k Nstar) (primitives cfg frame cache) root).bind
        (fun answer => .tick 3 (.pure (answer.1, answer.2.cache))))

end SteinerUpperBound.PortGraph.RuntimeAdapter
