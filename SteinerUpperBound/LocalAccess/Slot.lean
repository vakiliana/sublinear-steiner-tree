module

public import SteinerUpperBound.LocalAccess.Hits

@[expose] public section

namespace SteinerUpperBound.LocalAccess

open QueryProgram
open scoped Classical

set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

abbrev PortSlot (b B k : ℕ) := Fin b × (Fin B × Fin k)

structure SlotConfig (Q : Type*) (n k : ℕ) where
  key : Fin n → Q
  scale : ℝ
  terminals : Vector (Fin n) k
  covered : Vector Bool n

structure PortReply (n k b B : ℕ) where
  otherRoot : Fin n
  other : Frame (Fin n) b B
  reverse : PortSlot b B k
  name : Fin n × Sym2 (Fin n)

variable {Q : Type} {n k b B : ℕ}

def replyProgram (reply : Option (PortReply n k b B)) (cache : Cache Q) :
    Code (Sym2 (Fin n)) Q (Option (PortReply n k b B) × Cache Q) :=
  Code.operation 1 (reply, cache)

def replyResult (reply : Option (PortReply n k b B)) (cache : Cache Q) :
    Outcome (Option (PortReply n k b B) × Cache Q) :=
  (Outcome.pure (reply, cache)).add 2 0 0 0

noncomputable def finishProgram (cfg : SlotConfig Q n k) (v x y : Fin n)
    (other : Frame (Fin n) b B) (ci : Fin b) (cache : Cache Q) :
    Code (Sym2 (Fin n)) Q (Option (PortReply n k b B) × Cache Q) := do
  let pi ← indexProgram other.pointSlots.get y
  let ti ← indexProgram (fun i => some (cfg.terminals.get i)) x
  let root ← Code.operation 0 other.points.head?
  match pi, ti, root with
  | some p, some t, some r =>
      replyProgram (some ⟨r, other, (ci, (p, t)), (v, Sym2.mk x y)⟩) cache
  | _, _, _ => replyProgram none cache

noncomputable def finishResult (cfg : SlotConfig Q n k) (v x y : Fin n)
    (other : Frame (Fin n) b B) (ci : Fin b) (cache : Cache Q) :
    Outcome (Option (PortReply n k b B) × Cache Q) := do
  let pi ← indexResult other.pointSlots.get y
  let ti ← indexResult (fun i => some (cfg.terminals.get i)) x
  let root ← (Outcome.pure other.points.head?).add 1 0 0 0
  match pi, ti, root with
  | some p, some t, some r =>
      replyResult (some ⟨r, other, (ci, (p, t)), (v, Sym2.mk x y)⟩) cache
  | _, _, _ => replyResult none cache

noncomputable def eligibilityProgram (cfg : SlotConfig Q n k) (v x y : Fin n)
    (current other : Frame (Fin n) b B) (ci : Fin b) (cache : Cache Q) :
    Code (Sym2 (Fin n)) Q (Option (PortReply n k b B) × Cache Q) := do
  let eligible ← thirdProgram cfg.key (5 * cfg.scale / 8) v
    current.points other.points cfg.terminals.toList cache
  if !eligible.found then replyProgram none eligible.cache
  else finishProgram cfg v x y other ci eligible.cache

noncomputable def eligibilityResult (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n)
    (current other : Frame (Fin n) b B) (ci : Fin b) (cache : Cache Q) :
    Outcome (Option (PortReply n k b B) × Cache Q) := do
  let eligible ← thirdResult w bits cfg.key (5 * cfg.scale / 8) v
    current.points other.points cfg.terminals.toList cache
  if !eligible.found then replyResult none eligible.cache
  else finishResult cfg v x y other ci eligible.cache

noncomputable def mutualProgram (cfg : SlotConfig Q n k) (v x y : Fin n)
    (current other : Frame (Fin n) b B) (cache : Cache Q) :
    Code (Sym2 (Fin n)) Q (Option (PortReply n k b B) × Cache Q) := do
  let meets ← hitsProgram cfg.covered other.points
  if meets then replyProgram none cache else do
    let ci ← indexProgram other.rows.slots.get v
    match ci with
    | none => replyProgram none cache
    | some i => eligibilityProgram cfg v x y current other i cache

noncomputable def mutualResult (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n)
    (current other : Frame (Fin n) b B) (cache : Cache Q) :
    Outcome (Option (PortReply n k b B) × Cache Q) := do
  let meets ← hitsResult cfg.covered other.points
  if meets then replyResult none cache else do
    let ci ← indexResult other.rows.slots.get v
    match ci with
    | none => replyResult none cache
    | some i => eligibilityResult w bits cfg v x y current other i cache

noncomputable def partnerProgram (cfg : SlotConfig Q n k) (v x y : Fin n)
    (current : Frame (Fin n) b B) (cache : Cache Q) :
    Code (Sym2 (Fin n)) Q (Option (PortReply n k b B) × Cache Q) := do
  let other ← locateProgram cfg.key cfg.scale b B (List.finRange n) cfg.terminals.toList y cache
  match other.frame with
  | none => replyProgram none other.cache
  | some f => mutualProgram cfg v x y current f other.cache

noncomputable def partnerResult (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n) (current : Frame (Fin n) b B) (cache : Cache Q) :
    Outcome (Option (PortReply n k b B) × Cache Q) := do
  let other ← locateResult w bits cfg.key cfg.scale b B (List.finRange n) cfg.terminals.toList y cache
  match other.frame with
  | none => replyResult none other.cache
  | some f => mutualResult w bits cfg v x y current f other.cache

noncomputable def slotProgram (cfg : SlotConfig Q n k) (current : Frame (Fin n) b B)
    (slot : PortSlot b B k) (cache : Cache Q) :
    Code (Sym2 (Fin n)) Q (Option (PortReply n k b B) × Cache Q) := do
  let loaded ← Code.operation 39
    (current.rows.slots.get slot.1, current.pointSlots.get slot.2.1, cfg.terminals.get slot.2.2)
  match loaded with
  | (some v, some x, y) => do
      let covered ← Code.operation 0 (cfg.covered.get y)
      if covered then replyProgram none cache else do
        let same ← ComponentExplore.member y current.points
        if same then replyProgram none cache else do
          let dx ← Code.metric (Sym2.mk v x) Code.pure
          let dy ← Code.metric (Sym2.mk v y) Code.pure
          let near ← Code.operation 2 (decide (dx ≤ 5 * cfg.scale / 8 ∧ dy ≤ 5 * cfg.scale / 8))
          if !near then replyProgram none cache else do
            let (retained, cache') ← Cache.resolve (cfg.key y) cache
            if !retained then replyProgram none cache' else do
              partnerProgram cfg v x y current cache'
  | _ => replyProgram none cache

noncomputable def slotResult (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (current : Frame (Fin n) b B) (slot : PortSlot b B k)
    (cache : Cache Q) : Outcome (Option (PortReply n k b B) × Cache Q) := do
  let loaded ← (Outcome.pure
    (current.rows.slots.get slot.1, current.pointSlots.get slot.2.1,
      cfg.terminals.get slot.2.2)).add 40 0 0 0
  match loaded with
  | (some v, some x, y) => do
      let covered ← (Outcome.pure (cfg.covered.get y)).add 1 0 0 0
      if covered then replyResult none cache else do
        let same ← ComponentExplore.memberResult y current.points
        if same then replyResult none cache else do
          let dx ← (⟨w (Sym2.mk v x), 1, 1, 0, 0⟩ : Outcome ℝ)
          let dy ← (⟨w (Sym2.mk v y), 1, 1, 0, 0⟩ : Outcome ℝ)
          let near ← (Outcome.pure
            (decide (dx ≤ 5 * cfg.scale / 8 ∧ dy ≤ 5 * cfg.scale / 8))).add 3 0 0 0
          if !near then replyResult none cache else do
            let (retained, cache') ← Cache.resolved bits (cfg.key y) cache
            if !retained then replyResult none cache' else do
              partnerResult w bits cfg v x y current cache'
  | _ => replyResult none cache

namespace SlotEvaluation

theorem pure_value {R : Type*} (r : R) : (Outcome.pure r).value = r := rfl

theorem add_value {R : Type*} (o : Outcome R) (w m q z : ℕ) :
    (o.add w m q z).value = o.value := rfl

theorem combine_value {R S : Type*} (a : Outcome R) (b : Outcome S) :
    (a.combine b).value = b.value := rfl

theorem operation (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    {R : Type*} (cost : ℕ) (r : R) (F : Outcome R → ℝ) :
    Code.evaluate w bits (Code.operation cost r) F = F ((Outcome.pure r).add (cost + 1) 0 0 0) :=
  rfl

theorem metric (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (e : Sym2 (Fin n)) (F : Outcome ℝ → ℝ) :
    Code.evaluate w bits (.metric e .pure) F = F ⟨w e, 1, 1, 0, 0⟩ := rfl

theorem member (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (x : Fin n) (l : List (Fin n)) (F : Outcome Bool → ℝ) :
    Code.evaluate w bits (ComponentExplore.member x l) F =
      F (ComponentExplore.memberResult x l) := ComponentExplore.member_evaluates w bits x l F

theorem resolve (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (q : Q) (cache : Cache Q) (F : Outcome (Bool × Cache Q) → ℝ) :
    Code.evaluate w bits (Cache.resolve q cache) F = F (Cache.resolved bits q cache) :=
  Cache.resolve_evaluates w bits q cache F

theorem locate (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (root : Fin n) (cache : Cache Q)
    (F : Outcome (Located (Fin n) Q b B) → ℝ) :
    Code.evaluate w bits (locateProgram cfg.key cfg.scale b B (List.finRange n)
      cfg.terminals.toList root cache) F =
      F (locateResult w bits cfg.key cfg.scale b B (List.finRange n)
        cfg.terminals.toList root cache) :=
  locate_evaluates w bits cfg.key cfg.scale b B (List.finRange n) cfg.terminals.toList root cache F

theorem hits (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (D : Vector Bool n) (l : List (Fin n)) (F : Outcome Bool → ℝ) :
    Code.evaluate w bits (hitsProgram D l) F = F (hitsResult D l) := hits_evaluates w bits D l F

theorem index (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool) {d : ℕ}
    (get : Fin d → Option (Fin n)) (x : Fin n) (F : Outcome (Option (Fin d)) → ℝ) :
    Code.evaluate w bits (indexProgram get x) F = F (indexResult get x) := index_evaluates w bits get x F

theorem third (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v : Fin n) (C D : List (Fin n)) (cache : Cache Q)
    (F : Outcome (ThirdAnswer Q) → ℝ) :
    Code.evaluate w bits (thirdProgram cfg.key (5 * cfg.scale / 8) v C D cfg.terminals.toList cache) F =
      F (thirdResult w bits cfg.key (5 * cfg.scale / 8) v C D cfg.terminals.toList cache) :=
  third_evaluates w bits cfg.key (5 * cfg.scale / 8) v C D cfg.terminals.toList cache F

end SlotEvaluation

theorem finish_evaluate (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n) (other : Frame (Fin n) b B)
    (ci : Fin b) (cache : Cache Q) (F : Outcome (Option (PortReply n k b B) × Cache Q) → ℝ) :
    Code.evaluate w bits (finishProgram cfg v x y other ci cache) F =
      F (finishResult cfg v x y other ci cache) := by
  simp only [finishProgram, finishResult, Bind.bind, Code.evaluate_bind, SlotEvaluation.index,
    SlotEvaluation.operation, SlotEvaluation.pure_value, SlotEvaluation.add_value]
  cases hp : (indexResult other.pointSlots.get y).value <;>
    cases ht : (indexResult (fun i => some (cfg.terminals.get i)) x).value <;>
    cases hr : other.points.head? <;>
    simp only [hp, ht, hr, replyProgram, replyResult, SlotEvaluation.operation]

theorem eligibility_evaluate (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n) (current other : Frame (Fin n) b B)
    (ci : Fin b) (cache : Cache Q) (F : Outcome (Option (PortReply n k b B) × Cache Q) → ℝ) :
    Code.evaluate w bits (eligibilityProgram cfg v x y current other ci cache) F =
      F (eligibilityResult w bits cfg v x y current other ci cache) := by
  simp only [eligibilityProgram, eligibilityResult, Bind.bind, Code.evaluate_bind, SlotEvaluation.third]
  cases he : (thirdResult w bits cfg.key (5 * cfg.scale / 8) v
      current.points other.points cfg.terminals.toList cache).value.found <;>
    simp only [he, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
      replyProgram, replyResult, SlotEvaluation.operation, finish_evaluate]

theorem mutual_evaluate (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n) (current other : Frame (Fin n) b B)
    (cache : Cache Q) (F : Outcome (Option (PortReply n k b B) × Cache Q) → ℝ) :
    Code.evaluate w bits (mutualProgram cfg v x y current other cache) F =
      F (mutualResult w bits cfg v x y current other cache) := by
  simp only [mutualProgram, mutualResult, Bind.bind, Code.evaluate_bind, SlotEvaluation.hits]
  cases hh : (hitsResult cfg.covered other.points).value <;>
    simp only [hh, Bool.false_eq_true, ite_false, ite_true, Code.evaluate_bind, SlotEvaluation.index]
  · cases hi : (indexResult other.rows.slots.get v).value <;>
      simp only [hi, replyProgram, replyResult, SlotEvaluation.operation, eligibility_evaluate]
  · simp only [replyProgram, replyResult, SlotEvaluation.operation]

theorem partner_evaluate (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n) (current : Frame (Fin n) b B)
    (cache : Cache Q) (F : Outcome (Option (PortReply n k b B) × Cache Q) → ℝ) :
    Code.evaluate w bits (partnerProgram cfg v x y current cache) F =
      F (partnerResult w bits cfg v x y current cache) := by
  simp only [partnerProgram, partnerResult, Bind.bind, Code.evaluate_bind, SlotEvaluation.locate]
  cases ho : (locateResult w bits cfg.key cfg.scale b B (List.finRange n)
      cfg.terminals.toList y cache).value.frame <;>
    simp only [ho, replyProgram, replyResult, SlotEvaluation.operation, mutual_evaluate]

theorem slot_evaluates (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (current : Frame (Fin n) b B) (slot : PortSlot b B k)
    (cache : Cache Q) :
    Code.Evaluates w bits (slotProgram cfg current slot cache) (slotResult w bits cfg current slot cache) := by
  intro F
  simp only [slotProgram, slotResult, Bind.bind, Code.evaluate_bind, SlotEvaluation.operation,
    SlotEvaluation.pure_value, SlotEvaluation.add_value]
  cases hv : current.rows.slots.get slot.1 <;> cases hx : current.pointSlots.get slot.2.1 <;>
    simp only [hv, hx, replyProgram, replyResult, SlotEvaluation.operation,
      Code.evaluate_bind, SlotEvaluation.pure_value, SlotEvaluation.add_value]
  rename_i v x
  cases hd : cfg.covered.get (cfg.terminals.get slot.2.2) <;>
    simp only [hd, Bool.false_eq_true, ite_false, ite_true, replyProgram, replyResult,
      SlotEvaluation.operation, Code.evaluate_bind, SlotEvaluation.member]
  cases hm : (ComponentExplore.memberResult (cfg.terminals.get slot.2.2) current.points).value <;>
    simp only [hm, Bool.false_eq_true, ite_false, ite_true, replyProgram, replyResult,
      SlotEvaluation.operation, Code.evaluate_bind, SlotEvaluation.metric,
      SlotEvaluation.pure_value, SlotEvaluation.add_value]
  by_cases hn : w (Sym2.mk v x) ≤ 5 * cfg.scale / 8 ∧
      w (Sym2.mk v (cfg.terminals.get slot.2.2)) ≤ 5 * cfg.scale / 8 <;>
    simp only [hn, decide_true, decide_false, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true, replyProgram, replyResult,
      SlotEvaluation.operation, Code.evaluate_bind, SlotEvaluation.resolve,
      SlotEvaluation.pure_value, SlotEvaluation.add_value, true_and]
  cases hr : (Cache.resolved bits (cfg.key (cfg.terminals.get slot.2.2)) cache).value.1 <;>
    simp only [hr, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
      replyProgram, replyResult, SlotEvaluation.operation, partner_evaluate]

end SteinerUpperBound.LocalAccess
