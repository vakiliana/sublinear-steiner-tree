module

public import SteinerUpperBound.LocalAccess.Slot

@[expose] public section

namespace SteinerUpperBound.LocalAccess

open QueryProgram
open scoped Classical

set_option maxHeartbeats 1600000

variable {Q : Type} {n k b B : ℕ}

theorem index_counters {d : ℕ} (get : Fin d → Option (Fin n)) (x : Fin n) :
    (indexResult get x).metricQueries = 0 ∧ (indexResult get x).retentionQueries = 0 ∧
      (indexResult get x).positiveReplies = 0 :=
  indexScan_counters get x _

theorem finish_work (cfg : SlotConfig Q n k) (v x y : Fin n)
    (other : Frame (Fin n) b B) (ci : Fin b) (cache : Cache Q) :
    (finishResult cfg v x y other ci cache).work ≤ 2 * B + 2 * k + 5 := by
  have hp := index_work other.pointSlots.get y
  have ht := index_work (fun i => some (cfg.terminals.get i)) x
  cases hpi : (indexResult other.pointSlots.get y).value <;>
    cases hti : (indexResult (fun i => some (cfg.terminals.get i)) x).value <;>
    cases hr : other.points.head? <;>
    simp only [finishResult, Bind.bind, hpi, hti, hr, replyResult, Outcome.combine,
      Outcome.add, Outcome.pure] <;> omega

theorem finish_counters (cfg : SlotConfig Q n k) (v x y : Fin n)
    (other : Frame (Fin n) b B) (ci : Fin b) (cache : Cache Q) :
    (finishResult cfg v x y other ci cache).metricQueries = 0 ∧
      (finishResult cfg v x y other ci cache).retentionQueries = 0 ∧
      (finishResult cfg v x y other ci cache).positiveReplies = 0 := by
  have hp := index_counters other.pointSlots.get y
  have ht := index_counters (fun i => some (cfg.terminals.get i)) x
  cases hpi : (indexResult other.pointSlots.get y).value <;>
    cases hti : (indexResult (fun i => some (cfg.terminals.get i)) x).value <;>
    cases hr : other.points.head? <;>
    simp only [finishResult, Bind.bind, hpi, hti, hr, replyResult, Outcome.combine,
      Outcome.add, Outcome.pure, hp.1, hp.2.1, hp.2.2, ht.1, ht.2.1, ht.2.2,
      Nat.zero_add, true_and]

theorem finish_cache (cfg : SlotConfig Q n k) (v x y : Fin n)
    (other : Frame (Fin n) b B) (ci : Fin b) (cache : Cache Q) :
    (finishResult cfg v x y other ci cache).value.2 = cache := by
  cases hpi : (indexResult other.pointSlots.get y).value <;>
    cases hti : (indexResult (fun i => some (cfg.terminals.get i)) x).value <;>
    cases hr : other.points.head? <;>
    simp only [finishResult, Bind.bind, hpi, hti, hr, replyResult, Outcome.combine,
      Outcome.add, Outcome.pure]

def eligibilityBudget (k B : ℕ) : ℕ :=
  (4 * B + 12) * (k + 1) + 2 * B + 2 * k + 7

theorem eligibility_work (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n) (current other : Frame (Fin n) b B)
    (ci : Fin b) (cache : Cache Q) (hc : current.points.length ≤ B) (ho : other.points.length ≤ B) :
    (eligibilityResult w bits cfg v x y current other ci cache).work ≤ eligibilityBudget k B := by
  have ht := third_work w bits cfg.key (5 * cfg.scale / 8) v
    current.points other.points cfg.terminals.toList cache
  have hs := Nat.mul_le_mul_right (k + 1) (show
    2 * (current.points.length + other.points.length) + 12 ≤ 4 * B + 12 by omega)
  simp only [Vector.length_toList] at ht
  have hf := finish_work cfg v x y other ci
    (thirdResult w bits cfg.key (5 * cfg.scale / 8) v current.points other.points
      cfg.terminals.toList cache).value.cache
  cases he : (thirdResult w bits cfg.key (5 * cfg.scale / 8) v current.points other.points
      cfg.terminals.toList cache).value.found <;>
    simp only [eligibilityResult, Bind.bind, he, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_false, ite_true, replyResult, Outcome.combine, Outcome.add, Outcome.pure,
      eligibilityBudget] <;> omega

theorem eligibility_positive (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n) (current other : Frame (Fin n) b B)
    (ci : Fin b) (cache : Cache Q) :
    (eligibilityResult w bits cfg v x y current other ci cache).positiveReplies ≤ 1 := by
  have ht := third_positive w bits cfg.key (5 * cfg.scale / 8) v
    current.points other.points cfg.terminals.toList cache
  have hf := (finish_counters cfg v x y other ci
    (thirdResult w bits cfg.key (5 * cfg.scale / 8) v current.points other.points
      cfg.terminals.toList cache).value.cache).2.2
  cases he : (thirdResult w bits cfg.key (5 * cfg.scale / 8) v current.points other.points
      cfg.terminals.toList cache).value.found <;>
    simp only [eligibilityResult, Bind.bind, he, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_false, ite_true, replyResult, Outcome.combine, Outcome.add, Outcome.pure,
      hf] <;> omega

theorem eligibility_cache (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n) (current other : Frame (Fin n) b B)
    (ci : Fin b) (cache : Cache Q) :
    (eligibilityResult w bits cfg v x y current other ci cache).value.2 =
      (thirdResult w bits cfg.key (5 * cfg.scale / 8) v current.points other.points
        cfg.terminals.toList cache).value.cache := by
  cases he : (thirdResult w bits cfg.key (5 * cfg.scale / 8) v current.points other.points
      cfg.terminals.toList cache).value.found <;>
    simp only [eligibilityResult, Bind.bind, he, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_false, ite_true, replyResult, Outcome.combine, Outcome.add, Outcome.pure,
      finish_cache]

def mutualBudget (k b B : ℕ) : ℕ :=
  2 * B + 2 * b + eligibilityBudget k B + 4

theorem mutual_work (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n) (current other : Frame (Fin n) b B)
    (cache : Cache Q) (hc : current.points.length ≤ B) (ho : other.points.length ≤ B) :
    (mutualResult w bits cfg v x y current other cache).work ≤ mutualBudget k b B := by
  have hh := hits_work cfg.covered other.points
  have hi := index_work other.rows.slots.get v
  cases hd : (hitsResult cfg.covered other.points).value with
  | true =>
      simp only [mutualResult, Bind.bind, hd, ite_true, replyResult, Outcome.combine,
        Outcome.add, Outcome.pure, mutualBudget]
      omega
  | false =>
      cases hj : (indexResult other.rows.slots.get v).value with
      | none =>
          simp only [mutualResult, Bind.bind, hd, Bool.false_eq_true, ite_false, hj,
            replyResult, Outcome.combine, Outcome.add, Outcome.pure, mutualBudget]
          omega
      | some ci =>
          have he := eligibility_work w bits cfg v x y current other ci cache hc ho
          simp only [mutualResult, Bind.bind, hd, Bool.false_eq_true, ite_false, hj,
            Outcome.combine, mutualBudget]
          omega

theorem mutual_positive (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n) (current other : Frame (Fin n) b B) (cache : Cache Q) :
    (mutualResult w bits cfg v x y current other cache).positiveReplies ≤ 1 := by
  have hh := (hits_counters cfg.covered other.points).2.2
  have hi := (index_counters other.rows.slots.get v).2.2
  cases hd : (hitsResult cfg.covered other.points).value with
  | true =>
      simp only [mutualResult, Bind.bind, hd, ite_true, replyResult, Outcome.combine,
        Outcome.add, Outcome.pure, hh]
      omega
  | false =>
      cases hj : (indexResult other.rows.slots.get v).value with
      | none =>
          simp only [mutualResult, Bind.bind, hd, Bool.false_eq_true, ite_false, hj,
            replyResult, Outcome.combine, Outcome.add, Outcome.pure, hh, hi]
          omega
      | some ci =>
          have he := eligibility_positive w bits cfg v x y current other ci cache
          simpa only [mutualResult, Bind.bind, hd, Bool.false_eq_true, ite_false, hj,
            Outcome.combine, hh, hi, Nat.zero_add] using he

theorem mutual_cache_correct (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n) (current other : Frame (Fin n) b B)
    (cache : Cache Q) (hc : Cache.Correct bits cache) :
    Cache.Correct bits (mutualResult w bits cfg v x y current other cache).value.2 := by
  have he := third_cache_correct w bits cfg.key (5 * cfg.scale / 8) v
    current.points other.points cfg.terminals.toList cache hc
  cases hd : (hitsResult cfg.covered other.points).value <;>
    cases hj : (indexResult other.rows.slots.get v).value <;>
    simp only [mutualResult, Bind.bind, hd, Bool.false_eq_true, ite_false, ite_true, hj,
      replyResult, Outcome.combine, Outcome.add, Outcome.pure, eligibility_cache] <;>
    first | exact hc | exact he

def partnerBudget (n k b B : ℕ) : ℕ :=
  locateBudget n k b B + mutualBudget k b B + 2

theorem partner_work (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n) (current : Frame (Fin n) b B)
    (cache : Cache Q) (hc : Cache.Correct bits cache) (hC : current.points.length ≤ B)
    (hT : cfg.terminals.toList.Nodup)
    (hy : y ∈ ComponentExplore.retained bits cfg.key cfg.terminals.toList.toFinset) :
    (partnerResult w bits cfg v x y current cache).work ≤ partnerBudget n k b B := by
  have hl := locate_work w bits cfg.key cfg.scale b B (List.finRange n)
    cfg.terminals.toList y cache hc hT
    (by simpa only [ComponentExplore.retained, Finset.mem_filter, List.mem_toFinset] using hy)
  simp only [List.length_finRange, Vector.length_toList] at hl
  cases ho : (locateResult w bits cfg.key cfg.scale b B (List.finRange n)
      cfg.terminals.toList y cache).value.frame with
  | none =>
      simp only [partnerResult, Bind.bind, ho, replyResult, Outcome.combine, Outcome.add,
        Outcome.pure, partnerBudget]
      omega
  | some other =>
      have hs := locate_some w bits cfg.key cfg.scale b B (List.finRange n)
        cfg.terminals.toList y cache hc hT
        (by simpa only [ComponentExplore.retained, Finset.mem_filter, List.mem_toFinset] using hy) other ho
      have hm := mutual_work w bits cfg v x y current other
        (locateResult w bits cfg.key cfg.scale b B (List.finRange n)
          cfg.terminals.toList y cache).value.cache hC hs.2.2
      simp only [partnerResult, Bind.bind, ho, Outcome.combine, partnerBudget]
      omega

theorem partner_positive (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n) (current : Frame (Fin n) b B) (cache : Cache Q) :
    (partnerResult w bits cfg v x y current cache).positiveReplies ≤ B + 1 := by
  have hl := locate_positive w bits cfg.key cfg.scale b B (List.finRange n)
    cfg.terminals.toList y cache
  cases ho : (locateResult w bits cfg.key cfg.scale b B (List.finRange n)
      cfg.terminals.toList y cache).value.frame with
  | none =>
      simp only [partnerResult, Bind.bind, ho, replyResult, Outcome.combine, Outcome.add,
        Outcome.pure]
      omega
  | some other =>
      have hm := mutual_positive w bits cfg v x y current other
        (locateResult w bits cfg.key cfg.scale b B (List.finRange n)
          cfg.terminals.toList y cache).value.cache
      simp only [partnerResult, Bind.bind, ho, Outcome.combine]
      omega

theorem partner_cache_correct (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (v x y : Fin n) (current : Frame (Fin n) b B)
    (cache : Cache Q) (hc : Cache.Correct bits cache) :
    Cache.Correct bits (partnerResult w bits cfg v x y current cache).value.2 := by
  have hl := locate_cache_correct w bits cfg.key cfg.scale b B (List.finRange n)
    cfg.terminals.toList y cache hc
  cases ho : (locateResult w bits cfg.key cfg.scale b B (List.finRange n)
      cfg.terminals.toList y cache).value.frame <;>
    simp only [partnerResult, Bind.bind, ho, replyResult, Outcome.combine, Outcome.add,
      Outcome.pure]
  · exact hl
  · exact mutual_cache_correct w bits cfg v x y current _ _ hl

noncomputable def Heavy (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (current : Frame (Fin n) b B) (slot : PortSlot b B k) : Prop :=
  match current.rows.slots.get slot.1, current.pointSlots.get slot.2.1 with
  | some v, some x =>
      let y := cfg.terminals.get slot.2.2
      cfg.covered.get y = false ∧ y ∉ current.points ∧
        w (Sym2.mk v x) ≤ 5 * cfg.scale / 8 ∧
        w (Sym2.mk v y) ≤ 5 * cfg.scale / 8 ∧ bits (cfg.key y) = true
  | _, _ => False

theorem terminal_get_mem (cfg : SlotConfig Q n k) (i : Fin k) :
    cfg.terminals.get i ∈ cfg.terminals.toList := by
  apply List.mem_iff_get.mpr
  refine ⟨⟨i.val, by simpa only [Vector.length_toList] using i.isLt⟩, ?_⟩
  simp [Vector.get_eq_getElem]

theorem slot_work (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (current : Frame (Fin n) b B) (slot : PortSlot b B k)
    (cache : Cache Q) (hc : Cache.Correct bits cache) (hC : current.points.length ≤ B)
    (hT : cfg.terminals.toList.Nodup) :
    (slotResult w bits cfg current slot cache).work ≤
      2 * B + 64 + if Heavy w bits cfg current slot then partnerBudget n k b B else 0 := by
  cases hv : current.rows.slots.get slot.1 with
  | none =>
      simp only [slotResult, Heavy, Bind.bind, hv, replyResult, Outcome.combine,
        Outcome.add, Outcome.pure, ite_false]
      omega
  | some v =>
      cases hx : current.pointSlots.get slot.2.1 with
      | none =>
          simp only [slotResult, Heavy, Bind.bind, hv, hx, replyResult, Outcome.combine,
            Outcome.add, Outcome.pure, ite_false]
          omega
      | some x =>
          let y := cfg.terminals.get slot.2.2
          have hm := ComponentExplore.member_work y current.points
          have hr := Cache.resolved_work_le bits (cfg.key y) cache
          have hb := (Cache.resolved_correct bits (cfg.key y) cache hc).1
          cases hd : cfg.covered.get y with
          | true =>
              dsimp only [y] at *
              simp only [slotResult, Heavy, Bind.bind, hv, hx, hd, Bool.true_eq_false,
                ite_true, ite_false, false_and, replyResult, Outcome.combine, Outcome.add, Outcome.pure]
              omega
          | false =>
              cases hs : (ComponentExplore.memberResult y current.points).value with
              | true =>
                  have hmem := (ComponentExplore.member_value y current.points).mp hs
                  dsimp only [y] at *
                  simp only [slotResult, Heavy, Bind.bind, hv, hx, hd, hs, Bool.false_eq_true,
                    ite_true, ite_false, hmem, not_true_eq_false, and_false, false_and,
                    replyResult, Outcome.combine, Outcome.add, Outcome.pure]
                  omega
              | false =>
                  have hnot : y ∉ current.points := by
                    intro hy
                    have hh := (ComponentExplore.member_value y current.points).mpr hy
                    simp only [hs, Bool.false_eq_true] at hh
                  by_cases hn : w (Sym2.mk v x) ≤ 5 * cfg.scale / 8 ∧
                      w (Sym2.mk v y) ≤ 5 * cfg.scale / 8
                  · cases ht : (Cache.resolved bits (cfg.key y) cache).value.1 with
                    | false =>
                        have hbit : bits (cfg.key y) = false := hb.symm.trans ht
                        dsimp only [y] at *
                        simp only [slotResult, Heavy, Bind.bind, hv, hx, hd, hs, hn.1, hn.2,
                          ht, hbit, Bool.false_eq_true, Bool.not_false, Bool.not_true, ite_true,
                          ite_false, decide_true, decide_false, and_false, false_and, true_and,
                          replyResult, Outcome.combine, Outcome.add, Outcome.pure]
                        omega
                    | true =>
                        have hbit : bits (cfg.key y) = true := hb.symm.trans ht
                        have hret : y ∈ ComponentExplore.retained bits cfg.key cfg.terminals.toList.toFinset := by
                          apply Finset.mem_filter.mpr
                          exact ⟨List.mem_toFinset.mpr (terminal_get_mem cfg slot.2.2), hbit⟩
                        have hcache := (Cache.resolved_correct bits (cfg.key y) cache hc).2
                        have hp := partner_work w bits cfg v x y current
                          (Cache.resolved bits (cfg.key y) cache).value.2 hcache hC hT hret
                        dsimp only [y] at *
                        simp only [slotResult, Heavy, Bind.bind, hv, hx, hd, hs, hn.1, hn.2,
                          ht, hbit, hnot, Bool.false_eq_true, Bool.not_false, Bool.not_true,
                          ite_true, ite_false, decide_true, decide_false, true_and,
                          not_false_eq_true, replyResult, Outcome.combine, Outcome.add, Outcome.pure]
                        cases hknown : cache (cfg.key (cfg.terminals.get slot.2.2)) <;>
                          simp only [Cache.resolved, hknown] at hp ⊢ <;> omega
                  · dsimp only [y] at *
                    have hheavy : ¬ Heavy w bits cfg current slot := by
                      simp only [Heavy, hv, hx]
                      exact fun h => hn ⟨h.2.2.1, h.2.2.2.1⟩
                    simp only [slotResult, Bind.bind, hv, hx, hd, hs, hn, hnot,
                      Bool.false_eq_true, Bool.not_false, Bool.not_true, ite_true, ite_false,
                      decide_true, decide_false, true_and, replyResult, Outcome.combine,
                      Outcome.add, Outcome.pure, hheavy]
                    omega

theorem slot_positive (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (current : Frame (Fin n) b B) (slot : PortSlot b B k)
    (cache : Cache Q) (hc : Cache.Correct bits cache) :
    (slotResult w bits cfg current slot cache).positiveReplies ≤
      if Heavy w bits cfg current slot then B + 2 else 0 := by
  cases hv : current.rows.slots.get slot.1 <;> cases hx : current.pointSlots.get slot.2.1
  all_goals
    try { simp only [slotResult, Heavy, Bind.bind, hv, hx, replyResult, Outcome.combine,
      Outcome.add, Outcome.pure, ite_false]; omega }
  rename_i v x
  let y := cfg.terminals.get slot.2.2
  have hm := (ComponentExplore.member_counters y current.points).2.2
  have hb := (Cache.resolved_correct bits (cfg.key y) cache hc).1
  have hr := ComponentExplore.resolved_positive_bit bits (cfg.key y) cache
  cases hd : cfg.covered.get y <;>
    cases hs : (ComponentExplore.memberResult y current.points).value
  all_goals
    dsimp only [y] at *
    try { simp only [slotResult, Bind.bind, hv, hx, hd, hs, Bool.false_eq_true,
      ite_true, ite_false, replyResult, Outcome.combine, Outcome.add, Outcome.pure, hm]; omega }
  have hnot : y ∉ current.points := by
    intro hy
    have hh := (ComponentExplore.member_value y current.points).mpr hy
    dsimp only [y] at hh
    simp only [hs, Bool.false_eq_true] at hh
  by_cases hn : w (Sym2.mk v x) ≤ 5 * cfg.scale / 8 ∧ w (Sym2.mk v y) ≤ 5 * cfg.scale / 8
  · cases ht : (Cache.resolved bits (cfg.key y) cache).value.1 with
    | false =>
        have hbit : bits (cfg.key y) = false := hb.symm.trans ht
        dsimp only [y] at *
        simp only [ht, Bool.false_eq_true, ite_false] at hr
        simp only [slotResult, Bind.bind, hv, hx, hd, hs, hn, ht, Bool.false_eq_true,
          Bool.not_false, Bool.not_true, ite_true, ite_false, decide_true, replyResult,
          Outcome.combine, Outcome.add, Outcome.pure, hm, true_and]
        omega
    | true =>
        have hbit : bits (cfg.key y) = true := hb.symm.trans ht
        have hp := partner_positive w bits cfg v x y current
          (Cache.resolved bits (cfg.key y) cache).value.2
        dsimp only [y] at *
        simp only [ht, ite_true] at hr
        simp only [slotResult, Heavy, Bind.bind, hv, hx, hd, hs, hn.1, hn.2, ht, hbit, hnot,
          Bool.false_eq_true, Bool.not_false, Bool.not_true, ite_true, ite_false, decide_true,
          true_and, not_false_eq_true, Outcome.combine, Outcome.add, Outcome.pure, hm]
        cases hknown : cache (cfg.key (cfg.terminals.get slot.2.2)) <;>
          simp only [Cache.resolved, hknown, hbit, ite_true] at hp ⊢ <;> omega
  · dsimp only [y] at *
    simp only [slotResult, Bind.bind, hv, hx, hd, hs, hn, Bool.false_eq_true,
      Bool.not_false, Bool.not_true, ite_true, ite_false, decide_false, replyResult,
      Outcome.combine, Outcome.add, Outcome.pure, hm]
    omega

theorem slot_cache_correct (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (current : Frame (Fin n) b B) (slot : PortSlot b B k)
    (cache : Cache Q) (hc : Cache.Correct bits cache) :
    Cache.Correct bits (slotResult w bits cfg current slot cache).value.2 := by
  cases hv : current.rows.slots.get slot.1 <;> cases hx : current.pointSlots.get slot.2.1
  all_goals
    try { simpa only [slotResult, Bind.bind, hv, hx, replyResult, Outcome.combine,
      Outcome.add, Outcome.pure] using hc }
  rename_i v x
  let y := cfg.terminals.get slot.2.2
  have hr := Cache.resolved_correct bits (cfg.key y) cache hc
  have hp := partner_cache_correct w bits cfg v x y current
    (Cache.resolved bits (cfg.key y) cache).value.2 hr.2
  cases hd : cfg.covered.get y <;>
    cases hs : (ComponentExplore.memberResult y current.points).value
  all_goals
    dsimp only [y] at *
    try { simpa only [slotResult, Bind.bind, hv, hx, hd, hs, Bool.false_eq_true,
      ite_true, ite_false, replyResult, Outcome.combine, Outcome.add, Outcome.pure] using hc }
  by_cases hn : w (Sym2.mk v x) ≤ 5 * cfg.scale / 8 ∧
      w (Sym2.mk v y) ≤ 5 * cfg.scale / 8
  · cases ht : (Cache.resolved bits (cfg.key y) cache).value.1 <;>
      dsimp only [y] at * <;>
      simp only [slotResult, Bind.bind, hv, hx, hd, hs, hn, ht, Bool.false_eq_true,
        Bool.not_false, Bool.not_true, ite_true, ite_false, decide_true, replyResult,
        Outcome.combine, Outcome.add, Outcome.pure, true_and]
    · exact hr.2
    · exact hp
  · dsimp only [y] at *
    simpa only [slotResult, Bind.bind, hv, hx, hd, hs, hn, Bool.false_eq_true,
      Bool.not_false, ite_true, ite_false, decide_false, replyResult, Outcome.combine,
      Outcome.add, Outcome.pure] using hc

theorem slot_metric_queries (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (cfg : SlotConfig Q n k) (current : Frame (Fin n) b B) (slot : PortSlot b B k)
    (cache : Cache Q) (hc : Cache.Correct bits cache) (hC : current.points.length ≤ B)
    (hT : cfg.terminals.toList.Nodup) :
    (slotResult w bits cfg current slot cache).metricQueries ≤
      2 * B + 64 + if Heavy w bits cfg current slot then partnerBudget n k b B else 0 := by
  have ha := (slot_evaluates w bits cfg current slot cache).accounted w bits _ _ |>.1
  have hw := slot_work w bits cfg current slot cache hc hC hT
  omega

end SteinerUpperBound.LocalAccess
