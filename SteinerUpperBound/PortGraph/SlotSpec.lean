module

public import SteinerUpperBound.PortGraph.SlotValues

@[expose] public section

namespace SteinerUpperBound.PortGraph

open QueryProgram
open scoped Classical BigOperators
open Covers.Geometry

variable {n k b B : ℕ} {Q : Type}

theorem outcome_bind_value {R S : Type} (a : Outcome R) (f : R → Outcome S) :
    (a >>= f).value = (f a.value).value := rfl

theorem outcome_pure_value {R : Type*} (r : R) : (Outcome.pure r).value = r := rfl

theorem terminal_get_mem (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (i : Fin k) :
    cfg.terminals.get i ∈ I.terminals := by
  apply (terminal_mem I cfg hT _).mp
  apply Vector.mem_toList_iff.mpr
  apply Vector.mem_iff_getElem.mpr
  exact ⟨i.val, i.isLt, (Vector.get_eq_getElem cfg.terminals i).symm⟩

noncomputable def partnerSpec (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (v x y : Fin n) (hx : x ∈ C.val)
    (hy : y ∈ retained I bits cfg) : Option (LocalAccess.PortReply n k b B) :=
  if hD : portComponent I bits cfg y ∈ smallParts I bits cfg B then
    let D : Vertex I bits cfg B := ⟨portComponent I bits cfg y, hD⟩
    if hv : v ∈ lists I bits cfg b D.val then
      if v ∈ eligible I bits cfg then
        some (reply I bits cfg hT hnd D v x y
          ((vertex_subset I bits cfg B C).trans (retained_subset I bits cfg) hx)
          (componentOn_self I _ _ hy) (centerPosition I bits cfg b B hT D v hv))
      else none
    else none
  else none

theorem partner_value (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (v x y : Fin n) (hx : x ∈ C.val)
    (hy : y ∈ retained I bits cfg) (hyC : y ∉ C.val)
    (hdx : I.distance v x ≤ radius cfg) (hdy : I.distance v y ≤ radius cfg)
    (c : Cache Q) (hc : Cache.Correct bits c) :
    (LocalAccess.partnerResult I.weight bits cfg v x y (canonicalFrame I cfg b B C.val) c).value.1 =
      partnerSpec I bits cfg hT hnd C v x y hx hy := by
  classical
  let Cy := portComponent I bits cfg y
  have hCy : Cy ∈ parts I bits cfg := componentOn_mem_componentsOn I _ _ hy
  have hne : C.val ≠ Cy := fun he => hyC (he.symm ▸ componentOn_self I _ _ hy)
  let located := LocalAccess.locateResult I.weight bits cfg.key cfg.scale b B (List.finRange n)
    cfg.terminals.toList y c
  have hl := locate_frame I bits cfg b B hT hnd hy c hc
  have hlc := LocalAccess.locate_cache_correct I.weight bits cfg.key cfg.scale b B (List.finRange n)
    cfg.terminals.toList y c hc
  simp only [LocalAccess.partnerResult, bind, outcomeMonad, Outcome.combine]
  by_cases hD : Cy ∈ smallParts I bits cfg B
  · have hsmall := (Finset.mem_filter.mp hD).2.1
    rw [ite_eq_left hsmall] at hl
    rw [hl]
    rw [partnerSpec, dite_eq_left hD]
    exact mutual_value I bits cfg hT hnd C ⟨Cy, hD⟩ v x y hx
      (componentOn_self I _ _ hy) hne hdx hdy located.value.cache hlc
  · rw [partnerSpec, dite_eq_right hD]
    by_cases hsmall : Cy.card ≤ B
    · rw [ite_eq_left hsmall] at hl
      rw [hl]
      have hnot : ¬ Disjoint Cy (removed I cfg) := fun hd =>
        hD (Finset.mem_filter.mpr ⟨hCy, hsmall, hd⟩)
      have hh := (hits_frame_iff I bits cfg b B hT hCy).mpr hnot
      simp only [LocalAccess.mutualResult, bind, outcomeMonad, Outcome.combine]
      rw [hh]
      simp [LocalAccess.replyResult, Outcome.add, Outcome.pure]
    · rw [ite_eq_right hsmall] at hl
      rw [hl]
      rfl

noncomputable def slotSpec (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (s : LocalAccess.PortSlot b B k) :
    Option (LocalAccess.PortReply n k b B) :=
  match (canonicalFrame I cfg b B C.val).rows.slots.get s.1,
      (canonicalFrame I cfg b B C.val).pointSlots.get s.2.1 with
  | some v, some x =>
    let y := cfg.terminals.get s.2.2
    if hx : x ∈ C.val then
      if hy : y ∈ retained I bits cfg then
        if y ∉ removed I cfg ∧ y ∉ C.val ∧
            I.distance v x ≤ radius cfg ∧ I.distance v y ≤ radius cfg then
          partnerSpec I bits cfg hT hnd C v x y hx hy
        else none
      else none
    else none
  | _, _ => none

theorem member_frame (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (C : Vertex I bits cfg B) (y : Fin n) :
    (ComponentExplore.memberResult y (canonicalFrame I cfg b B C.val).points).value = true ↔ y ∈ C.val := by
  rw [ComponentExplore.member_value, canonicalFrame_points]
  exact pointList_mem I cfg hT C.val
    ((vertex_subset I bits cfg B C).trans (retained_subset I bits cfg)) y

/-- First-component output of the genuine causal slot program is exactly the
finite static geometric test, independently of its incoming correct cache. -/
theorem slot_value (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (s : LocalAccess.PortSlot b B k)
    (c : Cache Q) (hc : Cache.Correct bits c) :
    (LocalAccess.slotResult I.weight bits cfg (canonicalFrame I cfg b B C.val) s c).value.1 =
      slotSpec I bits cfg hT hnd C s := by
  classical
  cases hv : (canonicalFrame I cfg b B C.val).rows.slots.get s.1 with
  | none =>
    simp [LocalAccess.slotResult, bind, outcomeMonad, Outcome.combine, Outcome.add, Outcome.pure,
      LocalAccess.replyResult, hv, slotSpec]
  | some v =>
    cases hx : (canonicalFrame I cfg b B C.val).pointSlots.get s.2.1 with
    | none =>
      simp [LocalAccess.slotResult, bind, outcomeMonad, Outcome.combine, Outcome.add, Outcome.pure,
        LocalAccess.replyResult, hv, hx, slotSpec]
    | some x =>
      have hxC := pointSlot_mem I cfg b B hT C.val
        ((vertex_subset I bits cfg B C).trans (retained_subset I bits cfg)) hx
      simp only [LocalAccess.slotResult, outcome_bind_value, LocalAccess.SlotEvaluation.add_value,
        outcome_pure_value,
        hv, hx, slotSpec, dite_eq_left hxC]
      generalize hydef : cfg.terminals.get s.2.2 = y
      have hyT : y ∈ I.terminals := hydef ▸ terminal_get_mem I cfg hT s.2.2
      have hres := Cache.resolved_correct bits (cfg.key y) c hc
      have hmem := member_frame (b := b) I bits cfg hT C y
      have hcov := not_mem_removed I cfg hyT
      by_cases hyN : y ∈ retained I bits cfg
      · have hb := ((mem_retained I bits cfg y).mp hyN).2
        by_cases hyD : y ∈ removed I cfg
        · have hbD : cfg.covered.get y = true := (Finset.mem_filter.mp hyD).2
          simp [hbD, LocalAccess.replyResult, Outcome.add, Outcome.pure, hyN, hyD]
        · have hbD : cfg.covered.get y = false := hcov.mp hyD
          rw [hbD]
          simp only [Bool.false_eq_true, ite_false, dite_eq_left hyN, outcome_bind_value,
            LocalAccess.SlotEvaluation.add_value, outcome_pure_value]
          by_cases hyC : y ∈ C.val
          · have hm := hmem.mpr hyC
            rw [hm]
            simp [LocalAccess.replyResult, Outcome.add, Outcome.pure, hyC]
          · have hm : (ComponentExplore.memberResult y (canonicalFrame I cfg b B C.val).points).value = false := by
              cases hh : (ComponentExplore.memberResult y (canonicalFrame I cfg b B C.val).points).value <;> simp_all
            rw [hm]
            simp only [Bool.false_eq_true, ite_false, outcome_bind_value,
              LocalAccess.SlotEvaluation.add_value, outcome_pure_value]
            by_cases hd : I.distance v x ≤ radius cfg ∧ I.distance v y ≤ radius cfg
            · have hnear : decide (I.weight s(v, x) ≤ 5 * cfg.scale / 8 ∧
                  I.weight s(v, y) ≤ 5 * cfg.scale / 8) = true := by
                simp only [decide_eq_true_eq, Instance.weight_mk]
                exact hd
              rw [hnear]
              simp only [Bool.not_true, Bool.false_eq_true, ite_false, outcome_bind_value,
                LocalAccess.SlotEvaluation.add_value, outcome_pure_value]
              rw [hres.1, hb]
              simp only [Bool.not_true, Bool.false_eq_true, ite_false]
              rw [ite_eq_left ⟨hyD, hyC, hd⟩]
              exact partner_value I bits cfg hT hnd C v x y hxC hyN hyC hd.1 hd.2 _ hres.2
            · have hnear : decide (I.weight s(v, x) ≤ 5 * cfg.scale / 8 ∧
                  I.weight s(v, y) ≤ 5 * cfg.scale / 8) = false := by
                simp only [decide_eq_false_iff_not, Instance.weight_mk]
                exact hd
              rw [hnear]
              simp [LocalAccess.replyResult, Outcome.add, Outcome.pure, hd]
      · have hb : bits (cfg.key y) = false := by
          cases he : bits (cfg.key y) with
          | false => rfl
          | true => exact (hyN ((mem_retained I bits cfg y).mpr ⟨hyT, he⟩)).elim
        simp only [dite_eq_right hyN]
        cases hD : cfg.covered.get y with
        | true => simp [hD, LocalAccess.replyResult, Outcome.add, Outcome.pure]
        | false =>
          simp only [hD, Bool.false_eq_true, ite_false, outcome_bind_value,
            LocalAccess.SlotEvaluation.add_value, outcome_pure_value]
          cases hm : (ComponentExplore.memberResult y (canonicalFrame I cfg b B C.val).points).value with
          | true => simp [hm, LocalAccess.replyResult, Outcome.add, Outcome.pure]
          | false =>
            simp only [hm, Bool.false_eq_true, ite_false, outcome_bind_value,
              LocalAccess.SlotEvaluation.add_value, outcome_pure_value]
            change (if (!decide (I.weight s(v, x) ≤ 5 * cfg.scale / 8 ∧
                I.weight s(v, y) ≤ 5 * cfg.scale / 8)) = true then
              LocalAccess.replyResult none c
            else (Cache.resolved bits (cfg.key y) c >>= fun z =>
              if (!z.1) = true then LocalAccess.replyResult none z.2
              else LocalAccess.partnerResult I.weight bits cfg v x y
                (canonicalFrame I cfg b B C.val) z.2)).value.1 = none
            split_ifs with hnear
            · rfl
            · simp only [outcome_bind_value, LocalAccess.SlotEvaluation.add_value, outcome_pure_value]
              rw [hres.1, hb]
              simp [LocalAccess.replyResult, Outcome.add, Outcome.pure]

end SteinerUpperBound.PortGraph
