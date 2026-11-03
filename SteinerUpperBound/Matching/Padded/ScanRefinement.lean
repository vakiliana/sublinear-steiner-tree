module

public import SteinerUpperBound.Matching.Padded.Safety
public import SteinerUpperBound.Matching.Padded.OrderedLists

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical

variable {V E A : Type*} {G : Graph V E} {S : Slots G} {Q : ℕ}

def LocalRun.forget (r : LocalRun S Q A) : Graph.Run E A := ⟨r.value, r.memo, r.calls⟩

theorem LocalRun.forget_value (r : LocalRun S Q A) : r.forget.value = r.value := rfl

theorem LocalRun.forget_calls (r : LocalRun S Q A) : r.forget.calls = r.calls := rfl

def LocalRun.forgetScan (r : LocalRun S Q (Option (Entry S Q))) : Graph.Run E (Option E) :=
  ⟨r.value.map Entry.edge, r.memo, r.calls⟩

theorem LocalRun.forget_mapEntries (r : LocalRun S Q (Option (Entry S Q))) :
    (r.mapValue (Option.map Entry.edge)).forget = r.forgetScan := rfl

namespace Oracle

variable (S : Slots G) [Fintype V] [Fintype E] (P : Parameters S)

theorem idealScan_refines
    (call : Entry S P.rankCard → Cache S P.rankCard → Memo E →
      (E → Fin P.rankCard) → LocalRun S P.rankCard Bool)
    (reference : E → Memo E → Graph.Run E Bool)
    (ranks : E → Fin P.rankCard) (hn : Function.Injective ranks)
    (v : V) (cutoff : ℕ)
    (hcall : ∀ x t ν, Cache.Invariant S P.rankCard t → Cache.Consistent S P.rankCard t ranks →
      ranks x.edge = x.rank → x.rank.val < cutoff →
        RunSafe S P.rankCard ranks (call x t ν ranks) ∧
          (call x t ν ranks).forget = reference x.edge ν)
    (cursor fuel : ℕ) (s : Cache S P.rankCard) (μ : Memo E)
    (hs : Cache.Invariant S P.rankCard s) (hc : Cache.Consistent S P.rankCard s ranks)
    (hf : (G.candidates (UniformOrder.order ranks) (Fintype.card E) v).length ≤ cursor + fuel) :
    (idealScan S P call v cutoff cursor fuel s μ ranks).forgetScan =
      Graph.Run.scan reference
        (((G.candidates (UniformOrder.order ranks) (Fintype.card E) v).drop cursor).takeWhile
          (fun e => (ranks e).val < cutoff)) μ := by
  let L := G.candidates (UniformOrder.order ranks) (Fintype.card E) v
  induction fuel generalizing cursor s μ with
  | zero =>
    have hd : L.drop cursor = [] := List.drop_eq_nil_of_le (by simpa using hf)
    dsimp only [L] at hd
    simp only [idealScan, LocalRun.forgetScan, hd, List.takeWhile_nil, Graph.Run.scan, Option.map_none]
  | succ fuel ih =>
    rw [idealScan]
    have hnext := Cache.idealNext_correct S P v cursor s ranks hs hc hn
    cases ha : (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks).1 with
    | none =>
      have hget : L[cursor]? = none := by
        simpa only [ha, Option.map_none] using hnext.value.symm
      have hd := drop_after_exhaustion L cursor hget
      dsimp only [L] at hd
      simp only [hd, List.takeWhile_nil, Graph.Run.scan, LocalRun.forgetScan, Option.map_none]
    | some x =>
      have hget : L[cursor]? = some x.edge := by
        simpa only [ha, Option.map_some] using hnext.value.symm
      have hd := drop_after_lookup L cursor x.edge hget
      have hxrank := (hnext.valid x ha).2.2
      dsimp only
      by_cases hk : x.rank.val < cutoff
      · simp only [hk, ↓reduceIte]
        have hpred : (ranks x.edge).val < cutoff := by simpa only [hxrank] using hk
        rw [hd, List.takeWhile_cons_of_pos (by simpa only [decide_eq_true_eq] using hpred),
          Graph.Run.scan]
        have hr := hcall x _ μ hnext.invariant hnext.consistent hxrank hk
        have hv := congrArg Graph.Run.value hr.2
        have hm := congrArg Graph.Run.memo hr.2
        have hcalls := congrArg Graph.Run.calls hr.2
        dsimp only [LocalRun.forget] at hv hm hcalls
        cases hb : (call x
            (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks).2
            μ ranks).value with
        | true =>
          have htrue : (reference x.edge μ).value = true := hv.symm.trans hb
          simp only [htrue, ↓reduceIte, LocalRun.forgetScan, Option.map_some, hm, hcalls]
        | false =>
          have hfalse : (reference x.edge μ).value = false := hv.symm.trans hb
          simp only [Bool.false_eq_true, ↓reduceIte, hfalse]
          have ht := ih (cursor + 1)
            (call x
              (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks).2
              μ ranks).cache
            (call x
              (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks).2
              μ ranks).memo hr.1.invariant hr.1.consistent (by omega)
          have he := congrArg (fun t : Graph.Run E (Option E) =>
            (⟨t.value, t.memo,
              (call x
                (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks).2
                μ ranks).calls ++ t.calls⟩ : Graph.Run E (Option E))) ht
          simpa only [LocalRun.forgetScan, hm, hcalls] using he
      · simp only [hk, ↓reduceIte]
        have hpred : ¬ (ranks x.edge).val < cutoff := by simpa only [hxrank] using hk
        rw [hd, List.takeWhile_cons_of_neg (by simpa only [decide_eq_true_eq] using hpred)]
        rfl

end Oracle

end SteinerUpperBound.Matching.Padded
