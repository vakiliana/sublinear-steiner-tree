module

public import SteinerUpperBound.Matching.Padded.Adaptive

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Oracle

open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] (P : Parameters S)

noncomputable def idealScan (S : Slots G) (P : Parameters S)
    (call : Entry S P.rankCard → Cache S P.rankCard → Memo E →
      (E → Fin P.rankCard) → LocalRun S P.rankCard Bool)
    (v : V) (cutoff cursor : ℕ) :
    ℕ → Cache S P.rankCard → Memo E → (E → Fin P.rankCard) →
      LocalRun S P.rankCard (Option (Entry S P.rankCard))
  | 0, s, μ, _ => ⟨none, μ, s, []⟩
  | fuel + 1, s, μ, ranks =>
    let answer := Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks
    match answer.1 with
    | none => ⟨none, μ, answer.2, []⟩
    | some x =>
      if x.rank.val < cutoff then
        let r := call x answer.2 μ ranks
        if r.value then ⟨some x, r.memo, r.cache, r.calls⟩ else
          let t := idealScan S P call v cutoff (cursor + 1) fuel r.cache r.memo ranks
          ⟨t.value, t.memo, t.cache, r.calls ++ t.calls⟩
      else ⟨none, μ, answer.2, []⟩

noncomputable def idealEdge (S : Slots G) (P : Parameters S) (d : Directed E)
    (rank : Fin P.rankCard) (ancestors : List (Directed E)) (s : Cache S P.rankCard)
    (μ : Memo E) (ranks : E → Fin P.rankCard) : LocalRun S P.rankCard Bool :=
  match μ d with
  | some b => ⟨b, μ, s, [⟨d, ancestors, true⟩]⟩
  | none =>
    let r := idealScan S P (fun x t ν world =>
      if _hr : x.rank.val < rank.val then
        idealEdge S P (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν world
      else ⟨false, ν, t, []⟩)
      (G.head d) rank.val 0 (P.Nstar + 1) s μ ranks
    ⟨r.value.isNone, Function.update r.memo d (some r.value.isNone), r.cache,
      ⟨d, ancestors, false⟩ :: r.calls⟩
termination_by rank.val
decreasing_by exact _hr

noncomputable def idealRootCall (v : V) (x : Entry S P.rankCard) (s : Cache S P.rankCard)
    (μ : Memo E) (ranks : E → Fin P.rankCard) : LocalRun S P.rankCard Bool :=
  idealEdge S P (G.away v x.edge) x.rank [] s μ ranks

noncomputable def idealVertex (v : V) (ranks : E → Fin P.rankCard) :
    LocalRun S P.rankCard (Option E) :=
  (idealScan S P (idealRootCall S P v)
    v P.rankCard 0 (P.Nstar + 1) (Cache.empty S P.rankCard) (fun _ => none) ranks).mapValue
      (Option.map Entry.edge)

theorem idealVertex_cache (v : V) (ranks : E → Fin P.rankCard) :
    (idealVertex S P v ranks).cache =
      (idealScan S P (idealRootCall S P v) v P.rankCard 0 (P.Nstar + 1)
        (Cache.empty S P.rankCard) (fun _ => none) ranks).cache :=
  LocalRun.mapValue_cache _ _

theorem scan_joint [Fintype E]
    (call : Entry S P.rankCard → Cache S P.rankCard → Memo E →
      Program (Command S) (LocalRun S P.rankCard Bool))
    (idealCall : Entry S P.rankCard → Cache S P.rankCard → Memo E →
      (E → Fin P.rankCard) → LocalRun S P.rankCard Bool)
    (hcall : ∀ x s μ, Joint P.rankCard_pos s LocalRun.cache (call x s μ) (idealCall x s μ))
    (v : V) (cutoff cursor fuel : ℕ) (s : Cache S P.rankCard) (μ : Memo E) :
    Joint P.rankCard_pos s LocalRun.cache (scan S P call v cutoff cursor fuel s μ)
      (idealScan S P idealCall v cutoff cursor fuel s μ) := by
  induction fuel generalizing cursor s μ with
  | zero =>
    exact Joint.ret _ rfl
  | succ fuel ih =>
    let step : (Option (Entry S P.rankCard) × Cache S P.rankCard) →
        (E → Fin P.rankCard) → LocalRun S P.rankCard (Option (Entry S P.rankCard)) :=
      fun answer ranks =>
        match answer.1 with
        | none => ⟨none, μ, answer.2, []⟩
        | some x =>
          if x.rank.val < cutoff then
            let r := idealCall x answer.2 μ ranks
            if r.value then ⟨some x, r.memo, r.cache, r.calls⟩ else
              let t := idealScan S P idealCall v cutoff (cursor + 1) fuel r.cache r.memo ranks
              ⟨t.value, t.memo, t.cache, r.calls ++ t.calls⟩
          else ⟨none, μ, answer.2, []⟩
    intro f
    rw [scan, Program.expect_bind]
    calc
      _ = (Cache.next S P.rankCard P.rankCard_pos P.sortHeight (P.rankExponent + 1)
          v cursor s).expect (fun answer =>
            (Cache.completion S P.rankCard P.rankCard_pos answer.2).expect
              (fun ranks => f (step answer ranks) ranks)) := by
        have hj := Cache.next_joint S P.rankCard P.rankCard_pos P.sortHeight
          (P.rankExponent + 1) v cursor s (fun answer ranks => f (step answer ranks) ranks)
        convert hj using 1
        apply congrArg (Cache.completion S P.rankCard P.rankCard_pos s).expect
        funext ranks
        rw [idealScan]
        dsimp only [step]
        cases (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks).1 <;>
          rfl
      _ = _ := by
        apply congrArg (Program.expect (Cache.next S P.rankCard P.rankCard_pos P.sortHeight
          (P.rankExponent + 1) v cursor s))
        funext answer
        cases hx : answer.1 with
        | none => simp only [step, hx, Program.expect_ret]
        | some x =>
          by_cases hr : x.rank.val < cutoff
          · simp only [step, hx, hr, ↓reduceIte, Program.expect_bind]
            let finish : LocalRun S P.rankCard Bool → (E → Fin P.rankCard) →
                LocalRun S P.rankCard (Option (Entry S P.rankCard)) :=
              fun r ranks =>
                if r.value then ⟨some x, r.memo, r.cache, r.calls⟩ else
                  let t := idealScan S P idealCall v cutoff (cursor + 1) fuel r.cache r.memo ranks
                  ⟨t.value, t.memo, t.cache, r.calls ++ t.calls⟩
            calc
              _ = (call x answer.2 μ).expect (fun r =>
                  (Cache.completion S P.rankCard P.rankCard_pos r.cache).expect
                    (fun ranks => f (finish r ranks) ranks)) :=
                hcall x answer.2 μ (fun r ranks => f (finish r ranks) ranks)
              _ = _ := by
                apply congrArg (Program.expect (call x answer.2 μ))
                funext r
                cases hv : r.value with
                | true => simp only [finish, hv, ↓reduceIte, Program.expect_ret]
                | false =>
                  simp only [finish, hv, Bool.false_eq_true, ↓reduceIte,
                    Program.expect_bind, Program.expect_tick, Program.expect_ret]
                  exact ih (cursor + 1) r.cache r.memo
                    (fun t ranks => f ⟨t.value, t.memo, t.cache, r.calls ++ t.calls⟩ ranks)
          · simp only [step, hx, hr, ↓reduceIte, Program.expect_ret]

theorem edge_joint [Fintype E] (d : Directed E) (rank : Fin P.rankCard)
    (ancestors : List (Directed E)) (s : Cache S P.rankCard) (μ : Memo E) :
    Joint P.rankCard_pos s LocalRun.cache (edge S P d rank ancestors s μ)
      (idealEdge S P d rank ancestors s μ) := by
  let call := fun (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E) =>
    if _hr : x.rank.val < rank.val then
      edge S P (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν
    else .ret ⟨false, ν, t, []⟩
  let idealCall := fun (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E)
      (world : E → Fin P.rankCard) =>
    if _hr : x.rank.val < rank.val then
      idealEdge S P (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν world
    else ⟨false, ν, t, []⟩
  have hcall (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E) :
      Joint P.rankCard_pos t LocalRun.cache (call x t ν) (idealCall x t ν) := by
    dsimp only [call, idealCall]
    by_cases hr : x.rank.val < rank.val
    · simp only [hr, ↓reduceDIte]
      exact edge_joint (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν
    · simp only [hr, ↓reduceDIte]
      exact Joint.ret _ rfl
  intro f
  rw [edge, Program.expect_tick]
  cases hm : μ d with
  | some b =>
    simp only [Program.expect_ret]
    apply congrArg (Cache.completion S P.rankCard P.rankCard_pos s).expect
    funext ranks
    rw [idealEdge, hm]
  | none =>
    simp only [Program.expect_bind, Program.expect_tick, Program.expect_ret]
    have hj := scan_joint S P call idealCall hcall (G.head d) rank.val 0 (P.Nstar + 1) s μ
      (fun r ranks => f
        ⟨r.value.isNone, Function.update r.memo d (some r.value.isNone), r.cache,
          ⟨d, ancestors, false⟩ :: r.calls⟩ ranks)
    convert hj using 1
    apply congrArg (Cache.completion S P.rankCard P.rankCard_pos s).expect
    funext ranks
    rw [idealEdge, hm]
termination_by rank.val
decreasing_by exact hr

theorem vertex_joint [Fintype E] (v : V) :
    Joint P.rankCard_pos (Cache.empty S P.rankCard) LocalRun.cache (vertex S P v)
      (idealVertex S P v) := by
  intro f
  rw [vertex, Program.expect_tick, Program.expect_bind]
  simp only [Program.expect_ret]
  exact scan_joint S P (rootCall S P v) (idealRootCall S P v)
    (fun x s μ => edge_joint S P (G.away v x.edge) x.rank [] s μ)
    v P.rankCard 0 (P.Nstar + 1) (Cache.empty S P.rankCard) (fun _ => none)
    (fun r ranks => f ⟨r.value.map Entry.edge, r.memo, r.cache, r.calls⟩ ranks)

end SteinerUpperBound.Matching.Padded.Oracle
