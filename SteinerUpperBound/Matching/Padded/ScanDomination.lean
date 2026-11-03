module

public import SteinerUpperBound.Matching.Padded.NextDomination
public import SteinerUpperBound.Matching.Padded.RunRefinement

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Presentation

open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical

variable {V E Vertex Label M T : Type*} {G : Graph V E} {S : Slots G} [Fintype V] [Fintype E]
    {P : Parameters S} {C : Runtime.Config Vertex} (J : Presentation (Label := Label) S P C)
    (I : Runtime.Primitives C.length Label M T) (m : M → ℝ) (bits : T → Bool)
    (K : J.Contract I m bits) (D : J.Deterministic I m bits K)
    (A : Account S) (counter : Causal.Counter) (resources : J.Resources I m bits K A counter)

include D resources

theorem scan_dominates
    (call : Entry S C.rankCard → Cache S C.rankCard → Memo E →
      Program (Command S) (LocalRun S C.rankCard Bool))
    (rawCall : Runtime.Copy C (Label := Label) → Runtime.State C I →
      (Label × Vertex → Option Bool) → Runtime.Code M T (Runtime.Result C I Bool))
    (v : V) (cutoff : ℕ)
    (hcall : ∀ x s t μ ν, J.StateMatch I m bits K s t → J.MemoMatch μ ν →
      Cache.Invariant S C.rankCard s → x.source.1 = v → Cache.EntryValid S C.rankCard x →
      x.rank.val < cutoff →
      Causal.Dominates m bits counter (Command.charge A) A.rate
        (call x s μ) (rawCall (J.liftEntry x) t ν) (J.RunMatch I m bits K Eq))
    (cursor fuel : ℕ) (s : Cache S C.rankCard) (t : Runtime.State C I)
    (μ : Memo E) (ν : Label × Vertex → Option Bool)
    (hstate : J.StateMatch I m bits K s t) (hmemo : J.MemoMatch μ ν)
    (hs : Cache.Invariant S C.rankCard s) :
    Causal.Dominates m bits counter (Command.charge A) A.rate
      (Oracle.scan S J.parameters call v cutoff cursor fuel s μ)
      (Runtime.scan C I rawCall (J.vertex v) cutoff cursor fuel t ν)
      (J.RunMatch I m bits K (fun hit raw => raw = hit.map J.liftEntry)) := by
  induction fuel generalizing cursor s t μ ν with
  | zero =>
    exact Causal.Dominates.ret m bits counter _ _ _ _ _
      ⟨rfl, hmemo, hstate, rfl, hs⟩
  | succ fuel ih =>
    have heq := Oracle.scan.eq_def S J.parameters call v cutoff cursor (fuel + 1) s μ
    rw [heq, Runtime.scan]
    apply Causal.Dominates.bind m bits counter (Command.charge A) A.rate _ _ _ _ _ _
      (next_dominates_supported J I m bits K D A counter resources v cursor s t hstate hs)
    intro answer raw hanswer
    have hnext := hanswer.1
    have hinv := hanswer.2.1
    cases hhit : answer.1 with
    | none =>
      have hraw : raw.1 = none := by simpa only [hhit, Option.map_none] using hnext.1
      rw [hraw]
      exact Causal.Dominates.ret m bits counter _ _ _ _ _
        ⟨rfl, hmemo, hnext.2, rfl, hinv⟩
    | some x =>
      have hraw : raw.1 = some (J.liftEntry x) := by simpa only [hhit, Option.map_some] using hnext.1
      rw [hraw]
      dsimp only
      by_cases hk : x.rank.val < cutoff
      · simp only [liftEntry, hk, ↓reduceIte]
        have hx := hanswer.2.2 x hhit
        apply Causal.Dominates.bind m bits counter (Command.charge A) A.rate _ _ _ _ _ _
          (hcall x answer.2 raw.2 μ ν hnext.2 hmemo hinv hx.1 hx.2 hk)
        intro r rawRun hr
        have hv : rawRun.value = r.value := hr.value.symm
        rw [hv]
        cases hb : r.value with
        | true =>
          simp only [↓reduceIte]
          exact Causal.Dominates.ret m bits counter _ _ _ _ _
            ⟨rfl, hr.memo, hr.state, hr.calls, hr.invariant⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          apply Causal.Dominates.bind m bits counter (Command.charge A) A.rate _ _ _ _ _ _
            (ih (cursor + 1) r.cache rawRun.cache r.memo rawRun.memo hr.state hr.memo hr.invariant)
          intro result rawResult hresult
          have hlength : rawRun.calls.length = r.calls.length := by rw [hr.calls, List.length_map]
          apply Causal.Dominates.spend m bits counter (Command.charge A) A.rate
            (.oracle (r.calls.length + 4)) (rawRun.calls.length + 4) _ _ _
            (by simp only [Command.charge, hlength, resources.rate, le_refl])
          apply Causal.Dominates.ret m bits counter _ _
          refine ⟨hresult.value, hresult.memo, hresult.state, ?_, hresult.invariant⟩
          rw [hr.calls, hresult.calls, List.map_append]
      · simp only [liftEntry, hk, ↓reduceIte]
        exact Causal.Dominates.ret m bits counter _ _ _ _ _
          ⟨rfl, hmemo, hnext.2, rfl, hinv⟩

end SteinerUpperBound.Matching.Padded.Presentation
