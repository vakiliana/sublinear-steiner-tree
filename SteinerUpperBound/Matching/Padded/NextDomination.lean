module

public import SteinerUpperBound.Matching.Padded.CollectionDomination
public import SteinerUpperBound.Matching.Padded.KernelSupport

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Presentation

open scoped Classical

variable {V E Vertex Label M T : Type*} {G : Graph V E} {S : Slots G} [Fintype V]
    {P : Parameters S} {C : Runtime.Config Vertex} (J : Presentation (Label := Label) S P C)
    (I : Runtime.Primitives C.length Label M T) (m : M → ℝ) (bits : T → Bool)
    (K : J.Contract I m bits) (D : J.Deterministic I m bits K)
    (A : Account S) (counter : Causal.Counter) (resources : J.Resources I m bits K A counter)

def AnswerMatch (answer : Option (Entry S C.rankCard) × Cache S C.rankCard)
    (raw : Option (Runtime.Copy C (Label := Label)) × Runtime.State C I) : Prop :=
  raw.1 = answer.1.map J.liftEntry ∧ J.StateMatch I m bits K answer.2 raw.2

include D resources

theorem nextLoop_dominates (v : V) (cursor fuel : ℕ) (s : Cache S C.rankCard) (t : Runtime.State C I)
    (hmatch : J.StateMatch I m bits K s t) (hprepared : s.prepared v = true) :
    Causal.Dominates m bits counter (Command.charge A) A.rate
      (Cache.nextLoop S C.rankCard C.rankCard_pos C.sortHeight v cursor fuel s)
      (Runtime.nextLoop C I (J.vertex v) cursor fuel t)
      (J.AnswerMatch I m bits K) := by
  induction fuel generalizing s t with
  | zero =>
    exact Causal.Dominates.ret m bits counter _ _ (none, s) (none, t) _ ⟨rfl, hmatch⟩
  | succ fuel ih =>
    rw [Cache.nextLoop, Runtime.nextLoop]
    apply Causal.Dominates.spend m bits counter (Command.charge A) A.rate (.oracle 6) 6 _ _ _
      (by simp only [Command.charge, resources.rate, le_refl])
    rw [hmatch.cache.available J I v cursor]
    cases ha : Cache.available S C.rankCard v cursor s with
    | some x =>
      simp only [Option.map_some]
      exact Causal.Dominates.ret m bits counter _ _ (some x, s) (some (J.liftEntry x), t) _
        ⟨rfl, hmatch⟩
    | none =>
      simp only [Option.map_none, hmatch.cache.boundary J I v]
      by_cases hb : Cache.boundary S C.rankCard s v < C.rankCard
      · simp only [hb, ↓reduceIte]
        have hext := extend_dominates J I m bits K D A counter resources v s t hmatch hprepared
        have hstrong := Causal.Dominates.strengthen_model m bits counter (Command.charge A) A.rate
          _ _ (J.StateMatch I m bits K) (fun u => u.prepared = s.prepared) hext
          (Cache.extend_prepared S C.rankCard C.rankCard_pos C.sortHeight v s)
        apply Causal.Dominates.bind m bits counter (Command.charge A) A.rate _ _ _ _ _ _ hstrong
        intro u raw h
        exact ih u raw h.1 (by simpa only [h.2] using hprepared)
      · simp only [hb, ↓reduceIte]
        exact Causal.Dominates.ret m bits counter _ _ (none, s) (none, t) _ ⟨rfl, hmatch⟩

theorem next_dominates (v : V) (cursor : ℕ) (s : Cache S C.rankCard) (t : Runtime.State C I)
    (hmatch : J.StateMatch I m bits K s t) :
    Causal.Dominates m bits counter (Command.charge A) A.rate
      (Cache.next S C.rankCard C.rankCard_pos C.sortHeight (C.rankExponent + 1) v cursor s)
      (Runtime.next C I (J.vertex v) cursor t)
      (J.AnswerMatch I m bits K) := by
  classical
  let s' := { s with requests := Function.update s.requests v (s.requests v + 1) }
  let t' := { t with requests := Function.update t.requests (J.vertex v) (t.requests (J.vertex v) + 1) }
  have hr : J.StateMatch I m bits K s' t' := hmatch.requests_update J I m bits K v
  rw [Cache.next, Runtime.next]
  rw [hmatch.cache.prepared v]
  cases hp : s.prepared v with
  | true =>
    simp only [↓reduceIte]
    exact nextLoop_dominates J I m bits K D A counter resources v cursor (C.rankExponent + 2)
      s' t' hr hp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply Causal.Dominates.bind m bits counter (Command.charge A) A.rate
      (.tick (.prepare v) (.ret ())) (I.prepare (J.vertex v) t.memory)
      (fun (_ : Unit) => Cache.nextLoop S C.rankCard C.rankCard_pos C.sortHeight v cursor
        (C.rankExponent + 2) { s' with prepared := Function.update s'.prepared v true })
      (fun memory => Runtime.nextLoop C I (J.vertex v) cursor (C.rankExponent + 2)
        { t' with prepared := Function.update t'.prepared (J.vertex v) true, memory := memory })
      _ (J.AnswerMatch I m bits K)
      (prepare_dominates J I m bits K D A counter resources v t.memory hmatch.memory.1)
    intro modelUnit memory hm
    have hs : J.StateMatch I m bits K { s' with prepared := Function.update s'.prepared v true }
        { t' with prepared := Function.update t'.prepared (J.vertex v) true, memory := memory } :=
      hr.prepared_update J I m bits K v memory hm
    exact nextLoop_dominates J I m bits K D A counter resources v cursor (C.rankExponent + 2)
      _ _ hs (by simp)

theorem next_dominates_supported [Fintype E] (v : V) (cursor : ℕ)
    (s : Cache S C.rankCard) (t : Runtime.State C I)
    (hmatch : J.StateMatch I m bits K s t) (hs : Cache.Invariant S C.rankCard s) :
    Causal.Dominates m bits counter (Command.charge A) A.rate
      (Cache.next S C.rankCard C.rankCard_pos C.sortHeight (C.rankExponent + 1) v cursor s)
      (Runtime.next C I (J.vertex v) cursor t)
      (fun answer raw => J.AnswerMatch I m bits K answer raw ∧
        Cache.Invariant S C.rankCard answer.2 ∧
          ∀ x, answer.1 = some x → x.source.1 = v ∧ Cache.EntryValid S C.rankCard x) := by
  exact Causal.Dominates.strengthen_model m bits counter (Command.charge A) A.rate _ _ _ _
    (next_dominates J I m bits K D A counter resources v cursor s t hmatch)
    (Cache.next_supported S J.parameters v cursor s hs)

end SteinerUpperBound.Matching.Padded.Presentation
