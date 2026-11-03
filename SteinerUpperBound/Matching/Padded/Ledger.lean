module

public import SteinerUpperBound.Matching.Padded.Execution

@[expose] public section

/-!
Outgoing sorted-list requests, including exhaustion and cutoff requests, are
charged to both endpoint orientations of the actual invocation trace.
-/

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V]

namespace Cache

def requestValue (Q : ℕ) (u : V → ℝ) (s : Cache S Q) : ℝ :=
  ∑ v, u v * (s.requests v : ℝ)

theorem empty_requestValue (Q : ℕ) (u : V → ℝ) :
    requestValue S Q u (empty S Q) = 0 := by simp [requestValue, empty]

theorem idealNext_requestValue (Q height maxLevel : ℕ) (u : V → ℝ) (v : V) (cursor : ℕ)
    (s : Cache S Q) (ranks : E → Fin Q) :
    requestValue S Q u (idealNext S Q height maxLevel v cursor s ranks).2 =
      requestValue S Q u s + u v := by
  classical
  unfold requestValue
  rw [idealNext_requests]
  calc
    _ = ∑ x, (u x * (s.requests x : ℝ) + if x = v then u v else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = v
      · subst x
        simp only [Function.update_self, Nat.cast_add, Nat.cast_one, ↓reduceIte]
        ring
      · simp only [Function.update_of_ne hx, hx, ↓reduceIte, add_zero]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

end Cache

variable [Fintype E]

theorem LocalRun.mapValue_calls {Q : ℕ} {A B : Type*} (f : A → B) (r : LocalRun S Q A) :
    (r.mapValue f).calls = r.calls := rfl

noncomputable def requestTrace (u : V → ℝ) (cs : List (Invocation E)) : ℝ :=
  Graph.weightedRequests cs (fun d => u (G.head d) + u (G.tail d))

theorem requestTrace_nil (u : V → ℝ) : requestTrace (G := G) u [] = 0 := by
  simp only [requestTrace, Graph.weightedRequests_eq_sum_log, List.map_nil, List.sum_nil]

theorem requestTrace_append (u : V → ℝ) (xs ys : List (Invocation E)) :
    requestTrace (G := G) u (xs ++ ys) =
      requestTrace (G := G) u xs + requestTrace (G := G) u ys := by
  simp only [requestTrace, Graph.weightedRequests_eq_sum_log, List.map_append, List.sum_append]

theorem requestTrace_cons (u : V → ℝ) (c : Invocation E) (cs : List (Invocation E)) :
    requestTrace (G := G) u (c :: cs) =
      u (G.head c.state) + u (G.tail c.state) + requestTrace (G := G) u cs := by
  simp only [requestTrace, Graph.weightedRequests_eq_sum_log, List.map_cons, List.sum_cons]

namespace Oracle

variable (P : Parameters S) (u : V → ℝ) (hu : ∀ v, 0 ≤ u v)

include hu

theorem idealScan_requestValue
    (call : Entry S P.rankCard → Cache S P.rankCard → Memo E →
      (E → Fin P.rankCard) → LocalRun S P.rankCard Bool)
    (ranks : E → Fin P.rankCard) (v : V) (cutoff : ℕ)
    (hcall : ∀ x t ν, Cache.Invariant S P.rankCard t → Cache.Consistent S P.rankCard t ranks →
      G.Incident x.edge v → x.rank.val < cutoff →
        RunSafe S P.rankCard ranks (call x t ν ranks) ∧
          Cache.requestValue S P.rankCard u (call x t ν ranks).cache + u v ≤
            Cache.requestValue S P.rankCard u t + requestTrace (G := G) u (call x t ν ranks).calls)
    (cursor fuel : ℕ) (s : Cache S P.rankCard) (μ : Memo E)
    (hs : Cache.Invariant S P.rankCard s) (hc : Cache.Consistent S P.rankCard s ranks) :
    Cache.requestValue S P.rankCard u (idealScan S P call v cutoff cursor fuel s μ ranks).cache ≤
      Cache.requestValue S P.rankCard u s + u v +
        requestTrace (G := G) u (idealScan S P call v cutoff cursor fuel s μ ranks).calls := by
  induction fuel generalizing cursor s μ with
  | zero =>
    simpa only [idealScan, requestTrace_nil, add_zero] using
      le_add_of_nonneg_right (hu v) (a := Cache.requestValue S P.rankCard u s)
  | succ fuel ih =>
    rw [idealScan]
    have hn := Cache.idealNext_safe S P v cursor s ranks hs hc
    have hreq := Cache.idealNext_requestValue S P.rankCard P.sortHeight (P.rankExponent + 1)
      u v cursor s ranks
    cases ha : (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks).1 with
    | none => simpa only [requestTrace_nil, add_zero] using le_of_eq hreq
    | some x =>
      dsimp only
      by_cases hk : x.rank.val < cutoff
      · simp only [hk, ↓reduceIte]
        have hvalid := hn.valid x ha
        have hi : G.Incident x.edge v := by
          have hh := (S.test_incident hvalid.2.1).1
          simpa only [hvalid.1] using hh
        have hr := hcall x _ μ hn.invariant hn.consistent hi hk
        have hcredit :
            Cache.requestValue S P.rankCard u
              (call x (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1)
                v cursor s ranks).2 μ ranks).cache ≤
              Cache.requestValue S P.rankCard u s +
                requestTrace (G := G) u
                  (call x (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1)
                    v cursor s ranks).2 μ ranks).calls := by
          rw [hreq] at hr
          linarith [hr.2]
        cases hb : (call x
            (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks).2 μ ranks).value with
        | true =>
          simp only [↓reduceIte]
          linarith [hu v]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have ht := ih (cursor + 1)
            (call x (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1)
              v cursor s ranks).2 μ ranks).cache
            (call x (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1)
              v cursor s ranks).2 μ ranks).memo hr.1.invariant hr.1.consistent
          rw [requestTrace_append]
          linarith
      · simpa only [hk, ↓reduceIte, requestTrace_nil, add_zero] using le_of_eq hreq

theorem idealEdge_requestValue (d : Directed E) (rank : Fin P.rankCard)
    (ancestors : List (Directed E)) (s : Cache S P.rankCard) (μ : Memo E)
    (ranks : E → Fin P.rankCard) (hs : Cache.Invariant S P.rankCard s)
    (hc : Cache.Consistent S P.rankCard s ranks) :
    Cache.requestValue S P.rankCard u (idealEdge S P d rank ancestors s μ ranks).cache +
        u (G.tail d) ≤
      Cache.requestValue S P.rankCard u s +
        requestTrace (G := G) u (idealEdge S P d rank ancestors s μ ranks).calls := by
  rw [idealEdge]
  cases hm : μ d with
  | some b =>
    simp only [requestTrace_cons, requestTrace_nil, add_zero]
    linarith [hu (G.head d)]
  | none =>
    let call := fun (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E)
        (world : E → Fin P.rankCard) =>
      if _h : x.rank.val < rank.val then
        idealEdge S P (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν world
      else ⟨false, ν, t, []⟩
    have hcall (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E)
        (ht : Cache.Invariant S P.rankCard t) (hct : Cache.Consistent S P.rankCard t ranks)
        (hi : G.Incident x.edge (G.head d)) (hk : x.rank.val < rank.val) :
        RunSafe S P.rankCard ranks (call x t ν ranks) ∧
          Cache.requestValue S P.rankCard u (call x t ν ranks).cache + u (G.head d) ≤
            Cache.requestValue S P.rankCard u t + requestTrace (G := G) u (call x t ν ranks).calls := by
      dsimp only [call]
      simp only [hk, ↓reduceDIte]
      have hh := idealEdge_requestValue (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν ranks ht hct
      rw [G.tail_away hi] at hh
      exact ⟨idealEdge_safe S P _ _ _ _ _ _ ht hct, hh⟩
    have hr := idealScan_requestValue S P u hu call ranks (G.head d) rank.val hcall
      0 (P.Nstar + 1) s μ hs hc
    simp only [requestTrace_cons]
    linarith
termination_by rank.val
decreasing_by exact hk

theorem idealVertex_requestValue (v : V) (ranks : E → Fin P.rankCard) :
    Cache.requestValue S P.rankCard u (idealVertex S P v ranks).cache ≤
      u v + requestTrace (G := G) u (idealVertex S P v ranks).calls := by
  have hcall (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E)
      (ht : Cache.Invariant S P.rankCard t) (hc : Cache.Consistent S P.rankCard t ranks)
      (hi : G.Incident x.edge v) (_hk : x.rank.val < P.rankCard) :
      RunSafe S P.rankCard ranks (idealRootCall S P v x t ν ranks) ∧
        Cache.requestValue S P.rankCard u (idealRootCall S P v x t ν ranks).cache + u v ≤
          Cache.requestValue S P.rankCard u t +
            requestTrace (G := G) u (idealRootCall S P v x t ν ranks).calls := by
    have hh := idealEdge_requestValue S P u hu (G.away v x.edge) x.rank [] t ν ranks ht hc
    rw [G.tail_away hi] at hh
    exact ⟨idealEdge_safe S P _ _ _ _ _ _ ht hc, hh⟩
  have hh := idealScan_requestValue S P u hu (idealRootCall S P v) ranks v P.rankCard hcall
    0 (P.Nstar + 1) (Cache.empty S P.rankCard) (fun _ => none)
    (Cache.empty_invariant S P.rankCard P.rankCard_pos) (Cache.empty_consistent S P.rankCard ranks)
  rw [Cache.empty_requestValue, zero_add] at hh
  have hcalls : (idealVertex S P v ranks).calls =
      (idealScan S P (idealRootCall S P v) v P.rankCard 0 (P.Nstar + 1)
        (Cache.empty S P.rankCard) (fun _ => none) ranks).calls :=
    LocalRun.mapValue_calls S _ _
  rw [idealVertex_cache, hcalls]
  exact hh

end Oracle

end SteinerUpperBound.Matching.Padded
