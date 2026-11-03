module

public import SteinerUpperBound.Matching.Padded.Potential
public import SteinerUpperBound.Matching.Padded.Budget

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical BigOperators

namespace Program

variable {C A B : Type*}

theorem bind_resource (p : Program C A) (k : A → Program C B) (charge : C → ℝ) (rate : ℝ)
    (mid : A → ℝ) (post : B → ℝ) (budget : ℝ)
    (hp : p.expectedCost charge rate + p.expect mid ≤ budget)
    (hk : ∀ a, (k a).expectedCost charge rate + (k a).expect post ≤ mid a) :
    (p.bind k).expectedCost charge rate + (p.bind k).expect post ≤ budget := by
  have hh := p.expect_mono hk
  rw [expect_add] at hh
  rw [expectedCost_bind, expect_bind]
  linarith

end Program

namespace Cache

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ) [Fintype V]

theorem empty_reserve (A : Account S) (H height L : ℕ) :
    reserve S Q A H height L (empty S Q) = 0 := by
  simp [reserve, credit, sortingCredit, boundaryValue, levelValue, preparedValue, empty, boundary]

theorem reserve_requests (A : Account S) (H height L : ℕ) (s : Cache S Q) (requests : V → ℕ) :
    reserve S Q A H height L { s with requests := requests } = reserve S Q A H height L s := rfl

theorem preparedValue_mark (v : V) (s : Cache S Q) (hp : s.prepared v = false) :
    preparedValue S Q { s with prepared := Function.update s.prepared v true } =
      preparedValue S Q s + 1 := by
  classical
  have he (u : V) :
      (if Function.update s.prepared v true u then (1 : ℝ) else 0) =
        (if s.prepared u then 1 else 0) + if u = v then 1 else 0 := by
    by_cases hu : u = v
    · subst u; simp [hp]
    · simp [Function.update_of_ne hu, hu]
  simp only [preparedValue]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

theorem reserve_mark (A : Account S) (H height L : ℕ) (v : V) (s : Cache S Q)
    (hp : s.prepared v = false) :
    reserve S Q A H height L { s with prepared := Function.update s.prepared v true } =
      reserve S Q A H height L s - A.Cstar := by
  have hc : credit S Q A H height { s with prepared := Function.update s.prepared v true } =
      credit S Q A H height s := rfl
  have hb : boundaryValue S Q A { s with prepared := Function.update s.prepared v true } =
      boundaryValue S Q A s := rfl
  have hl : levelValue S Q { s with prepared := Function.update s.prepared v true } =
      levelValue S Q s := rfl
  simp only [reserve, hc, hb, hl, preparedValue_mark S Q v s hp]
  ring

theorem nextLoop_bucket (hQ : 0 < Q) (A : Account S) (H height L : ℕ) (v : V)
    (cursor fuel : ℕ) (s : Cache S Q)
    (hL : extensionCoefficient H height (S.length v) ≤ L) :
    (nextLoop S Q hQ height v cursor fuel s).expectedCost (Command.bucketCharge A) A.rate +
      (nextLoop S Q hQ height v cursor fuel s).expect (fun answer =>
        reserve S Q A H height L answer.2) ≤ reserve S Q A H height L s := by
  induction fuel generalizing s with
  | zero => simp only [nextLoop, Program.expectedCost_ret, Program.expect_ret, zero_add, le_refl]
  | succ fuel ih =>
    rw [nextLoop, Program.expectedCost_tick, Program.expect_tick]
    simp only [Command.bucketCharge, zero_add]
    cases ha : available S Q v cursor s with
    | some x => simp only [Program.expectedCost_ret, Program.expect_ret, zero_add, le_refl]
    | none =>
      split_ifs
      · exact Program.bind_resource (extend S Q hQ height v s)
          (fun t => nextLoop S Q hQ height v cursor fuel t) _ _ (reserve S Q A H height L) _ _
          (extend_reserve S Q hQ A H height L v s hL) ih
      · simp only [Program.expectedCost_ret, Program.expect_ret, zero_add, le_refl]

theorem next_bucket (hQ : 0 < Q) (A : Account S) (H height L maxLevel : ℕ)
    (v : V) (cursor : ℕ) (s : Cache S Q)
    (hL : extensionCoefficient H height (S.length v) ≤ L) :
    (next S Q hQ height maxLevel v cursor s).expectedCost (Command.bucketCharge A) A.rate +
      (next S Q hQ height maxLevel v cursor s).expect (fun answer =>
        reserve S Q A H height L answer.2) ≤ reserve S Q A H height L s := by
  classical
  unfold next
  cases hp : s.prepared v with
  | true =>
    simp only [↓reduceIte]
    have hh := nextLoop_bucket S Q hQ A H height L v cursor (maxLevel + 1)
      { s with requests := Function.update s.requests v (s.requests v + 1) } hL
    simpa only [reserve_requests] using hh
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Program.expectedCost_tick, Program.expect_tick,
      Command.bucketCharge, Command.charge]
    have hh := nextLoop_bucket S Q hQ A H height L v cursor (maxLevel + 1)
      { s with requests := Function.update s.requests v (s.requests v + 1),
               prepared := Function.update s.prepared v true } hL
    have he :
        reserve S Q A H height L
          { s with requests := Function.update s.requests v (s.requests v + 1),
                   prepared := Function.update s.prepared v true } =
          reserve S Q A H height L s - A.Cstar := by
      rw [← reserve_mark S Q A H height L v s hp]
      exact reserve_requests S Q A H height L
        { s with prepared := Function.update s.prepared v true }
        (Function.update s.requests v (s.requests v + 1))
    rw [he] at hh
    linarith [A.preparation_le v]

end Cache

namespace Oracle

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] (P : Parameters S)
    (A : Account S) (H L : ℕ)

theorem scan_bucket
    (call : Entry S P.rankCard → Cache S P.rankCard → Memo E →
      Program (Command S) (LocalRun S P.rankCard Bool))
    (hcall : ∀ x t μ, (call x t μ).expectedCost (Command.bucketCharge A) A.rate +
      (call x t μ).expect (fun r => Cache.reserve S P.rankCard A H P.sortHeight L r.cache) ≤
        Cache.reserve S P.rankCard A H P.sortHeight L t)
    (hL : ∀ v, Cache.extensionCoefficient H P.sortHeight (S.length v) ≤ L)
    (v : V) (cutoff cursor fuel : ℕ) (s : Cache S P.rankCard) (μ : Memo E) :
    (scan S P call v cutoff cursor fuel s μ).expectedCost (Command.bucketCharge A) A.rate +
      (scan S P call v cutoff cursor fuel s μ).expect
        (fun r => Cache.reserve S P.rankCard A H P.sortHeight L r.cache) ≤
      Cache.reserve S P.rankCard A H P.sortHeight L s := by
  induction fuel generalizing cursor s μ with
  | zero => simp only [scan, Program.expectedCost_ret, Program.expect_ret, zero_add, le_refl]
  | succ fuel ih =>
    rw [scan]
    apply Program.bind_resource (B := LocalRun S P.rankCard (Option (Entry S P.rankCard)))
      (Cache.next S P.rankCard P.rankCard_pos P.sortHeight (P.rankExponent + 1) v cursor s)
      _ _ _ (fun (answer : Option (Entry S P.rankCard) × Cache S P.rankCard) =>
        Cache.reserve S P.rankCard A H P.sortHeight L answer.2)
      _ _ (Cache.next_bucket S P.rankCard P.rankCard_pos A H P.sortHeight L (P.rankExponent + 1)
        v cursor s (hL v))
    intro answer
    cases ha : answer.1 with
    | none => simp only [Program.expectedCost_ret, Program.expect_ret, zero_add, le_refl]
    | some x =>
      dsimp only
      by_cases hk : x.rank.val < cutoff
      · simp only [hk, ↓reduceIte]
        apply Program.bind_resource (B := LocalRun S P.rankCard (Option (Entry S P.rankCard)))
          (call x answer.2 μ) _ _ _ (fun (r : LocalRun S P.rankCard Bool) =>
            Cache.reserve S P.rankCard A H P.sortHeight L r.cache)
          _ _ (hcall x answer.2 μ)
        intro r
        cases hb : r.value with
        | true => simp only [↓reduceIte, Program.expectedCost_ret, Program.expect_ret, zero_add, le_refl]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          apply Program.bind_resource (B := LocalRun S P.rankCard (Option (Entry S P.rankCard)))
            (scan S P call v cutoff (cursor + 1) fuel r.cache r.memo) _ _ _
            (fun (t : LocalRun S P.rankCard (Option (Entry S P.rankCard))) =>
              Cache.reserve S P.rankCard A H P.sortHeight L t.cache)
            _ _ (ih (cursor + 1) r.cache r.memo)
          intro t
          simp only [Program.expectedCost_tick, Program.expect_tick, Program.expectedCost_ret,
            Program.expect_ret, Command.bucketCharge, zero_add, le_refl]
      · simp only [hk, ↓reduceIte, Program.expectedCost_ret, Program.expect_ret, zero_add, le_refl]

theorem edge_bucket
    (hL : ∀ v, Cache.extensionCoefficient H P.sortHeight (S.length v) ≤ L)
    (d : Directed E) (rank : Fin P.rankCard) (ancestors : List (Directed E))
    (s : Cache S P.rankCard) (μ : Memo E) :
    (edge S P d rank ancestors s μ).expectedCost (Command.bucketCharge A) A.rate +
      (edge S P d rank ancestors s μ).expect
        (fun r => Cache.reserve S P.rankCard A H P.sortHeight L r.cache) ≤
      Cache.reserve S P.rankCard A H P.sortHeight L s := by
  rw [edge, Program.expectedCost_tick, Program.expect_tick]
  simp only [Command.bucketCharge, zero_add]
  cases hm : μ d with
  | some b => simp only [Program.expectedCost_ret, Program.expect_ret, zero_add, le_refl]
  | none =>
    let call := fun (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E) =>
      if _h : x.rank.val < rank.val then
        edge S P (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν
      else .ret ⟨false, ν, t, []⟩
    have hcall (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E) :
        (call x t ν).expectedCost (Command.bucketCharge A) A.rate +
          (call x t ν).expect (fun r => Cache.reserve S P.rankCard A H P.sortHeight L r.cache) ≤
        Cache.reserve S P.rankCard A H P.sortHeight L t := by
      dsimp only [call]
      split_ifs with hk
      · exact edge_bucket hL (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν
      · simp only [Program.expectedCost_ret, Program.expect_ret, zero_add, le_refl]
    apply Program.bind_resource (B := LocalRun S P.rankCard Bool)
      (scan S P call (G.head d) rank.val 0 (P.Nstar + 1) s μ) _ _ _
      (fun (r : LocalRun S P.rankCard (Option (Entry S P.rankCard))) =>
        Cache.reserve S P.rankCard A H P.sortHeight L r.cache)
      _ _ (scan_bucket S P A H L call hcall hL (G.head d) rank.val 0 (P.Nstar + 1) s μ)
    intro r
    simp only [Program.expectedCost_tick, Program.expect_tick, Program.expectedCost_ret,
      Program.expect_ret, Command.bucketCharge, zero_add, le_refl]
termination_by rank.val
decreasing_by exact hk

theorem vertex_bucket
    (hL : ∀ v, Cache.extensionCoefficient H P.sortHeight (S.length v) ≤ L) (v : V) :
    (vertex S P v).expectedCost (Command.bucketCharge A) A.rate +
      (vertex S P v).expect (fun r => Cache.reserve S P.rankCard A H P.sortHeight L r.cache) ≤ 0 := by
  rw [vertex, Program.expectedCost_tick, Program.expect_tick]
  simp only [Command.bucketCharge, zero_add]
  have hs := scan_bucket S P A H L (rootCall S P v)
    (fun x s μ => edge_bucket S P A H L hL (G.away v x.edge) x.rank [] s μ) hL
    v P.rankCard 0 (P.Nstar + 1) (Cache.empty S P.rankCard) (fun _ => none)
  have hz := Cache.empty_reserve S P.rankCard A H P.sortHeight L
  apply Program.bind_resource (B := LocalRun S P.rankCard (Option E))
    (scan S P (rootCall S P v) v P.rankCard 0 (P.Nstar + 1) (Cache.empty S P.rankCard) (fun _ => none))
    _ _ _ (fun (r : LocalRun S P.rankCard (Option (Entry S P.rankCard))) =>
      Cache.reserve S P.rankCard A H P.sortHeight L r.cache)
    _ _ (by simpa only [hz] using hs)
  intro r
  simp only [Program.expectedCost_ret, Program.expect_ret, zero_add, le_refl]

end Oracle

end SteinerUpperBound.Matching.Padded
