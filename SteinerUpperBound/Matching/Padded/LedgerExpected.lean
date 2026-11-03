module

public import SteinerUpperBound.Matching.Padded.Ledger

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Execution

open SteinerLowerBound
open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E] (P : Parameters S)

theorem good_requestValue (u : V → ℝ) (hu : ∀ v, 0 ≤ u v) (v : V) :
    (law S P v).expect (fun x => if Function.Injective x.2 then
      Cache.requestValue S P.rankCard u ((Oracle.vertex S P v).output x.1).cache else 0) ≤
      u v + (law S P v).expect (fun x => if Function.Injective x.2 then
        requestTrace (G := G) u ((Oracle.vertex S P v).output x.1).calls else 0) := by
  rw [expect_ideal S P v (fun r ranks => if Function.Injective ranks then
      Cache.requestValue S P.rankCard u r.cache else 0),
    expect_ideal S P v (fun r ranks => if Function.Injective ranks then
      requestTrace (G := G) u r.calls else 0),
    ← Law.expect_const (UniformRanks.law P.rankCard P.rankCard_pos (E := E)) (u v), ← Law.expect_add]
  apply Law.expect_mono
  intro ranks
  by_cases hn : Function.Injective ranks
  · simp only [hn, ↓reduceIte]
    exact Oracle.idealVertex_requestValue S P u hu v ranks
  · simpa only [hn, ↓reduceIte, add_zero] using hu v

theorem expected_good_requestValue [Nonempty V] (u : V → ℝ) (hu : ∀ v, 0 ≤ u v) :
    (Law.uniform V).expect (fun v => (law S P v).expect (fun x =>
      if Function.Injective x.2 then
        Cache.requestValue S P.rankCard u ((Oracle.vertex S P v).output x.1).cache else 0)) ≤
      (∑ v, u v) / Fintype.card V +
        (∑ d : Directed E, (u (G.head d) + u (G.tail d))) * G.callBudget / Fintype.card V := by
  have hh := (Law.uniform V).expect_mono (fun v => good_requestValue S P u hu v)
  rw [Law.expect_add, FiniteAveraging.uniform_expect_eq_sum_div u] at hh
  have hc := expected_good_weighted_calls S P
    (fun d => u (G.head d) + u (G.tail d))
    (fun d => add_nonneg (hu _) (hu _))
  exact hh.trans (add_le_add (le_refl _) hc)

theorem sum_tail_indicator (x : V) :
    (∑ d : Directed E, if G.tail d = x then (1 : ℝ) else 0) = G.degree x := by
  calc
    _ = ∑ d : Directed E, if G.head d = x then (1 : ℝ) else 0 := by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, Graph.head, Graph.tail]
      apply Finset.sum_congr rfl
      intro e _
      exact add_comm _ _
    _ = _ := G.sum_head_indicator x

theorem expected_good_vertexRequests [Nonempty V] (x : V) :
    (Law.uniform V).expect (fun v => (law S P v).expect (fun y =>
      if Function.Injective y.2 then
        (((Oracle.vertex S P v).output y.1).cache.requests x : ℝ) else 0)) ≤
      (1 + 2 * (G.degree x : ℝ) * G.callBudget) / Fintype.card V := by
  have hh := expected_good_requestValue S P (fun v => if v = x then 1 else 0)
    (fun _ => by split_ifs <;> norm_num)
  have hval (s : Cache S P.rankCard) :
      Cache.requestValue S P.rankCard (fun v => if v = x then 1 else 0) s = s.requests x := by
    simp [Cache.requestValue, ite_mul]
  simp_rw [hval] at hh
  have hs : (∑ d : Directed E,
      ((if G.head d = x then (1 : ℝ) else 0) + (if G.tail d = x then 1 else 0))) = 2 * G.degree x := by
    rw [Finset.sum_add_distrib, G.sum_head_indicator x, sum_tail_indicator (G := G) x]
    ring
  rw [hs] at hh
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, one_mul, ← add_div] using hh

end SteinerUpperBound.Matching.Padded.Execution
