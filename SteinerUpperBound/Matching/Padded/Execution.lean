module

public import SteinerUpperBound.Matching.Padded.CoreCorrect

@[expose] public section

/-!
The extra completion coordinate is an analysis-only coupling. It is not
sampled by the runtime. Costs below are the costs of the actual execution
leaf, not the cost of constructing this probability space.
-/

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical BigOperators

namespace Program

variable {C A R : Type*} [Fintype R]

noncomputable def completedLaw (p : Program C A) (posterior : A → Law R) : Law (p.Outcomes × R) :=
  p.law.bind fun leaf => (posterior (p.output leaf)).map fun ranks => (leaf, ranks)

theorem completedLaw_expect (p : Program C A) (posterior : A → Law R) (f : A → R → ℝ) :
    (completedLaw p posterior).expect (fun x => f (p.output x.1) x.2) =
      p.expect (fun a => (posterior a).expect (f a)) := by
  simp only [completedLaw, Law.expect_bind, Law.expect_map, expect]

theorem completedLaw_cost (p : Program C A) (posterior : A → Law R) (charge : C → ℝ) (rate : ℝ) :
    (completedLaw p posterior).expect (fun x => p.cost charge rate x.1) = p.expectedCost charge rate := by
  simp only [completedLaw, Law.expect_bind, Law.expect_map, Law.expect_const, expectedCost]

end Program

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E] (P : Parameters S)

theorem Cache.empty_completion (Q : ℕ) (hQ : 0 < Q) :
    Cache.completion S Q hQ (Cache.empty S Q) = UniformRanks.law Q hQ (E := E) := rfl

namespace Execution

abbrev Space (v : V) := (Oracle.vertex S P v).Outcomes × (E → Fin P.rankCard)

noncomputable def law (v : V) : Law (Space S P v) :=
  Program.completedLaw (Oracle.vertex S P v)
    (fun r => Cache.completion S P.rankCard P.rankCard_pos r.cache)

theorem expect_output (v : V) (f : LocalRun S P.rankCard (Option E) → (E → Fin P.rankCard) → ℝ) :
    (law S P v).expect (fun x => f ((Oracle.vertex S P v).output x.1) x.2) =
      (Oracle.vertex S P v).expect (fun r =>
        (Cache.completion S P.rankCard P.rankCard_pos r.cache).expect (f r)) := by
  exact Program.completedLaw_expect _ _ f

theorem expect_ideal (v : V) (f : LocalRun S P.rankCard (Option E) → (E → Fin P.rankCard) → ℝ) :
    (law S P v).expect (fun x => f ((Oracle.vertex S P v).output x.1) x.2) =
      (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).expect
        (fun ranks => f (Oracle.idealVertex S P v ranks) ranks) := by
  rw [expect_output]
  have h := Oracle.vertex_joint S P v f
  rw [Cache.empty_completion] at h
  exact h.symm

theorem ranks_marginal (v : V) :
    (law S P v).map Prod.snd = UniformRanks.law P.rankCard P.rankCard_pos (E := E) := by
  apply FiniteLaw.eq_of_expect
  intro f
  rw [Law.expect_map]
  exact expect_ideal S P v (fun _ ranks => f ranks)

theorem ties_probability (v : V) :
    (law S P v).prob {x | ¬ Function.Injective x.2} ≤
      (Fintype.card E : ℝ) ^ 2 / P.rankCard := by
  calc
    _ = ((law S P v).map Prod.snd).prob {ranks | ¬ Function.Injective ranks} :=
      (Law.prob_map (law S P v) Prod.snd _).symm
    _ ≤ _ := by
      rw [ranks_marginal]
      exact UniformRanks.collision_bound P.rankCard P.rankCard_pos

theorem good_statistic (v : V) (f : Graph.Run E (Option E) → ℝ) :
    (law S P v).expect (fun x =>
      if Function.Injective x.2 then f (((Oracle.vertex S P v).output x.1).forget) else 0) =
      (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).expect
        (fun ranks => if Function.Injective ranks then
          f (G.vertexOracle (UniformOrder.order ranks) v) else 0) := by
  rw [expect_ideal S P v (fun r ranks => if Function.Injective ranks then f r.forget else 0)]
  apply congrArg (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).expect
  funext ranks
  by_cases hn : Function.Injective ranks
  · simp only [hn, ↓reduceIte, Oracle.idealVertex_refines S P v ranks hn]
  · simp only [hn, ↓reduceIte]

theorem good_uniform_statistic (v : V) (f : Graph.Run E (Option E) → ℝ) :
    (law S P v).expect (fun x =>
      if Function.Injective x.2 then f (((Oracle.vertex S P v).output x.1).forget) else 0) =
      (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).prob {ranks | Function.Injective ranks} *
        (Rank.uniform (E := E)).expect (fun ρ => f (G.vertexOracle ρ v)) := by
  rw [good_statistic]
  exact UniformOrder.no_tie_expect (E := E) P.rankCard P.rankCard_pos
    (fun ρ => f (G.vertexOracle ρ v))

theorem expected_cost (v : V) (A : Account S) :
    (law S P v).expect
      (fun x => (Oracle.vertex S P v).cost (Command.charge A) A.rate x.1) =
        (Oracle.vertex S P v).expectedCost (Command.charge A) A.rate := by
  exact Program.completedLaw_cost _ _ _ _

theorem good_cost_le (v : V) (A : Account S) :
    (law S P v).expect (fun x => if Function.Injective x.2 then
      (Oracle.vertex S P v).cost (Command.charge A) A.rate x.1 else 0) ≤
        (Oracle.vertex S P v).expectedCost (Command.charge A) A.rate := by
  rw [← expected_cost S P v A]
  apply Law.expect_mono
  intro x
  split_ifs
  · exact le_refl _
  · exact Program.cost_nonneg _ _ _ (Command.charge_nonneg A) A.rate_nonneg _

theorem weighted_nonneg (cs : List (Invocation E)) (w : Directed E → ℝ) (hw : ∀ d, 0 ≤ w d) :
    0 ≤ Graph.weightedRequests cs w :=
  Finset.sum_nonneg fun d _ => mul_nonneg (hw d) (Nat.cast_nonneg _)

theorem expected_good_weighted_calls [Nonempty V] (w : Directed E → ℝ) (hw : ∀ d, 0 ≤ w d) :
    (Law.uniform V).expect (fun v => (law S P v).expect (fun x =>
      if Function.Injective x.2 then Graph.weightedRequests
        (((Oracle.vertex S P v).output x.1).calls) w else 0)) ≤
      (∑ d, w d) * G.callBudget / Fintype.card V := by
  have heq :
      (Law.uniform V).expect (fun v => (law S P v).expect (fun x =>
        if Function.Injective x.2 then Graph.weightedRequests
          (((Oracle.vertex S P v).output x.1).calls) w else 0)) =
      (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).prob {ranks | Function.Injective ranks} *
        G.randomRequest.expect (fun z => Graph.weightedRequests (G.vertexOracle z.1 z.2).calls w) := by
    have hv (v : V) := good_uniform_statistic S P v (fun r => Graph.weightedRequests r.calls w)
    simp only [LocalRun.forget_calls] at hv
    simp_rw [hv]
    rw [Law.expect_const_mul, G.expect_randomRequest]
    congr 1
    exact UniformOrder.expect_commute _ _ _
  rw [heq]
  have hn := G.randomRequest.expect_nonneg
    (fun z => weighted_nonneg (G.vertexOracle z.1 z.2).calls w hw)
  have hp := (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).prob_le_one
    {ranks | Function.Injective ranks}
  have hm : (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).prob
        {ranks | Function.Injective ranks} *
        G.randomRequest.expect (fun z => Graph.weightedRequests (G.vertexOracle z.1 z.2).calls w) ≤
      G.randomRequest.expect (fun z => Graph.weightedRequests (G.vertexOracle z.1 z.2).calls w) := by
    nlinarith
  exact hm.trans (G.expected_weighted_requests_le w hw)

end Execution

end SteinerUpperBound.Matching.Padded
