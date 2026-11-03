module

public import SteinerUpperBound.Matching.Padded.ValueKernel
public import SteinerUpperBound.Matching.Padded.DominationTools

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical

theorem probability_cost_le {Ω : Type*} [Fintype Ω] (μ : Law Ω) (cost : Ω → ℝ)
    (Good : Ω → Prop) (hcost : ∀ ω, 0 ≤ cost ω) (threshold : ℝ) (ht : 0 < threshold) :
    μ.prob {ω | threshold ≤ cost ω} ≤
      μ.prob {ω | ¬ Good ω} +
        μ.expect (fun ω => if Good ω then cost ω else 0) / threshold := by
  classical
  have hs : {ω | threshold ≤ cost ω} ⊆ {ω | ¬ Good ω} ∪
      {ω | threshold ≤ if Good ω then cost ω else 0} := by
    intro ω hw
    change threshold ≤ cost ω at hw
    by_cases hg : Good ω
    · apply Or.inr
      change threshold ≤ if Good ω then cost ω else 0
      simpa only [hg, ↓reduceIte] using hw
    · exact Or.inl hg
  have hn (ω : Ω) : 0 ≤ if Good ω then cost ω else 0 := by split_ifs; exact hcost ω; exact le_refl _
  exact (μ.prob_mono hs).trans ((μ.prob_union_le _ _).trans
    (add_le_add (le_refl _) (μ.markov hn ht)))

namespace Execution

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E] (P : Parameters S)

theorem model_cost_tail (A : Account S) (v : V) (threshold : ℝ) (ht : 0 < threshold) :
    (Oracle.vertex S P v).measured (Command.charge A) A.rate
        (fun _ cost => if threshold ≤ cost then 1 else 0) ≤
      1 / (P.Nstar : ℝ) ^ 30 +
        (Execution.law S P v).expect (fun x => if Function.Injective x.2 then
          (Oracle.vertex S P v).cost (Command.charge A) A.rate x.1 else 0) / threshold := by
  classical
  have hm := probability_cost_le (Execution.law S P v)
    (fun x => (Oracle.vertex S P v).cost (Command.charge A) A.rate x.1)
    (fun x => Function.Injective x.2)
    (fun x => Program.cost_nonneg _ _ _ (Command.charge_nonneg A) A.rate_nonneg x.1)
    threshold ht
  have hs := hm.trans (add_le_add (Parameters.tie_budget S P v) (le_refl _))
  rw [Law.prob_eq_expect] at hs
  have he :
      (Execution.law S P v).expect (fun x =>
        if threshold ≤ (Oracle.vertex S P v).cost (Command.charge A) A.rate x.1 then (1 : ℝ) else 0) =
      (Oracle.vertex S P v).measured (Command.charge A) A.rate
        (fun _ cost => if threshold ≤ cost then 1 else 0) := by
    simp only [Execution.law, Program.completedLaw, Law.expect_bind, Law.expect_map,
      Law.expect_const, Program.measured]
    apply congrArg (Oracle.vertex S P v).law.expect
    funext leaf
    exact Law.expect_const
      (Cache.completion S P.rankCard P.rankCard_pos ((Oracle.vertex S P v).output leaf).cache)
      (if threshold ≤ (Oracle.vertex S P v).cost (Command.charge A) A.rate leaf then 1 else 0)
  rw [← he]
  convert hs using 1
  · apply congrArg (Execution.law S P v).expect
    funext x
    by_cases h : threshold ≤ (Oracle.vertex S P v).cost (Command.charge A) A.rate x.1 <;> simp [h]
  · congr 2
    apply congrArg (Execution.law S P v).expect
    funext x
    by_cases h : Function.Injective x.2 <;> simp [h]

end Execution

namespace Presentation

variable {V E Vertex Label M T : Type*} {G : Graph V E} {S : Slots G} [Fintype V] [Fintype E]
    {P : Parameters S} {C : Runtime.Config Vertex} (J : Presentation (Label := Label) S P C)
    (I : Runtime.Primitives C.length Label M T) (m : M → ℝ) (bits : T → Bool)
    (K : J.Contract I m bits) (D : J.Deterministic I m bits K)
    (A : Account S) (counter : Causal.Counter) (resources : J.Resources I m bits K A counter)

include D resources

theorem vertex_counter_tail (v : V) (threshold : ℝ) (ht : 0 < threshold) :
    (Runtime.vertex C I (J.vertex v)).evaluate m bits
        (fun o => if threshold ≤ counter.value o then 1 else 0) ≤
      1 / (C.Nstar : ℝ) ^ 30 +
        (Execution.law S J.parameters v).expect (fun x => if Function.Injective x.2 then
          (Oracle.vertex S J.parameters v).cost (Command.charge A) A.rate x.1 else 0) / threshold :=
  (Causal.Dominates.counter_tail m bits counter (Command.charge A) A.rate _ _ _
    (vertex_dominates J I m bits K D A counter resources v) threshold).trans
      (Execution.model_cost_tail S J.parameters A v threshold ht)

end Presentation

end SteinerUpperBound.Matching.Padded
