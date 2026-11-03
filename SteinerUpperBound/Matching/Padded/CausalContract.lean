module

public import SteinerUpperBound.Matching.Padded.RawCausal

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Causal

open SteinerLowerBound
open scoped Classical

variable {M T A : Type*}

def Ensures (m : M → ℝ) (b : T → Bool) (p : Code M T A) (P : A → Prop) : Prop :=
  ∀ f : A → ℝ, (∀ a, P a → f a = 0) → expect m b p f = 0

theorem ensures_of_evaluates (m : M → ℝ) (b : T → Bool) (p : Code M T A)
    (o : Outcome A) (h : p.Evaluates m b o) (P : A → Prop) (ho : P o.value) :
    Ensures m b p P := by
  intro f hf
  unfold expect
  rw [h]
  exact hf o.value ho

structure Counter where
  work : ℝ
  metric : ℝ
  retained : ℝ
  positive : ℝ
  work_nonneg : 0 ≤ work
  metric_nonneg : 0 ≤ metric
  retained_nonneg : 0 ≤ retained
  positive_nonneg : 0 ≤ positive

def Counter.value (c : Counter) (o : Outcome A) : ℝ :=
  c.work * o.work + c.metric * o.metricQueries +
    c.retained * o.retentionQueries + c.positive * o.positiveReplies

theorem Counter.value_nonneg (c : Counter) (o : Outcome A) : 0 ≤ c.value o := by
  exact add_nonneg
    (add_nonneg
      (add_nonneg (mul_nonneg c.work_nonneg (Nat.cast_nonneg _))
        (mul_nonneg c.metric_nonneg (Nat.cast_nonneg _)))
      (mul_nonneg c.retained_nonneg (Nat.cast_nonneg _)))
    (mul_nonneg c.positive_nonneg (Nat.cast_nonneg _))

end SteinerUpperBound.Matching.Padded.Causal

namespace SteinerUpperBound.Matching.Padded.RawCausal.Primitives

open SteinerLowerBound
open scoped Classical

variable {V E Label M T : Type*} {G : Graph V E} (S : Slots G) (encode : E ↪ Label)
    (I : Primitives S.length Label M T) (m : M → ℝ) (b : T → Bool)

/-- Only primitive correctness and persistence are supplied by a slot frontend. -/
structure Contract where
  Inv : I.Memory → Prop
  Ready : I.Memory → V → Prop
  initial : Inv I.initial
  prepare : ∀ v memory, Inv memory →
    Causal.Ensures m b (I.prepare v memory) (fun memory' =>
      Inv memory' ∧ Ready memory' v ∧ ∀ u, Ready memory u → Ready memory' u)
  slot : ∀ s memory, Inv memory → Ready memory s.1 →
    Causal.Ensures m b (I.slot s memory) (fun answer =>
      answer.1 = (S.test s).map (fun hit => (encode hit.1, hit.2)) ∧
        Inv answer.2 ∧ ∀ u, Ready memory u → Ready answer.2 u)

/-- Per-test and preparation bounds are fixed before rank randomness. -/
structure Resources (K : Contract S encode I m b) (A : Account S) (c : Causal.Counter) : Prop where
  rate : A.rate = c.work
  prepare : ∀ v memory, K.Inv memory →
    (I.prepare v memory).evaluate m b c.value ≤ A.preparation v
  slot : ∀ s memory, K.Inv memory → K.Ready memory s.1 →
    (I.slot s memory).evaluate m b c.value ≤ A.slot s

end SteinerUpperBound.Matching.Padded.RawCausal.Primitives
