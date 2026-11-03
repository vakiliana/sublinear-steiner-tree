module

public import SteinerUpperBound.Matching.ExpectedCalls

@[expose] public section

/-!
# Uniform-root and vertexwise request bounds

`randomRequest` draws the copy order and the root independently. A vertex
request account charges the outer root once and each directed invocation at its
head. The weighted theorem also supports arbitrary nonnegative fixed accounts.
-/

namespace SteinerUpperBound.Matching

open SteinerLowerBound FiniteAveraging
open scoped Classical BigOperators

namespace FiniteAveraging

theorem uniform_expect_eq_sum_div {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    (Law.uniform A).expect f = (∑ a, f a) / Fintype.card A := by
  simp only [Law.expect, Law.uniform]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

end FiniteAveraging

namespace Graph

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : Graph V E)

noncomputable def weightedRequests (cs : List (Invocation E)) (w : Directed E → ℝ) : ℝ :=
  ∑ d, w d * (requests cs d : ℝ)

theorem weightedRequests_eq_sum_log (cs : List (Invocation E)) (w : Directed E → ℝ) :
    weightedRequests cs w = (cs.map fun c => w c.state).sum := by
  classical
  induction cs with
  | nil => simp [weightedRequests, requests]
  | cons c cs ih =>
    have hcons : weightedRequests (c :: cs) w = weightedRequests cs w + w c.state := by
      unfold weightedRequests
      simp only [requests, List.countP_cons, decide_eq_true_eq, Nat.cast_add,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_add, Finset.sum_add_distrib]
      congr 1
      simp
    rw [hcons, ih]
    simp [add_comm]

theorem weightedRequests_one (cs : List (Invocation E)) :
    weightedRequests cs (fun _ => 1) = cs.length := by
  rw [weightedRequests_eq_sum_log]
  simp

omit [Fintype V] in
theorem weightedRequests_head (cs : List (Invocation E)) (x : V) :
    weightedRequests cs (fun d => if G.head d = x then 1 else 0) =
      (cs.countP (fun c => decide (G.head c.state = x)) : ℝ) := by
  rw [weightedRequests_eq_sum_log]
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, decide_eq_true_eq,
      Nat.cast_add, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, ih]
    ring

omit [Fintype V] in
theorem sum_head_indicator (x : V) :
    (∑ d : Directed E, if G.head d = x then (1 : ℝ) else 0) = G.degree x := by
  classical
  rw [degree, Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Fintype.sum_bool, head]
  by_cases hl : G.left e = x
  · have hr : G.right e ≠ x := fun hr => G.loopless e (hl.trans hr.symm)
    simp [Incident, hl, hr]
  · by_cases hr : G.right e = x
    · simp [Incident, hl, hr]
    · simp [Incident, hl, hr]

variable [Nonempty V]

/-- Uniform order and uniform root, sampled independently. -/
noncomputable def randomRequest (_G : Graph V E) : Law (Rank E × V) :=
  (Rank.uniform (E := E)).bind fun ρ => (Law.uniform V).map fun v => (ρ, v)

theorem expect_randomRequest (f : Rank E × V → ℝ) :
    G.randomRequest.expect f = (Rank.uniform (E := E)).expect
      (fun ρ => (Law.uniform V).expect fun v => f (ρ, v)) := by
  rw [randomRequest, Law.expect_bind]
  simp only [Law.expect_map]

theorem expected_weighted_requests_eq (w : Directed E → ℝ) :
    G.randomRequest.expect (fun z => weightedRequests (G.vertexOracle z.1 z.2).calls w) =
      (∑ d, w d * (Rank.uniform (E := E)).expect (fun ρ => (G.Q ρ d : ℝ))) /
        Fintype.card V := by
  have hroot (ρ : Rank E) :
      (Law.uniform V).expect (fun v => weightedRequests (G.vertexOracle ρ v).calls w) =
        (∑ d, w d * (G.Q ρ d : ℝ)) / Fintype.card V := by
    rw [uniform_expect_eq_sum_div]
    congr 1
    unfold weightedRequests
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [← Finset.mul_sum]
    simp only [Q, Nat.cast_sum]
  rw [G.expect_randomRequest]
  simp_rw [hroot, div_eq_mul_inv]
  rw [Law.expect_mul_const, expect_sum]
  simp only [Law.expect_const_mul]

/-- A fixed nonnegative cost on each directed state can be accounted separately. -/
theorem expected_weighted_requests_le (w : Directed E → ℝ) (hw : ∀ d, 0 ≤ w d) :
    G.randomRequest.expect (fun z => weightedRequests (G.vertexOracle z.1 z.2).calls w) ≤
      (∑ d, w d) * G.callBudget / Fintype.card V := by
  rw [G.expected_weighted_requests_eq]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ d, w d * G.callBudget :=
      Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (G.expected_Q_le d) (hw d)
    _ = _ := (Finset.sum_mul ..).symm

noncomputable def totalInvocations (ρ : Rank E) (v : V) : ℕ :=
  (G.vertexOracle ρ v).calls.length

noncomputable def vertexInvocations (ρ : Rank E) (v x : V) : ℕ :=
  (G.vertexOracle ρ v).calls.countP fun c => decide (G.head c.state = x)

theorem expected_totalInvocations_le :
    G.randomRequest.expect (fun z => (G.totalInvocations z.1 z.2 : ℝ)) ≤
      (2 * Fintype.card E : ℝ) * G.callBudget / Fintype.card V := by
  have h := G.expected_weighted_requests_le (fun _ => 1) (fun _ => by norm_num)
  simpa only [weightedRequests_one, totalInvocations, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_prod, Fintype.card_bool,
    Nat.cast_mul, Nat.cast_ofNat, mul_comm (Fintype.card E : ℝ) 2] using h

theorem expected_vertexInvocations_le (x : V) :
    G.randomRequest.expect (fun z => (G.vertexInvocations z.1 z.2 x : ℝ)) ≤
      (G.degree x : ℝ) * G.callBudget / Fintype.card V := by
  have h := G.expected_weighted_requests_le (fun d => if G.head d = x then 1 else 0)
    (fun d => by split_ifs <;> norm_num)
  simpa only [G.weightedRequests_head, vertexInvocations, G.sum_head_indicator] using h

noncomputable def totalRequests (ρ : Rank E) (v : V) : ℕ :=
  1 + G.totalInvocations ρ v

noncomputable def vertexRequests (ρ : Rank E) (v x : V) : ℕ :=
  (if v = x then 1 else 0) + G.vertexInvocations ρ v x

theorem expected_root_charge (x : V) :
    G.randomRequest.expect (fun z => if z.2 = x then (1 : ℝ) else 0) =
      1 / Fintype.card V := by
  rw [G.expect_randomRequest]
  have hroot : (Law.uniform V).expect (fun v => if v = x then (1 : ℝ) else 0) =
      1 / Fintype.card V := by
    simp [Law.expect, Law.uniform, mul_ite, one_div]
  simp only [hroot, Law.expect_const]

theorem expected_totalRequests_le :
    G.randomRequest.expect (fun z => (G.totalRequests z.1 z.2 : ℝ)) ≤
      2 * (1 + (Fintype.card E : ℝ) / Fintype.card V) * G.callBudget := by
  have heq : (fun z : Rank E × V => (G.totalRequests z.1 z.2 : ℝ)) =
      fun z => 1 + (G.totalInvocations z.1 z.2 : ℝ) := by
    funext z
    simp [totalRequests]
  rw [heq, Law.expect_add, Law.expect_const]
  have hh := G.expected_totalInvocations_le
  have hb := G.callBudget_ge_one
  have ht : 2 * (1 + (Fintype.card E : ℝ) / Fintype.card V) * G.callBudget =
      2 * G.callBudget + (2 * Fintype.card E : ℝ) * G.callBudget / Fintype.card V := by ring
  rw [ht]
  linarith

theorem expected_vertexRequests_le (x : V) :
    G.randomRequest.expect (fun z => (G.vertexRequests z.1 z.2 x : ℝ)) ≤
      (1 + (G.degree x : ℝ)) * G.callBudget / Fintype.card V := by
  have heq : (fun z : Rank E × V => (G.vertexRequests z.1 z.2 x : ℝ)) =
      fun z => (if z.2 = x then 1 else 0) + (G.vertexInvocations z.1 z.2 x : ℝ) := by
    funext z
    simp [vertexRequests]
  rw [heq, Law.expect_add, G.expected_root_charge]
  calc
    _ ≤ 1 / (Fintype.card V : ℝ) +
        (G.degree x : ℝ) * G.callBudget / Fintype.card V :=
      add_le_add (le_refl _) (G.expected_vertexInvocations_le x)
    _ = (1 + (G.degree x : ℝ) * G.callBudget) / Fintype.card V := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (by nlinarith [G.callBudget_ge_one]) (Nat.cast_nonneg _)

end Graph

end SteinerUpperBound.Matching
