module

public import SteinerUpperBound.Matching.Padded.Density

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} [Fintype V] [Fintype E]

theorem sum_head_weight (u : V → ℝ) :
    (∑ d : Directed E, u (G.head d)) = ∑ v, u v * (G.degree v : ℝ) := by
  have he (d : Directed E) : u (G.head d) = ∑ v, u v * (if G.head d = v then (1 : ℝ) else 0) := by
    simp [mul_ite, eq_comm]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.mul_sum, G.sum_head_indicator v]

theorem sum_tail_weight (u : V → ℝ) :
    (∑ d : Directed E, u (G.tail d)) = ∑ v, u v * (G.degree v : ℝ) := by
  have he (d : Directed E) : u (G.tail d) = ∑ v, u v * (if G.tail d = v then (1 : ℝ) else 0) := by
    simp [mul_ite, eq_comm]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.mul_sum, Execution.sum_tail_indicator v]

theorem sum_state_weight (u : V → ℝ) :
    (∑ d : Directed E, (u (G.head d) + u (G.tail d))) =
      2 * ∑ v, (G.degree v : ℝ) * u v := by
  rw [Finset.sum_add_distrib, sum_head_weight, sum_tail_weight]
  simp only [mul_comm (G.degree _ : ℝ)]
  ring

variable (S : Slots G) (P : Parameters S)

theorem densityWeight_sum_le (A : Account S) : (∑ v, densityWeight S A v) ≤ ∑ v, A.W v :=
  Finset.sum_le_sum fun v _ => densityWeight_le S A v

theorem densityWeight_states_le (A : Account S) :
    (∑ d : Directed E, (densityWeight S A (G.head d) + densityWeight S A (G.tail d))) ≤
      2 * ∑ v, A.W v := by
  rw [sum_state_weight]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => densityWeight_degree_le S A v) (by norm_num)

theorem expected_good_densityRequests [Nonempty V] (A : Account S) :
    (Law.uniform V).expect (fun v => (Execution.law S P v).expect (fun x =>
      if Function.Injective x.2 then
        Cache.requestValue S P.rankCard (densityWeight S A)
          ((Oracle.vertex S P v).output x.1).cache else 0)) ≤
      (1 + 2 * G.callBudget) * (∑ v, A.W v) / Fintype.card V := by
  have hh := Execution.expected_good_requestValue S P (densityWeight S A) (densityWeight_nonneg S A)
  have hsum := densityWeight_sum_le S A
  have hstates := densityWeight_states_le S A
  have hB := G.callBudget_ge_one
  have hfirst := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ _)
  have hsecond := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hstates (by linarith : 0 ≤ G.callBudget))
    (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ _)
  apply hh.trans
  convert add_le_add hfirst hsecond using 1 <;> ring

theorem expected_good_totalRequests [Nonempty V] :
    (Law.uniform V).expect (fun v => (Execution.law S P v).expect (fun x =>
      if Function.Injective x.2 then
        Cache.requestValue S P.rankCard (fun _ => 1)
          ((Oracle.vertex S P v).output x.1).cache else 0)) ≤
      1 + (4 * Fintype.card E : ℝ) * G.callBudget / Fintype.card V := by
  have hh := Execution.expected_good_requestValue S P (fun _ => 1) (fun _ => zero_le_one)
  have hm : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_prod,
    Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, div_self hm] at hh
  convert hh using 1 <;> ring

end SteinerUpperBound.Matching.Padded
