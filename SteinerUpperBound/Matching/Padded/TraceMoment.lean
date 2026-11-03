module

public import SteinerUpperBound.Matching.Padded.AgedTrace
public import SteinerUpperBound.Matching.Padded.TruncatedMoments

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} [Fintype V] [Fintype E]

theorem agedTrace_nonneg (cs : List (Invocation E)) : 0 ≤ agedTrace (-1) cs := by
  unfold agedTrace
  apply List.sum_nonneg
  intro value hv
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hv
  have h := Nat.cast_nonneg (α := ℝ) c.ancestors.length
  linarith

theorem agedTrace_le_length (cs : List (Invocation E)) (B : ℝ)
    (h : ∀ c ∈ cs, (c.ancestors.length : ℝ) + 2 ≤ B) :
    agedTrace (-1) cs ≤ B * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc := h c (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [agedTrace_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem calls_length_le (G : Graph V E) (ρ : Rank E) (v : V) :
    ((G.vertexOracle ρ v).calls.length : ℝ) ≤
      (2 * Fintype.card E : ℝ) * (2 * Fintype.card E + 1) := by
  rw [← Graph.weightedRequests_one]
  unfold Graph.weightedRequests
  calc
    _ ≤ ∑ _d : Directed E, (2 * Fintype.card E + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      simp only [one_mul]
      exact_mod_cast G.vertexOracle_requests_le ρ v d
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      ring

theorem agedTrace_all_le (G : Graph V E) (ρ : Rank E) (v : V) :
    agedTrace (-1) (G.vertexOracle ρ v).calls ≤
      (Fintype.card E + 1 : ℝ) * (2 * Fintype.card E) * (2 * Fintype.card E + 1) := by
  have ha := agedTrace_le_length (G.vertexOracle ρ v).calls (Fintype.card E + 1) (fun c hc => by
    have hh := G.validStack_length_le_copies ρ (G.vertexOracle_validStack ρ v c hc)
    simp only [List.length_cons] at hh
    exact_mod_cast (show c.ancestors.length + 2 ≤ Fintype.card E + 1 by omega))
  have hm := mul_le_mul_of_nonneg_left (calls_length_le G ρ v)
    (show (0 : ℝ) ≤ Fintype.card E + 1 by positivity)
  exact ha.trans (by convert hm using 1 <;> ring)

theorem agedTrace_short_le (G : Graph V E) (D : ℕ) (ρ : Rank E) (v : V)
    (h : ¬ G.LongStack D ρ) :
    agedTrace (-1) (G.vertexOracle ρ v).calls ≤ (D + 1 : ℝ) * (G.vertexOracle ρ v).calls.length := by
  apply agedTrace_le_length
  intro c hc
  have hlen : c.ancestors.length < D := by
    by_contra hn
    exact h ⟨c.state, c.ancestors, G.vertexOracle_validStack ρ v c hc, Nat.le_of_not_gt hn⟩
  exact_mod_cast (show c.ancestors.length + 2 ≤ D + 1 by omega)

theorem expected_agedTrace [Nonempty V] (G : Graph V E) (D : ℕ) :
    G.randomRequest.expect (fun z => agedTrace (-1) (G.vertexOracle z.1 z.2).calls) ≤
      (D + 1 : ℝ) * ((2 * Fintype.card E : ℝ) * G.callBudget / Fintype.card V) +
        ((Fintype.card E + 1 : ℝ) * (2 * Fintype.card E) * (2 * Fintype.card E + 1)) *
          (Rank.uniform (E := E)).prob {ρ | G.LongStack D ρ} := by
  classical
  have hh := expect_one_bad G.randomRequest
    (fun z => agedTrace (-1) (G.vertexOracle z.1 z.2).calls)
    (fun z => ((G.vertexOracle z.1 z.2).calls.length : ℝ))
    (fun z => ¬ G.LongStack D z.1) (D + 1)
    ((Fintype.card E + 1 : ℝ) * (2 * Fintype.card E) * (2 * Fintype.card E + 1))
    (by positivity) (by positivity) (fun _ => Nat.cast_nonneg _)
    (fun z => agedTrace_all_le G z.1 z.2) (fun z h => agedTrace_short_le G D z.1 z.2 h)
  have hraw : G.randomRequest.expect (fun z => ((G.vertexOracle z.1 z.2).calls.length : ℝ)) ≤
      (2 * Fintype.card E : ℝ) * G.callBudget / Fintype.card V := by
    simpa only [Graph.totalInvocations] using G.expected_totalInvocations_le
  have hcut : G.randomRequest.expect (fun z => @ite ℝ (¬ G.LongStack D z.1)
      (Classical.propDecidable _) ((G.vertexOracle z.1 z.2).calls.length : ℝ) 0) ≤
      G.randomRequest.expect (fun z => ((G.vertexOracle z.1 z.2).calls.length : ℝ)) := by
    apply G.randomRequest.expect_mono
    intro z
    by_cases hz : G.LongStack D z.1
    · simp only [hz, not_true_eq_false, ↓reduceIte]
      exact Nat.cast_nonneg _
    · simp only [hz, not_false_eq_true, ↓reduceIte]
      exact le_refl (((G.vertexOracle z.1 z.2).calls.length : ℝ))
  have hc := hcut.trans hraw
  have hp : G.randomRequest.prob {z | ¬ ¬ G.LongStack D z.1} =
      (Rank.uniform (E := E)).prob {ρ | G.LongStack D ρ} := by
    rw [Law.prob_eq_expect, G.expect_randomRequest]
    simp only [not_not, Law.expect_const]
    rw [Law.prob_eq_expect]
    apply congrArg (Rank.uniform (E := E)).expect
    funext ρ
    by_cases h : G.LongStack D ρ <;> simp [h]
  rw [hp] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hc (by positivity)) (le_refl _))

variable (S : Slots G) (P : Parameters S)

theorem expected_good_agedTrace [Nonempty V] (D : ℕ) :
    (Law.uniform V).expect (fun v => (Execution.law S P v).expect (fun x =>
      if Function.Injective x.2 then agedTrace (-1) ((Oracle.vertex S P v).output x.1).calls else 0)) ≤
      (D + 1 : ℝ) * ((2 * Fintype.card E : ℝ) * G.callBudget / Fintype.card V) +
        ((Fintype.card E + 1 : ℝ) * (2 * Fintype.card E) * (2 * Fintype.card E + 1)) *
          (Rank.uniform (E := E)).prob {ρ | G.LongStack D ρ} := by
  have hv (v : V) := Execution.good_uniform_statistic S P v (fun r => agedTrace (-1) r.calls)
  simp only [LocalRun.forget_calls] at hv
  simp_rw [hv]
  rw [Law.expect_const_mul, UniformOrder.expect_commute,
    ← G.expect_randomRequest (fun z => agedTrace (-1) (G.vertexOracle z.1 z.2).calls)]
  have hn := G.randomRequest.expect_nonneg (fun z => agedTrace_nonneg (G.vertexOracle z.1 z.2).calls)
  have hp := (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).prob_le_one {r | Function.Injective r}
  have hmul :
      (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).prob {r | Function.Injective r} *
        G.randomRequest.expect (fun z => agedTrace (-1) (G.vertexOracle z.1 z.2).calls) ≤
      G.randomRequest.expect (fun z => agedTrace (-1) (G.vertexOracle z.1 z.2).calls) := by nlinarith
  exact hmul.trans (expected_agedTrace G D)

end SteinerUpperBound.Matching.Padded
