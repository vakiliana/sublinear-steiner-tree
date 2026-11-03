module

public import SteinerUpperBound.Matching.Padded.Budget

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical

theorem mixture_error (x q bad base tail : ℝ)
    (hmass : q + bad = 1) (hx : x = q * base + tail)
    (hbad : 0 ≤ bad) (hbase0 : 0 ≤ base) (hbase1 : base ≤ 1)
    (htail0 : 0 ≤ tail) (htail1 : tail ≤ bad) :
    |x - base| ≤ bad := by
  have hp0 := mul_nonneg hbad hbase0
  have hp1 := mul_le_mul_of_nonneg_left hbase1 hbad
  have hprod : q * base + bad * base = base := by rw [← add_mul, hmass, one_mul]
  apply abs_le.mpr
  constructor <;> nlinarith

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E] (P : Parameters S)

theorem Execution.matched_mean_error (v : V) (f : Bool → ℝ)
    (hf0 : ∀ value, 0 ≤ f value) (hf1 : ∀ value, f value ≤ 1) :
    |(Oracle.vertex S P v).expect (fun r => f r.value.isSome) -
        (Rank.uniform (E := E)).expect (fun ρ => f (G.vertexOracle ρ v).value.isSome)| ≤
      (Execution.law S P v).prob {x | ¬ Function.Injective x.2} := by
  classical
  let μ := Execution.law S P v
  let X : Execution.Space S P v → ℝ := fun x => f ((Oracle.vertex S P v).output x.1).value.isSome
  let Good : Execution.Space S P v → Prop := fun x => Function.Injective x.2
  let base := (Rank.uniform (E := E)).expect (fun ρ => f (G.vertexOracle ρ v).value.isSome)
  let q := μ.prob {x | Good x}
  let bad := μ.prob {x | ¬ Good x}
  let tail := μ.expect (fun x => if Good x then 0 else X x)
  have hq : q = (UniformRanks.law P.rankCard P.rankCard_pos (E := E)).prob {r | Function.Injective r} := by
    calc
      q = (μ.map Prod.snd).prob {r | Function.Injective r} :=
        (Law.prob_map μ Prod.snd {r : E → Fin P.rankCard | Function.Injective r}).symm
      _ = _ := by rw [Execution.ranks_marginal]
  have hgood : μ.expect (fun x => if Good x then X x else 0) = q * base := by
    have h := Execution.good_uniform_statistic S P v (fun r => f r.value.isSome)
    simp only [LocalRun.forget_value] at h
    rw [← hq] at h
    exact h
  have hmodel : (Oracle.vertex S P v).expect (fun r => f r.value.isSome) = μ.expect X := by
    have h := Execution.expect_output S P v (fun r _ => f r.value.isSome)
    simp only [Law.expect_const] at h
    exact h.symm
  have hsplit : μ.expect X = μ.expect (fun x => if Good x then X x else 0) + tail := by
    rw [← Law.expect_add]
    apply congrArg μ.expect
    funext x
    by_cases hx : Good x <;> simp only [hx, ↓reduceIte, zero_add, add_zero]
  have hmass : q + bad = 1 := by
    have h := μ.prob_compl {x | Good x}
    change bad = 1 - q at h
    linarith
  have htail0 : 0 ≤ tail := μ.expect_nonneg (fun x => by
    split_ifs
    · exact le_refl _
    · exact hf0 _)
  have htail1 : tail ≤ bad := by
    calc
      tail ≤ μ.expect (fun x => if Good x then 0 else 1) := μ.expect_mono (fun x => by
        split_ifs
        · exact le_refl _
        · exact hf1 _)
      _ = bad := by
        dsimp only [bad]
        unfold Law.expect Law.prob
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : Good x <;> simp [hx]
  exact mixture_error _ q bad base tail hmass
    (hmodel.trans (hsplit.trans (by rw [hgood])))
    (μ.prob_nonneg _) ((Rank.uniform (E := E)).expect_nonneg (fun _ => hf0 _))
    (by simpa only [Law.expect_const] using
      (Rank.uniform (E := E)).expect_mono (fun _ => hf1 _)) htail0 htail1

theorem Execution.matched_mean_error_budget (v : V) (f : Bool → ℝ)
    (hf0 : ∀ value, 0 ≤ f value) (hf1 : ∀ value, f value ≤ 1) :
    |(Oracle.vertex S P v).expect (fun r => f r.value.isSome) -
        (Rank.uniform (E := E)).expect (fun ρ => f (G.vertexOracle ρ v).value.isSome)| ≤
      1 / (P.Nstar : ℝ) ^ 30 :=
  (Execution.matched_mean_error S P v f hf0 hf1).trans (Parameters.tie_budget S P v)

end SteinerUpperBound.Matching.Padded
