module

public import SteinerUpperBound.Matching.Padded.CoefficientBounds
public import SteinerUpperBound.Matching.Padded.GoodCost

@[expose] public section

set_option maxHeartbeats 2400000

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

private theorem scalar_cost_bound (h C r s L B D : ℝ)
    (hh : 1 ≤ h) (hC : 0 ≤ C) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hL0 : 0 ≤ L) (hB0 : 0 ≤ B) (hD0 : 0 ≤ D)
    (hL : L ≤ 16384 * h ^ 2) (hB : B ≤ 16777216 * h ^ 3)
    (hD : D ≤ 134217728 * h ^ 3) :
    2 * L * ((512 * h + 10) * ((1 + 2 * B) * s) + 2 * C) +
      L * C * (64 * h * (1 + 4 * B * r) + 64 * h) +
      C * ((1 + 4 * B * r) + 1) +
      (C * (64 * h) + (256 * h * C) * (1 + 4 * B * r) +
        32 * C * (D * (2 * B * r) + 1)) ≤
      (2 : ℝ) ^ 64 * h ^ 8 * (C * (1 + r) + s) := by
  let q := C * (1 + r) + s
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hcq : C ≤ q := by dsimp only [q]; nlinarith
  have hcrq : C * r ≤ q := by dsimp only [q]; nlinarith
  have hsq : s ≤ q := by dsimp only [q]; nlinarith
  have hp (k : ℕ) (hk : k ≤ 8) : h ^ k ≤ h ^ 8 := pow_le_pow_right₀ hh hk
  have hc (k : ℕ) (hk : k ≤ 8) : C * h ^ k ≤ q * h ^ 8 :=
    mul_le_mul hcq (hp k hk) (by positivity) hq
  have hcr (k : ℕ) (hk : k ≤ 8) : C * r * h ^ k ≤ q * h ^ 8 :=
    mul_le_mul hcrq (hp k hk) (by positivity) hq
  have hsw (k : ℕ) (hk : k ≤ 8) : s * h ^ k ≤ q * h ^ 8 :=
    mul_le_mul hsq (hp k hk) (by positivity) hq
  calc
    _ ≤
      2 * (16384 * h ^ 2) *
          ((512 * h + 10) * ((1 + 2 * (16777216 * h ^ 3)) * s) + 2 * C) +
        (16384 * h ^ 2) * C *
          (64 * h * (1 + 4 * (16777216 * h ^ 3) * r) + 64 * h) +
        C * ((1 + 4 * (16777216 * h ^ 3) * r) + 1) +
        (C * (64 * h) + (256 * h * C) * (1 + 4 * (16777216 * h ^ 3) * r) +
          32 * C * ((134217728 * h ^ 3) * (2 * (16777216 * h ^ 3) * r) + 1)) := by
      gcongr
    _ ≤ _ := by
      change _ ≤ (2 : ℝ) ^ 64 * h ^ 8 * q
      have hq8 : 0 ≤ q * h ^ 8 := mul_nonneg hq (by positivity)
      nlinarith only [hc 0 (by omega), hc 1 (by omega), hc 2 (by omega),
        hc 3 (by omega), hc 4 (by omega), hcr 3 (by omega), hcr 4 (by omega),
        hcr 6 (by omega), hsw 2 (by omega), hsw 3 (by omega),
        hsw 5 (by omega), hsw 6 (by omega), hq8]

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E]
    (P : Parameters S)

noncomputable def Account.publicPrice (A : Account S) : ℝ :=
  A.Cstar * (1 + (Fintype.card E : ℝ) / Fintype.card V) +
    (∑ v, A.W v) / Fintype.card V

def Parameters.costFactor : ℝ := (2 : ℝ) ^ 64 * (P.logarithm : ℝ) ^ 8

noncomputable def Execution.goodCost (A : Account S) (v : V) : ℝ :=
  (Execution.law S P v).expect (fun x : Execution.Space S P v => if Function.Injective x.2 then
    (Oracle.vertex S P v).cost (Command.charge A) A.rate x.1 else 0)

theorem Execution.goodCost_nonneg (A : Account S) (v : V) :
    0 ≤ Execution.goodCost S P A v := by
  apply Law.expect_nonneg
  intro x
  split
  · exact Program.cost_nonneg _ _ _ (Command.charge_nonneg A) A.rate_nonneg _
  · exact le_refl _

theorem Execution.expected_goodCost_le [Nonempty V] (A : Account S) :
    (Law.uniform V).expect (fun v => Execution.goodCost S P A v) ≤
      Parameters.costFactor S P * Account.publicPrice S A := by
  let h : ℝ := P.logarithm
  let r : ℝ := (Fintype.card E : ℝ) / Fintype.card V
  let s : ℝ := (∑ v, A.W v) / Fintype.card V
  let L : ℝ := Parameters.bucketCoefficient S P
  let B : ℝ := G.callBudget
  let D : ℝ := (_root_.SteinerUpperBound.Matching.Budget.depth (2 * P.logarithm) : ℝ) + 1
  have hh : 1 ≤ h := by
    dsimp only [h]
    exact_mod_cast (show 1 ≤ P.logarithm from Parameters.logarithm_pos S P)
  have hC0 := A.Cstar_nonneg
  have hrate := A.rate_le_Cstar
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hs : 0 ≤ s := by
    dsimp only [s]
    exact div_nonneg (Finset.sum_nonneg fun v _ => A.W_nonneg v) (Nat.cast_nonneg _)
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have hB0 : 0 ≤ B := le_trans (by norm_num) G.callBudget_ge_one
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hL : L ≤ 16384 * h ^ 2 := by
    dsimp only [L, h]
    exact_mod_cast Parameters.bucketCoefficient_poly S P
  have hB : B ≤ 16777216 * h ^ 3 := Parameters.callBudget_power S P
  have hD : D ≤ 134217728 * h ^ 3 := Parameters.depth_power S P
  have hH : (P.rankExponent : ℝ) + 1 ≤ 64 * h := by
    dsimp only [h, Parameters.rankExponent]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    dsimp only [h] at hh
    linarith
  have hstatic : (P.rankExponent + P.sortHeight + 12 : ℕ) ≤ 64 * h := by
    convert Parameters.static_work_power S P using 1 <;> push_cast <;> rfl
  have hrequest : requestWork S P A ≤ 256 * h * A.Cstar := by
    have hc := mul_le_mul_of_nonneg_left (Parameters.request_work_power S P) A.rate_nonneg
    have hr' := mul_le_mul_of_nonneg_left A.rate_le_Cstar
      (show 0 ≤ 256 * h by positivity)
    dsimp only [requestWork]
    push_cast
    nlinarith
  have hbase :
      1 + (4 * Fintype.card E : ℝ) * G.callBudget / Fintype.card V =
        1 + 4 * B * r := by dsimp only [r, B]; ring
  have hdense :
      (1 + 2 * G.callBudget) * (∑ v, A.W v) / Fintype.card V = (1 + 2 * B) * s := by
    dsimp only [B, s]
    ring
  have hpair :
      (2 * Fintype.card E : ℝ) * G.callBudget / Fintype.card V = 2 * B * r := by
    dsimp only [B, r]
    ring
  have hbad :
      (∑ v, A.W v) * ((Fintype.card E : ℝ) ^ 2 / P.rankCard +
        Fintype.card V * (P.rankExponent + 2) * Real.exp (-(64 : ℝ) * h)) ≤
          2 * A.Cstar := by
    have ht := Parameters.weighted_tie_le S P A
    have hd := Parameters.weighted_density_le S P A
    dsimp only [h]
    nlinarith
  have hres := Parameters.residual_tie_le_one S P
  have htrace := Parameters.trace_exception_le_one S P
  have htraceprob := (Rank.uniform (E := E)).prob_nonneg {ρ |
    G.LongStack (_root_.SteinerUpperBound.Matching.Budget.depth (2 * P.logarithm)) ρ}
  have hb := Oracle.bucket_expectation S P A (64 * h) (by positivity)
  have hexp : Real.exp (-(64 * h)) = Real.exp (-(64 : ℝ) * h) := by
    apply congrArg Real.exp
    ring
  rw [hexp, hbase, hdense] at hb
  have hb' :
      (Law.uniform V).expect (fun v =>
        (Oracle.vertex S P v).expectedCost (Command.bucketCharge A) A.rate) ≤
      2 * L * ((512 * h + 10) * ((1 + 2 * B) * s) + 2 * A.Cstar) +
        L * A.Cstar * (64 * h * (1 + 4 * B * r) + 64 * h) +
        A.Cstar * ((1 + 4 * B * r) + 1) := by
    apply hb.trans
    have hlevels :
        ((P.rankExponent : ℝ) + 1) * (1 + 4 * B * r) +
          ((P.rankExponent : ℝ) + 1) * Fintype.card V *
            ((Fintype.card E : ℝ) ^ 2 / P.rankCard) ≤
        64 * h * (1 + 4 * B * r) + 64 * h := by
      calc
        _ = ((P.rankExponent : ℝ) + 1) * (1 + 4 * B * r) +
          ((P.rankExponent : ℝ) + 1) *
            ((Fintype.card V : ℝ) * ((Fintype.card E : ℝ) ^ 2 / P.rankCard)) := by ring
        _ ≤ 64 * h * (1 + 4 * B * r) + 64 * h * 1 := by gcongr
        _ = _ := by ring
    have hfirst := mul_le_mul_of_nonneg_left hbad (show 0 ≤ 2 * L by positivity)
    have hlevel := mul_le_mul_of_nonneg_left hlevels
      (show 0 ≤ L * A.Cstar by positivity)
    have hprep := mul_le_mul_of_nonneg_left hres A.Cstar_nonneg
    dsimp only [L, B] at *
    nlinarith
  have ha := Execution.oracle_good_expectation S P A
    (_root_.SteinerUpperBound.Matching.Budget.depth (2 * P.logarithm))
  rw [hbase, hpair] at ha
  have ha' :
      (Law.uniform V).expect (fun v => (Execution.law S P v).expect (fun x =>
        if Function.Injective x.2 then
          (Oracle.vertex S P v).cost (Command.oracleCharge A) 0 x.1 else 0)) ≤
      A.Cstar * (64 * h) + (256 * h * A.Cstar) * (1 + 4 * B * r) +
        32 * A.Cstar * (D * (2 * B * r) + 1) := by
    apply ha.trans
    change A.rate * (P.rankExponent + P.sortHeight + 12 : ℕ) +
      requestWork S P A * (1 + 4 * B * r) +
      32 * A.rate * (D * (2 * B * r) + _) ≤ _
    gcongr
  have hall := (Law.uniform V).expect_mono (fun v => Execution.good_cost_split S P A v)
  rw [Law.expect_add] at hall
  have hsum := hall.trans (add_le_add hb' ha')
  have hscalar := scalar_cost_bound h A.Cstar r s L B D hh A.Cstar_nonneg hr hs
    hL0 hB0 hD0 hL hB hD
  dsimp only [Execution.goodCost, Parameters.costFactor, Account.publicPrice]
  exact hsum.trans hscalar

end SteinerUpperBound.Matching.Padded
