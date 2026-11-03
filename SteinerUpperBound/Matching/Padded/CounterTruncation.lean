module

public import SteinerUpperBound.Matching.Padded.CounterTail

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical

theorem truncated_cost_of_tail {Ω : Type*} [Fintype Ω] (μ : Law Ω)
    (cost : Ω → ℝ) (unit δ a : ℝ) (hu : 0 < unit) (hδ : 0 ≤ δ)
    (hcost : ∀ ω, 0 ≤ cost ω)
    (htail : ∀ t, 0 < t → μ.prob {ω | t ≤ cost ω} ≤ δ + a / t) (J : ℕ) :
    μ.expect (fun ω => if cost ω ≤ unit * (2 : ℝ) ^ J then cost ω else 0) ≤
      unit + 2 * δ * unit * (2 : ℝ) ^ J + 2 * (J : ℝ) * a := by
  induction J with
  | zero =>
    have hbase : μ.expect (fun ω => if cost ω ≤ unit then cost ω else 0) ≤ unit := by
      have hh := μ.expect_mono (fun ω =>
        show (if cost ω ≤ unit then cost ω else 0) ≤ unit from
          by split_ifs with h; exact h; exact hu.le)
      simpa only [Law.expect_const] using hh
    norm_num only [pow_zero, mul_one, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    have hpos : 0 ≤ 2 * δ * unit := by positivity
    linarith
  | succ J ih =>
    have hcap : 0 < unit * (2 : ℝ) ^ J := by positivity
    have hnext : 0 ≤ unit * (2 : ℝ) ^ (J + 1) := by positivity
    have hpoint (ω : Ω) :
        (if cost ω ≤ unit * (2 : ℝ) ^ (J + 1) then cost ω else 0) ≤
          (if cost ω ≤ unit * (2 : ℝ) ^ J then cost ω else 0) +
            unit * (2 : ℝ) ^ (J + 1) *
              if unit * (2 : ℝ) ^ J ≤ cost ω then 1 else 0 := by
      rw [pow_succ]
      split_ifs <;> nlinarith [hcost ω]
    have he := μ.expect_mono hpoint
    rw [Law.expect_add, Law.expect_const_mul] at he
    have heq :
        μ.expect (fun ω => if unit * (2 : ℝ) ^ J ≤ cost ω then 1 else 0) =
          μ.prob {ω | unit * (2 : ℝ) ^ J ≤ cost ω} :=
      (Law.prob_eq_expect μ _).symm
    rw [heq] at he
    have hp := mul_le_mul_of_nonneg_left (htail (unit * (2 : ℝ) ^ J) hcap) hnext
    have hratio :
        unit * (2 : ℝ) ^ (J + 1) * (a / (unit * (2 : ℝ) ^ J)) = 2 * a := by
      rw [pow_succ]
      field_simp [hu.ne', pow_ne_zero J (by norm_num : (2 : ℝ) ≠ 0)]
      <;> ring
    calc
      _ ≤ _ := he
      _ ≤ (unit + 2 * δ * unit * (2 : ℝ) ^ J + 2 * (J : ℝ) * a) +
          unit * (2 : ℝ) ^ (J + 1) * (δ + a / (unit * (2 : ℝ) ^ J)) :=
        add_le_add ih hp
      _ = _ := by
        rw [mul_add, hratio, pow_succ]
        push_cast
        ring

namespace Causal

variable {M T A : Type*}

noncomputable def counterSeed (m : M → ℝ) (bits : T → Bool) (p : QueryProgram.Code M T A)
    (counter : Counter) (seed : (p.compile m).Seed) : ℝ :=
  counter.value (((p.compile m).tree seed).output bits)

/-- This event is on the original compiled program's seed, with no posterior coordinate. -/
noncomputable def counterGood (m : M → ℝ) (bits : T → Bool) (p : QueryProgram.Code M T A)
    (counter : Counter) (ceiling : ℝ) (seed : (p.compile m).Seed) : Prop :=
  counterSeed m bits p counter seed ≤ ceiling

theorem counterGood_cost (m : M → ℝ) (bits : T → Bool) (p : QueryProgram.Code M T A)
    (counter : Counter) (ceiling : ℝ) :
    (p.compile m).law.expect (fun seed => if counterGood m bits p counter ceiling seed then
      counterSeed m bits p counter seed else 0) =
    p.evaluate m bits (fun o => if counter.value o ≤ ceiling then counter.value o else 0) := by
  have he := QueryProgram.Code.compile_expect m bits p
    (fun o => if counter.value o ≤ ceiling then counter.value o else 0)
  apply Eq.trans _ he
  apply congrArg (p.compile m).law.expect
  funext seed
  dsimp only [counterGood, counterSeed]
  by_cases h : counter.value (((p.compile m).tree seed).output bits) ≤ ceiling <;> simp [h]

theorem counterGood_failure (m : M → ℝ) (bits : T → Bool) (p : QueryProgram.Code M T A)
    (counter : Counter) (ceiling : ℝ) :
    (p.compile m).law.prob {seed | ¬ counterGood m bits p counter ceiling seed} =
      p.evaluate m bits (fun o => if ¬ counter.value o ≤ ceiling then 1 else 0) := by
  rw [Law.prob_eq_expect]
  have he := QueryProgram.Code.compile_expect m bits p
    (fun o => if ¬ counter.value o ≤ ceiling then (1 : ℝ) else 0)
  apply Eq.trans _ he
  apply congrArg (p.compile m).law.expect
  funext seed
  dsimp only [counterGood, counterSeed, Set.mem_setOf_eq]
  by_cases h : counter.value (((p.compile m).tree seed).output bits) ≤ ceiling <;> simp [h]

theorem code_truncated_of_tail (m : M → ℝ) (bits : T → Bool) (p : QueryProgram.Code M T A)
    (counter : Counter) (unit δ a : ℝ) (hu : 0 < unit) (hδ : 0 ≤ δ)
    (htail : ∀ t, 0 < t →
      p.evaluate m bits (fun o => if t ≤ counter.value o then 1 else 0) ≤ δ + a / t)
    (J : ℕ) :
    p.evaluate m bits (fun o => if counter.value o ≤ unit * (2 : ℝ) ^ J then
      counter.value o else 0) ≤ unit + 2 * δ * unit * (2 : ℝ) ^ J + 2 * (J : ℝ) * a := by
  have ht (t : ℝ) (hpos : 0 < t) :
      (p.compile m).law.prob {seed | t ≤ counterSeed m bits p counter seed} ≤ δ + a / t := by
    rw [Law.prob_eq_expect]
    have he := QueryProgram.Code.compile_expect m bits p
      (fun o => if t ≤ counter.value o then (1 : ℝ) else 0)
    exact he.trans_le (htail t hpos)
  have hh := truncated_cost_of_tail (p.compile m).law (counterSeed m bits p counter)
    unit δ a hu hδ (fun seed => counter.value_nonneg _) ht J
  rw [← counterGood_cost m bits p counter (unit * (2 : ℝ) ^ J)]
  exact hh

end Causal

end SteinerUpperBound.Matching.Padded
