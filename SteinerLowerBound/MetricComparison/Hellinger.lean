module

public import SteinerLowerBound.ProductProbability

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Law

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

noncomputable def affinity (μ ν : Law Ω) : ℝ :=
  ∑ ω, Real.sqrt (μ.mass ω) * Real.sqrt (ν.mass ω)

theorem affinity_nonneg (μ ν : Law Ω) : 0 ≤ affinity μ ν :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem affinity_le_one (μ ν : Law Ω) : affinity μ ν ≤ 1 := by
  have h := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset Ω) μ.nonneg ν.nonneg
  simpa only [affinity, μ.total, ν.total, Real.sqrt_one, mul_one] using h

@[simp]
theorem affinity_self (μ : Law Ω) : affinity μ μ = 1 := by
  unfold affinity
  simpa only [Real.mul_self_sqrt, μ.nonneg] using μ.total

theorem sqrt_difference_sum (μ ν : Law Ω) :
    (∑ ω, (Real.sqrt (μ.mass ω) - Real.sqrt (ν.mass ω)) ^ 2) =
      2 * (1 - affinity μ ν) := by
  have h (ω : Ω) :
      (Real.sqrt (μ.mass ω) - Real.sqrt (ν.mass ω)) ^ 2 =
        μ.mass ω + ν.mass ω -
          2 * (Real.sqrt (μ.mass ω) * Real.sqrt (ν.mass ω)) := by
    nlinarith [Real.sq_sqrt (μ.nonneg ω), Real.sq_sqrt (ν.nonneg ω)]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    μ.total, ν.total, affinity]
  ring

theorem sqrt_addition_sum (μ ν : Law Ω) :
    (∑ ω, (Real.sqrt (μ.mass ω) + Real.sqrt (ν.mass ω)) ^ 2) =
      2 * (1 + affinity μ ν) := by
  have h (ω : Ω) :
      (Real.sqrt (μ.mass ω) + Real.sqrt (ν.mass ω)) ^ 2 =
        μ.mass ω + ν.mass ω +
          2 * (Real.sqrt (μ.mass ω) * Real.sqrt (ν.mass ω)) := by
    nlinarith [Real.sq_sqrt (μ.nonneg ω), Real.sq_sqrt (ν.nonneg ω)]
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, μ.total, ν.total, affinity]
  ring

theorem close_of_affinity (μ ν : Law Ω) :
    Close μ ν (2 * Real.sqrt (2 * (1 - affinity μ ν))) := by
  classical
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset Ω)
    (fun ω => |Real.sqrt (μ.mass ω) - Real.sqrt (ν.mass ω)|)
    (fun ω => Real.sqrt (μ.mass ω) + Real.sqrt (ν.mass ω))
  simp only [sq_abs, sqrt_difference_sum, sqrt_addition_sum] at hcs
  have hs : Real.sqrt (2 * (1 + affinity μ ν)) ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [affinity_le_one μ ν]
  have hprod :
      ∑ ω, |μ.mass ω - ν.mass ω| ≤
        2 * Real.sqrt (2 * (1 - affinity μ ν)) := by
    calc
      _ = ∑ ω, |Real.sqrt (μ.mass ω) - Real.sqrt (ν.mass ω)| *
          (Real.sqrt (μ.mass ω) + Real.sqrt (ν.mass ω)) := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
          ← abs_mul]
        congr 1
        nlinarith [Real.sq_sqrt (μ.nonneg ω), Real.sq_sqrt (ν.nonneg ω)]
      _ ≤ _ := hcs.trans (by
        nlinarith [Real.sqrt_nonneg (2 * (1 - affinity μ ν))])
  intro E
  unfold prob
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply le_trans _ hprod
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ω ∈ E <;> simp [h]

noncomputable def step (μ : Law Ω) (k : Ω → Law Γ) : Law (Ω × Γ) where
  mass x := μ.mass x.1 * (k x.1).mass x.2
  nonneg x := mul_nonneg (μ.nonneg x.1) ((k x.1).nonneg x.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, (k _).total, mul_one, μ.total]

theorem affinity_step (μ ν : Law Ω) (k l : Ω → Law Γ) :
    affinity (step μ k) (step ν l) =
      ∑ ω, Real.sqrt (μ.mass ω) * Real.sqrt (ν.mass ω) * affinity (k ω) (l ω) := by
  simp only [affinity, step, Fintype.sum_prod_type, Real.sqrt_mul (μ.nonneg _),
    Real.sqrt_mul (ν.nonneg _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro γ _
  ring

theorem affinity_step_defect (μ ν : Law Ω) (k l : Ω → Law Γ)
    {ε δ : ℝ} (hε : 1 - affinity μ ν ≤ ε) (hδ₀ : 0 ≤ δ)
    (hδ : ∀ ω, 1 - affinity (k ω) (l ω) ≤ δ) :
    1 - affinity (step μ k) (step ν l) ≤ ε + δ := by
  rw [affinity_step]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset Ω))
    (f := fun ω => Real.sqrt (μ.mass ω) * Real.sqrt (ν.mass ω) *
      (1 - affinity (k ω) (l ω)))
    (g := fun ω => Real.sqrt (μ.mass ω) * Real.sqrt (ν.mass ω) * δ)
    (fun ω _ => mul_le_mul_of_nonneg_left (hδ ω)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, ← Finset.sum_mul] at h
  have h' := mul_le_mul_of_nonneg_right (affinity_le_one μ ν) hδ₀
  unfold affinity at hε h'
  linarith

end Law

namespace MetricComparison

@[reducible] def Answers : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × Answers n

@[instance_reducible]
instance answersFintype : (n : ℕ) → Fintype (Answers n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd Bool (Answers n) inferInstance (answersFintype n)

noncomputable def sequential {X : Type*} (kernel : X → Law Bool)
    (next : X → Bool → X) : (n : ℕ) → X → Law (Answers n)
  | 0, _ => Law.pure ()
  | n + 1, x => Law.step (kernel x) (fun b => sequential kernel next n (next x b))

theorem sequential_affinity {X Y : Type*}
    (kernel : X → Law Bool) (next : X → Bool → X)
    (kernel' : Y → Law Bool) (next' : Y → Bool → Y)
    (Rel : X → Y → Prop)
    (stable : ∀ x y, Rel x y → ∀ b, Rel (next x b) (next' y b))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hlocal : ∀ x y, Rel x y → 1 - Law.affinity (kernel x) (kernel' y) ≤ ε)
    (n : ℕ) (x : X) (y : Y) (hxy : Rel x y) :
    1 - Law.affinity (sequential kernel next n x) (sequential kernel' next' n y) ≤
      n * ε := by
  induction n generalizing x y with
  | zero => simp [sequential]
  | succ n ih =>
      have h := Law.affinity_step_defect (kernel x) (kernel' y)
        (fun b => sequential kernel next n (next x b))
        (fun b => sequential kernel' next' n (next' y b))
        (hlocal x y hxy) (mul_nonneg (Nat.cast_nonneg n) hε)
        (fun b => ih _ _ (stable x y hxy b))
      change 1 - Law.affinity (Law.step (kernel x)
        (fun b => sequential kernel next n (next x b)))
        (Law.step (kernel' y) (fun b => sequential kernel' next' n (next' y b))) ≤ _
      convert h using 1 <;> push_cast <;> ring

theorem sequential_close {X Y : Type*}
    (kernel : X → Law Bool) (next : X → Bool → X)
    (kernel' : Y → Law Bool) (next' : Y → Bool → Y)
    (Rel : X → Y → Prop)
    (stable : ∀ x y, Rel x y → ∀ b, Rel (next x b) (next' y b))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hlocal : ∀ x y, Rel x y → 1 - Law.affinity (kernel x) (kernel' y) ≤ ε)
    (n : ℕ) (x : X) (y : Y) (hxy : Rel x y) :
    Law.Close (sequential kernel next n x) (sequential kernel' next' n y)
      (2 * Real.sqrt (2 * (n : ℝ) * ε)) := by
  apply (Law.close_of_affinity _ _).mono
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  have h := sequential_affinity kernel next kernel' next' Rel stable hε hlocal n x y hxy
  nlinarith

end MetricComparison

end SteinerLowerBound
