module

public import SteinerUpperBound.Covers.Probability

@[expose] public section

namespace SteinerUpperBound.Covers.Factory

open SteinerLowerBound
open scoped Classical BigOperators
open ClosedRelation

variable {U : Type*} [Fintype U] [Nonempty U]

/-- `none` is the explicit finite-tape exhaustion flag. -/
noncomputable def law (R : U → U → Prop) (x : U) : ℕ → ℕ → Law (Option Bool)
  | 0, 0 => Law.pure (some false)
  | 0, _ + 1 => Law.pure none
  | _ + 1, 0 => Law.pure (some false)
  | B + 1, ψ + 1 => (Law.uniform U).bind (fun y =>
      if y = x then Law.pure (some true)
      else if R x y then law R x B ψ else law R x B (ψ + 1))

noncomputable def bitLaw (R : U → U → Prop) (x : U) (B ψ : ℕ) : Law Bool :=
  (law R x B ψ).map (fun b => b.getD false)

def scan (R : U → U → Prop) [DecidableRel R] [DecidableEq U] (x : U) :
    (B : ℕ) → ℕ → (Fin B → U) → Option Bool
  | 0, 0, _ => some false
  | 0, _ + 1, _ => none
  | _ + 1, 0, _ => some false
  | B + 1, ψ + 1, w =>
      if w 0 = x then some true
      else if R x (w 0) then scan R x B ψ (Fin.tail w)
      else scan R x B (ψ + 1) (Fin.tail w)

def draws (R : U → U → Prop) [DecidableRel R] [DecidableEq U] (x : U) :
    (B : ℕ) → ℕ → (Fin B → U) → ℕ
  | 0, _, _ => 0
  | _ + 1, 0, _ => 0
  | B + 1, ψ + 1, w =>
      if w 0 = x then 1
      else 1 + draws R x B (if R x (w 0) then ψ else ψ + 1) (Fin.tail w)

theorem draws_le (R : U → U → Prop) [DecidableRel R] [DecidableEq U]
    (x : U) (B ψ : ℕ) (w : Fin B → U) : draws R x B ψ w ≤ B := by
  induction B generalizing ψ with
  | zero => simp [draws]
  | succ B ih =>
    cases ψ with
    | zero => simp [draws]
    | succ ψ =>
      simp only [draws]
      by_cases hx : w 0 = x
      · simp [hx]
      · rw [if_neg hx]
        simpa only [Nat.add_comm] using Nat.add_le_add_left
          (ih (if R x (w 0) then ψ else ψ + 1) (Fin.tail w)) 1

theorem scan_law (R : U → U → Prop) (x : U) (B ψ : ℕ) :
    ((FiniteSampling.tape (Law.uniform U) B).map (scan R x B ψ)) = law R x B ψ := by
  classical
  induction B generalizing ψ with
  | zero =>
    cases ψ <;> apply LawOperations.ext_prob <;> intro E <;>
      simp [FiniteSampling.tape, Law.prob_map, Law.prob_pure, scan, law]
  | succ B ih =>
    cases ψ with
    | zero =>
      simpa only [scan, law] using
        FiniteSampling.map_const (FiniteSampling.tape (Law.uniform U) (B + 1)) (some false)
    | succ ψ =>
      rw [FiniteSampling.map_tape_succ]
      simp only [law]
      congr 1
      funext y
      by_cases hy : y = x
      · simp only [scan, Fin.cons_zero, hy, ↓reduceIte]
        exact FiniteSampling.map_const _ _
      · by_cases hR : R x y
        · simpa only [scan, Fin.cons_zero, hy, hR, ↓reduceIte, Fin.tail_cons] using ih ψ
        · simpa only [scan, Fin.cons_zero, hy, hR, ↓reduceIte, Fin.tail_cons] using ih (ψ + 1)

theorem harmonic (R : U → U → Prop) (hrefl : ∀ x, R x x) (x : U) (ψ : ℕ) :
    (Law.uniform U).bind (fun y =>
      if y = x then Law.pure true
      else if R x y then CategoricalCoupling.bernoulli (retentionRate R hrefl ψ x)
      else CategoricalCoupling.bernoulli (retentionRate R hrefl (ψ + 1) x)) =
        CategoricalCoupling.bernoulli (retentionRate R hrefl (ψ + 1) x) := by
  classical
  apply FiniteSampling.bool_ext
  change (Law.uniform U).expect (fun y =>
    (if y = x then Law.pure true
      else if R x y then CategoricalCoupling.bernoulli (retentionRate R hrefl ψ x)
      else CategoricalCoupling.bernoulli (retentionRate R hrefl (ψ + 1) x)).mass true) = _
  have hf (y : U) :
      (if y = x then Law.pure true
        else if R x y then CategoricalCoupling.bernoulli (retentionRate R hrefl ψ x)
        else CategoricalCoupling.bernoulli (retentionRate R hrefl (ψ + 1) x)).mass true =
      if y = x then 1
        else if y ∈ neighborhood R x then (retentionRate R hrefl ψ x : ℝ)
        else (retentionRate R hrefl (ψ + 1) x : ℝ) := by
    by_cases hy : y = x <;> by_cases hR : R x y <;>
      simp [hy, hR, neighborhood, Law.pure, CategoricalCoupling.bernoulli]
  simp_rw [hf]
  rw [FiniteSampling.uniform_expect, FiniteSampling.sum_three
    (neighborhood R x) x (by simp [neighborhood, hrefl])]
  change (1 + ((degree R x : ℝ) - 1) * (retentionRate R hrefl ψ x : ℝ) +
    ((Fintype.card U : ℝ) - degree R x) *
      (retentionRate R hrefl (ψ + 1) x : ℝ)) / Fintype.card U =
        (retentionRate R hrefl (ψ + 1) x : ℝ)
  have hk : (Fintype.card U : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (degree R x : ℝ) ≠ 0 := by
    exact_mod_cast (degree_pos R hrefl x).ne'
  have hq : (degree R x : ℝ) * (retentionRate R hrefl (ψ + 1) x : ℝ) =
      1 + ((degree R x : ℝ) - 1) * (retentionRate R hrefl ψ x : ℝ) := by
    dsimp [retentionRate, reciprocalRate]
    rw [pow_succ]
    field_simp
    <;> ring
  apply (div_eq_iff hk).mpr
  nlinarith

theorem bitLaw_zero (R : U → U → Prop) (x : U) (B : ℕ) :
    bitLaw R x B 0 = Law.pure false := by
  cases B <;> apply LawOperations.ext_prob <;> intro E <;>
    simp [bitLaw, law, Law.prob_map, Law.prob_pure]

theorem bitLaw_succ (R : U → U → Prop) (x : U) (B ψ : ℕ) :
    bitLaw R x (B + 1) (ψ + 1) = (Law.uniform U).bind (fun y =>
      if y = x then Law.pure true
      else if R x y then bitLaw R x B ψ else bitLaw R x B (ψ + 1)) := by
  classical
  rw [bitLaw, law, LawOperations.map_bind]
  congr 1
  funext y
  by_cases hy : y = x
  · simp only [hy, ↓reduceIte]
    apply LawOperations.ext_prob
    intro E
    simp [Law.prob_map, Law.prob_pure]
  · by_cases hR : R x y <;> simp [hy, hR, bitLaw]

/-- The only discrepancy is finite-tape exhaustion; no assumed sampler law. -/
theorem bitLaw_close (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (x : U) (B ψ : ℕ) :
    Law.Close (bitLaw R x B ψ)
      (CategoricalCoupling.bernoulli (retentionRate R hrefl ψ x))
      ((1 - 1 / (Fintype.card U : ℝ)) ^ B) := by
  classical
  induction B generalizing ψ with
  | zero => simpa using Law.close_one (bitLaw R x 0 ψ) _
  | succ B ih =>
    cases ψ with
    | zero =>
      have he : retentionRate R hrefl 0 x = (⟨0, by norm_num⟩ : Rate) := by
        apply Subtype.ext
        simp [retentionRate]
      rw [bitLaw_zero, he, FiniteSampling.bernoulli_zero]
      exact (Law.close_refl _).mono (by
        apply pow_nonneg
        have hk : (1 : ℝ) ≤ Fintype.card U := by exact_mod_cast Fintype.card_pos
        have hkpos : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
        exact sub_nonneg.mpr ((div_le_one hkpos).mpr hk))
    | succ ψ =>
      rw [bitLaw_succ, ← harmonic R hrefl x ψ]
      have h := Law.Close.bind_same (Law.uniform U)
        (fun y => if y = x then Law.pure true
          else if R x y then bitLaw R x B ψ else bitLaw R x B (ψ + 1))
        (fun y => if y = x then Law.pure true
          else if R x y then CategoricalCoupling.bernoulli (retentionRate R hrefl ψ x)
          else CategoricalCoupling.bernoulli (retentionRate R hrefl (ψ + 1) x))
        (fun y => if y = x then 0 else (1 - 1 / (Fintype.card U : ℝ)) ^ B)
        (fun y => by
          by_cases hy : y = x
          · simpa only [hy, ↓reduceIte] using Law.close_refl (Law.pure true)
          · by_cases hR : R x y
            · simpa only [hy, hR, ↓reduceIte] using ih ψ
            · simpa only [hy, hR, ↓reduceIte] using ih (ψ + 1))
      rw [FiniteSampling.uniform_expect_ne] at h
      simpa only [pow_succ, mul_comm] using h

theorem bitLaw_close_exp (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (x : U) (B ψ : ℕ) :
    Law.Close (bitLaw R x B ψ)
      (CategoricalCoupling.bernoulli (retentionRate R hrefl ψ x))
      (Real.exp (-(B : ℝ) / Fintype.card U)) := by
  apply (bitLaw_close R hrefl x B ψ).mono
  have hk : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hk1 : (1 : ℝ) ≤ Fintype.card U := by exact_mod_cast Fintype.card_pos
  simpa only [div_eq_mul_inv, one_mul] using
    FiniteSampling.survival_exp (by positivity : 0 ≤ 1 / (Fintype.card U : ℝ))
      ((div_le_one hk).mpr hk1) B

end SteinerUpperBound.Covers.Factory
