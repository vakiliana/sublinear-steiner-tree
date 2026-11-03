module

public import SteinerLowerBound.LawOperations
public import SteinerLowerBound.FiniteVariation
public import SteinerLowerBound.IndependentTrials

@[expose] public section

namespace SteinerUpperBound.ReusableSample

open SteinerLowerBound
open scoped BigOperators Classical

/-- A finite binary experiment; `true` is the acceptance branch. -/
inductive Tree : ℕ → Type
  | leaf : Tree 0
  | node {n : ℕ} (p : Rate) (reject accept : Tree n) : Tree (n + 1)

namespace Tree

def prepend {n : ℕ} (b : Bool) (w : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.cons b w

noncomputable def law : {n : ℕ} → Tree n → Law (Fin n → Bool)
  | 0, .leaf => Law.pure Fin.elim0
  | _ + 1, .node p l r =>
      Law.mix (p : ℝ) p.property.1 p.property.2
        (r.law.map (prepend true)) (l.law.map (prepend false))

theorem prob_node {n : ℕ} (p : Rate) (l r : Tree n)
    (E : Set (Fin (n + 1) → Bool)) :
    (node p l r).law.prob E =
      (p : ℝ) * r.law.prob ((prepend true) ⁻¹' E) +
        (1 - (p : ℝ)) * l.law.prob ((prepend false) ⁻¹' E) := by
  simp only [law, Law.prob_mix, Law.prob_map]

/-- Addition of one live record. At a relevant acceptance the two continuations
coincide, because that record is deleted. Other decisions may remain adaptive. -/
inductive Addition (q : ℝ) : {n : ℕ} → Tree n → Tree n → Prop
  | same {n : ℕ} (s : Tree n) : Addition q s s
  | irrelevant {n : ℕ} (p : Rate) {l l' r r' : Tree n}
      (hl : Addition q l l') (hr : Addition q r r') :
      Addition q (.node p l r) (.node p l' r')
  | relevant {n : ℕ} (p p' : Rate) {l l' : Tree n} (r : Tree n)
      (hp : (p' : ℝ) = (1 + q) * (p : ℝ) / (1 + q * (p : ℝ)))
      (hl : Addition q l l') :
      Addition q (.node p l r) (.node p' l' r)

theorem Addition.forward {q : ℝ} (hq : 0 ≤ q) {n : ℕ} {s s' : Tree n}
    (h : Addition q s s') (E : Set (Fin n → Bool)) :
    s'.law.prob E ≤ (1 + q) * s.law.prob E := by
  induction h with
  | same s =>
      nlinarith [s.law.prob_nonneg E]
  | @irrelevant n p l l' r r' hl hr ihl ihr =>
      rw [prob_node, prob_node]
      have h₀ := mul_le_mul_of_nonneg_left (ihl ((prepend false) ⁻¹' E))
        (sub_nonneg.mpr p.property.2)
      have h₁ := mul_le_mul_of_nonneg_left (ihr ((prepend true) ⁻¹' E))
        p.property.1
      nlinarith
  | @relevant n p p' l l' r hp hl ih =>
      have hd : 0 < 1 + q * (p : ℝ) := by
        nlinarith [mul_nonneg hq p.property.1]
      have he := (eq_div_iff hd.ne').mp hp
      have hpp : (p : ℝ) ≤ (p' : ℝ) := by
        rw [hp, le_div_iff₀ hd]
        nlinarith [mul_nonneg (mul_nonneg hq p.property.1)
          (sub_nonneg.mpr p.property.2)]
      have hpu : (p' : ℝ) ≤ (1 + q) * (p : ℝ) := by
        nlinarith [mul_nonneg (mul_nonneg hq p.property.1) p'.property.1]
      rw [prob_node, prob_node]
      have h₀ := mul_le_mul_of_nonneg_left (ih ((prepend false) ⁻¹' E))
        (sub_nonneg.mpr p'.property.2)
      have h₁ := mul_le_mul_of_nonneg_right hpu
        (r.law.prob_nonneg ((prepend true) ⁻¹' E))
      have h₂ := mul_le_mul_of_nonneg_right (show 1 - (p' : ℝ) ≤ 1 - (p : ℝ) by linarith)
        (mul_nonneg (by linarith : 0 ≤ 1 + q)
          (l.law.prob_nonneg ((prepend false) ⁻¹' E)))
      nlinarith

private theorem survival_exp (p : ℝ) :
    (1 - p) * Real.exp p ≤ 1 := by
  have h := Real.add_one_le_exp (-p)
  have he : Real.exp (-p) * Real.exp p = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith [Real.exp_pos p]

/-- Finite survival bound, proved directly by induction rather than by an
assumed martingale theorem. The parameter `L` is the remaining hazard budget. -/
theorem Addition.reverse {q : ℝ} (hq : 0 < q) {n : ℕ} {s s' : Tree n}
    (h : Addition q s s') (L : ℝ) (hL : 0 ≤ L)
    (E : Set (Fin n → Bool)) :
    s.law.prob E ≤ Real.exp (q * L) * s'.law.prob E + Real.exp (-L) := by
  induction h generalizing L with
  | same s =>
      have he : 1 ≤ Real.exp (q * L) :=
        Real.one_le_exp_iff.mpr (mul_nonneg hq.le hL)
      nlinarith [s.law.prob_nonneg E, Real.exp_pos (-L)]
  | @irrelevant n p l l' r r' hl hr ihl ihr =>
      rw [prob_node, prob_node]
      have h₀ := mul_le_mul_of_nonneg_left
        (ihl L hL ((prepend false) ⁻¹' E)) (sub_nonneg.mpr p.property.2)
      have h₁ := mul_le_mul_of_nonneg_left
        (ihr L hL ((prepend true) ⁻¹' E)) p.property.1
      nlinarith
  | @relevant n p p' l l' r hp hl ih =>
      have hd : 0 < 1 + q * (p : ℝ) := by
        nlinarith [mul_nonneg hq.le p.property.1]
      have he := (eq_div_iff hd.ne').mp hp
      have hpp : (p : ℝ) ≤ (p' : ℝ) := by
        rw [hp, le_div_iff₀ hd]
        nlinarith [mul_nonneg (mul_nonneg hq.le p.property.1)
          (sub_nonneg.mpr p.property.2)]
      have hre : 1 - (p : ℝ) = (1 + q * (p : ℝ)) * (1 - (p' : ℝ)) := by
        nlinarith
      let a := Real.log (1 + q * (p : ℝ)) / q
      have ha : 0 ≤ a := div_nonneg
        (Real.log_nonneg (by nlinarith [mul_nonneg hq.le p.property.1])) hq.le
      have hap : a ≤ (p : ℝ) := by
        apply (div_le_iff₀ hq).mpr
        have hh := Real.log_le_sub_one_of_pos hd
        nlinarith
      have hex : Real.exp (q * a) = 1 + q * (p : ℝ) := by
        dsimp [a]
        rw [mul_div_cancel₀ _ hq.ne', Real.exp_log hd]
      have hsur : (1 - (p : ℝ)) * Real.exp a ≤ 1 :=
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hap)
          (sub_nonneg.mpr p.property.2)).trans (survival_exp _)
      have hacc : (p : ℝ) * r.law.prob ((prepend true) ⁻¹' E) ≤
          Real.exp (q * L) * (p' : ℝ) * r.law.prob ((prepend true) ⁻¹' E) := by
        have hx := Real.one_le_exp_iff.mpr (mul_nonneg hq.le hL)
        have hpp' : (p : ℝ) ≤ Real.exp (q * L) * (p' : ℝ) := by
          nlinarith [p'.property.1]
        exact mul_le_mul_of_nonneg_right hpp' (r.law.prob_nonneg _)
      rw [prob_node, prob_node]
      by_cases hb : a ≤ L
      · have hb' := ih (L - a) (sub_nonneg.mpr hb) ((prepend false) ⁻¹' E)
        have hmul := mul_le_mul_of_nonneg_left hb' (sub_nonneg.mpr p.property.2)
        have hc : (1 - (p : ℝ)) * Real.exp (q * (L - a)) =
            Real.exp (q * L) * (1 - (p' : ℝ)) := by
          rw [mul_sub, Real.exp_sub, div_eq_mul_inv, hre]
          rw [hex]
          field_simp
        have herr : (1 - (p : ℝ)) * Real.exp (-(L - a)) ≤ Real.exp (-L) := by
          rw [show -(L - a) = -L + a by ring, Real.exp_add]
          nlinarith [Real.exp_pos (-L)]
        rw [mul_add, ← mul_assoc, hc] at hmul
        nlinarith
      · have hsmall : 1 - (p : ℝ) ≤ Real.exp (-L) := by
          have hla : L ≤ (p : ℝ) := (le_of_not_ge hb).trans hap
          have hz := Real.add_one_le_exp (-L)
          linarith
        have hrej : (1 - (p : ℝ)) * l.law.prob ((prepend false) ⁻¹' E) ≤
            Real.exp (-L) := by
          calc
            _ ≤ (1 - (p : ℝ)) * 1 := mul_le_mul_of_nonneg_left
              (l.law.prob_le_one _) (sub_nonneg.mpr p.property.2)
            _ ≤ _ := by simpa using hsmall
        have hnn := mul_nonneg (Real.exp_pos (q * L)).le
          (mul_nonneg (sub_nonneg.mpr p'.property.2)
            (l'.law.prob_nonneg ((prepend false) ⁻¹' E)))
        nlinarith

end Tree

end SteinerUpperBound.ReusableSample
