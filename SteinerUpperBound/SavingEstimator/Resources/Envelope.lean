module

public import SteinerUpperBound.SavingEstimator.Resources.Clipped

@[expose] public section

namespace SteinerUpperBound.SavingEstimator.Resources

open SteinerLowerBound
open scoped Classical

variable {U C : Type*}

noncomputable def envelope (Inv : C → Prop) (f : U → C → ℝ) (u : U) : ℝ :=
  sSup {r | ∃ c, Inv c ∧ f u c = r}

theorem envelope_bound (Inv : C → Prop) (f : U → C → ℝ) (c₀ : C) (hc₀ : Inv c₀)
    (upper : ℝ) (hupper : ∀ u c, Inv c → f u c ≤ upper) (u : U) :
    BddAbove {r | ∃ c, Inv c ∧ f u c = r} :=
  ⟨upper, by rintro r ⟨c, hc, rfl⟩; exact hupper u c hc⟩

theorem le_envelope (Inv : C → Prop) (f : U → C → ℝ) (c₀ : C) (hc₀ : Inv c₀)
    (upper : ℝ) (hupper : ∀ u c, Inv c → f u c ≤ upper) (u : U) (c : C) (hc : Inv c) :
    f u c ≤ envelope Inv f u :=
  le_csSup (envelope_bound Inv f c₀ hc₀ upper hupper u) ⟨c, hc, rfl⟩

theorem envelope_nonneg (Inv : C → Prop) (f : U → C → ℝ) (c₀ : C) (hc₀ : Inv c₀)
    (upper : ℝ) (hupper : ∀ u c, Inv c → f u c ≤ upper)
    (hnonneg : ∀ u c, Inv c → 0 ≤ f u c) (u : U) :
    0 ≤ envelope Inv f u :=
  (hnonneg u c₀ hc₀).trans (le_envelope Inv f c₀ hc₀ upper hupper u c₀ hc₀)

theorem envelope_approx (Inv : C → Prop) (f : U → C → ℝ) (c₀ : C) (hc₀ : Inv c₀)
    (upper : ℝ) (hupper : ∀ u c, Inv c → f u c ≤ upper) (u : U)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c, Inv c ∧ envelope Inv f u ≤ f u c + ε := by
  have hne : ({r | ∃ c, Inv c ∧ f u c = r} : Set ℝ).Nonempty := ⟨f u c₀, c₀, hc₀, rfl⟩
  have hbd := envelope_bound Inv f c₀ hc₀ upper hupper u
  have hlt : envelope Inv f u - ε < sSup {r | ∃ c, Inv c ∧ f u c = r} := by
    change envelope Inv f u - ε < envelope Inv f u
    linarith
  obtain ⟨r, ⟨c, hc, rfl⟩, hr⟩ := (lt_csSup_iff hbd hne).mp hlt
  exact ⟨c, hc, by linarith⟩

theorem envelope_sum_le [Fintype U]
    (Inv : C → Prop) (f : U → C → ℝ) (c₀ : C) (hc₀ : Inv c₀)
    (upper budget : ℝ) (hupper : ∀ u c, Inv c → f u c ≤ upper)
    (hfamily : ∀ caches : U → C, (∀ u, Inv (caches u)) →
      (∑ u, f u (caches u)) ≤ budget) :
    (∑ u, envelope Inv f u) ≤ budget := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  let η : ℝ := ε / (Fintype.card U + 1)
  have hη : 0 < η := by dsimp only [η]; positivity
  choose caches hcaches happrox using
    fun u => envelope_approx Inv f c₀ hc₀ upper hupper u η hη
  have hh := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => happrox u)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  have herr : (Fintype.card U : ℝ) * η ≤ ε := by
    dsimp only [η]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  exact hh.trans (add_le_add (hfamily caches hcaches) herr)

/-- Uniform bounds for every cache selector control even the supremum cache
envelope.  Thus later adaptive cache states need not be independent of labels. -/
theorem envelope_expect_le [Fintype U] (μ : Law U)
    (Inv : C → Prop) (f : U → C → ℝ) (c₀ : C) (hc₀ : Inv c₀)
    (upper budget : ℝ) (hupper : ∀ u c, Inv c → f u c ≤ upper)
    (hfamily : ∀ caches : U → C, (∀ u, Inv (caches u)) →
      μ.expect (fun u => f u (caches u)) ≤ budget) :
    μ.expect (envelope Inv f) ≤ budget := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hchoose (u : U) : ∃ c, Inv c ∧ envelope Inv f u ≤ f u c + ε := by
    have hne : ({r | ∃ c, Inv c ∧ f u c = r} : Set ℝ).Nonempty := ⟨f u c₀, c₀, hc₀, rfl⟩
    have hbd := envelope_bound Inv f c₀ hc₀ upper hupper u
    have hlt : envelope Inv f u - ε < sSup {r | ∃ c, Inv c ∧ f u c = r} := by
      change envelope Inv f u - ε < envelope Inv f u
      linarith
    obtain ⟨r, ⟨c, hc, rfl⟩, hr⟩ := (lt_csSup_iff hbd hne).mp hlt
    exact ⟨c, hc, by linarith⟩
  choose caches hcaches happrox using hchoose
  have hh := μ.expect_mono happrox
  rw [Law.expect_add, Law.expect_const] at hh
  exact hh.trans (add_le_add (hfamily caches hcaches) (le_refl ε))

end SteinerUpperBound.SavingEstimator.Resources
