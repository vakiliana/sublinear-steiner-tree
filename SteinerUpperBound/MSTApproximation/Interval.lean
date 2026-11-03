module

public import SteinerUpperBound.MSTApproximation.Score
public import SteinerUpperBound.MSTApproximation.Mass

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry
open scoped Classical BigOperators

noncomputable def estimate (k : ℕ) (g : Grid) (gminus empirical : ℕ → ℝ) (xi : ℝ) : ℝ :=
  ((k - 1 : ℕ) : ℝ) * g.first +
    ∑ i ∈ Finset.range g.intervals, g.width i *
      max 0 (Estimation.lowerCount (gminus i) (empirical i) xi - 1)

noncomputable def lowerEndpoint (nu value : ℝ) : ℝ := value / (1 + nu / 10)
noncomputable def upperEndpoint (nu value : ℝ) : ℝ := value / (1 - nu / 10)

variable {V : Type*} [Fintype V]

theorem estimate_loss (I : Instance V) (g : Grid) (N : ℕ → Finset V) (B : ℕ)
    (gminus empirical : ℕ → ℝ) (xi : ℝ) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) (hq2 : g.q ≤ 2)
    (hN : ∀ i < g.intervals, (N i).Nonempty)
    (hcal : ∀ i < g.intervals, (1 - xi) * ((N i).card : ℝ) ≤ gminus i)
    (hcal1 : ∀ i < g.intervals, gminus i ≤ (N i).card)
    (he : ∀ i < g.intervals, |empirical i - scoreMean I (N i) (g.scale i) B| ≤ xi) :
    estimate I.terminals.card g gminus empirical xi ≤ coverSum I g N ∧
      coverSum I g N - estimate I.terminals.card g gminus empirical xi ≤
        (1 / ((B : ℝ) + 1) + 3 * xi) * weightedMass g N := by
  have hcounts (i : ℕ) (hi : i < g.intervals) :=
    lowerCount_component_bounds I (N i) (g.scale i) B (hN i hi) (gminus i) (empirical i) xi
      hxi hxi1 (hcal i hi) (hcal1 i hi) (he i hi)
  have hclip (i : ℕ) (hi : i < g.intervals) :
      max 0 (Estimation.lowerCount (gminus i) (empirical i) xi - 1) ≤
        (componentCount I (N i) (g.scale i) : ℝ) - 1 := by
    have hsmall : (smallComponents I (N i) (g.scale i) B).card ≤
        componentCount I (N i) (g.scale i) := Finset.card_le_card (Finset.filter_subset _ _)
    have hsmallR : ((smallComponents I (N i) (g.scale i) B).card : ℝ) ≤
        componentCount I (N i) (g.scale i) := by exact_mod_cast hsmall
    have hk : (1 : ℝ) ≤ componentCount I (N i) (g.scale i) := by
      exact_mod_cast componentCount_pos I (N i) (g.scale i) (hN i hi)
    exact max_le (by linarith) (sub_le_sub_right ((hcounts i hi).2.1.trans hsmallR) 1)
  constructor
  · unfold estimate coverSum
    apply add_le_add le_rfl
    exact Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (hclip i (Finset.mem_range.mp hi)) (g.width_nonneg i))
  · have hdiff : coverSum I g N - estimate I.terminals.card g gminus empirical xi =
        ∑ i ∈ Finset.range g.intervals, g.width i *
          (((componentCount I (N i) (g.scale i) : ℝ) - 1) -
            max 0 (Estimation.lowerCount (gminus i) (empirical i) xi - 1)) := by
      unfold coverSum estimate
      simp only [mul_sub, Finset.sum_sub_distrib, mul_one]
      ring
    rw [hdiff]
    unfold weightedMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hil := Finset.mem_range.mp hi
    have hgap := (hcounts i hil).2.2
    have hmax := le_max_right (0 : ℝ) (Estimation.lowerCount (gminus i) (empirical i) xi - 1)
    have hw : g.width i ≤ g.scale i := by
      rw [g.width_eq]
      nlinarith [g.scale_pos i]
    have hgap0 : 0 ≤ ((N i).card : ℝ) / (B + 1) + 3 * xi * (N i).card := by positivity
    calc
      _ ≤ g.width i * (((componentCount I (N i) (g.scale i) : ℝ)) -
          Estimation.lowerCount (gminus i) (empirical i) xi) :=
        mul_le_mul_of_nonneg_left (by linarith) (g.width_nonneg i)
      _ ≤ g.width i * (((N i).card : ℝ) / (B + 1) + 3 * xi * (N i).card) :=
        mul_le_mul_of_nonneg_left hgap (g.width_nonneg i)
      _ ≤ g.scale i * (((N i).card : ℝ) / (B + 1) + 3 * xi * (N i).card) :=
        mul_le_mul_of_nonneg_right hw hgap0
      _ = _ := by ring

theorem coefficient_budget (A nu xi : ℝ) (B : ℕ)
    (hA : 0 < A) (hn : 0 < nu) (hxi : 0 ≤ xi) (hxiA : xi ≤ nu / (100 * A))
    (hB : 100 * A / nu ≤ (B : ℝ)) :
    0 ≤ 1 / ((B : ℝ) + 1) + 3 * xi ∧
      (1 / ((B : ℝ) + 1) + 3 * xi) * A ≤ nu / 10 := by
  have hBn := (div_le_iff₀ hn).mp hB
  have hrec : 1 / ((B : ℝ) + 1) ≤ nu / (100 * A) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < B + 1)
      (by positivity : 0 < 100 * A)).mpr
    nlinarith
  have hcancel : (nu / (100 * A)) * A = nu / 100 := by field_simp
  have hr := mul_le_mul_of_nonneg_right hrec hA.le
  have hx := mul_le_mul_of_nonneg_right hxiA hA.le
  rw [hcancel] at hr hx
  exact ⟨by positivity, by nlinarith⟩

theorem estimate_bounds (I : Instance V) (g : Grid) (N : ℕ → Finset V)
    (nu A xi : ℝ) (B : ℕ) (gminus empirical : ℕ → ℝ)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hA : 1 ≤ A) (hxi : 0 ≤ xi)
    (hxiA : xi ≤ nu / (100 * A)) (hB : 100 * A / nu ≤ (B : ℝ))
    (hq : g.q = fineRatio nu) (hT : I.terminals.Nonempty)
    (hN : ∀ i < g.intervals, N i ⊆ I.terminals)
    (hcover : ∀ i < g.intervals, CoverOn I I.terminals (N i) (fineDelta nu * g.scale i))
    (hfirst : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, x ≠ y → g.first ≤ I.distance x y)
    (hlast : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, I.distance x y ≤ g.scale g.intervals)
    (hmass : weightedMass g N ≤ A * I.mst)
    (hcal : ∀ i < g.intervals, (1 - xi) * ((N i).card : ℝ) ≤ gminus i)
    (hcal1 : ∀ i < g.intervals, gminus i ≤ (N i).card)
    (he : ∀ i < g.intervals, |empirical i - scoreMean I (N i) (g.scale i) B| ≤ xi) :
    (1 - nu / 10) * I.mst ≤ estimate I.terminals.card g gminus empirical xi ∧
      estimate I.terminals.card g gminus empirical xi ≤ (1 + nu / 10) * I.mst := by
  have hdelta : 0 ≤ fineDelta nu := by unfold fineDelta; positivity
  have hdhalf : fineDelta nu < 1 / 2 := by unfold fineDelta; linarith
  have hxi1 : xi ≤ 1 :=
    hxiA.trans ((div_le_one (show 0 < 100 * A by linarith)).mpr (by linarith))
  have hq2 : g.q ≤ 2 := by rw [hq]; unfold fineRatio; linarith
  have hn : ∀ i < g.intervals, (N i).Nonempty :=
    fun i hi => cover_nonempty I I.terminals (N i) _ (hcover i hi) hT
  have hquad := coverSum_bounds I g N (fineDelta nu) hT hdelta hdhalf hN hcover hfirst hlast
  have hscore := estimate_loss I g N B gminus empirical xi hxi hxi1 hq2 hn hcal hcal1 he
  obtain ⟨hc0, hcb⟩ := coefficient_budget A nu xi B (by linarith) hnu hxi hxiA hB
  have hmass' := mul_le_mul_of_nonneg_left hmass hc0
  have hbudget := mul_le_mul_of_nonneg_right hcb I.mst_nonneg
  have hfactor := fine_factor nu hnu hnu1
  rw [← hq] at hfactor
  have hu := mul_le_mul_of_nonneg_right hfactor I.mst_nonneg
  constructor <;> nlinarith

theorem endpoints_of_estimate (L value nu : ℝ) (hL : 0 ≤ L)
    (hn : 0 < nu) (hn1 : nu ≤ 1)
    (hlo : (1 - nu / 10) * L ≤ value) (hhi : value ≤ (1 + nu / 10) * L) :
    L / (1 + nu) ≤ lowerEndpoint nu value ∧ lowerEndpoint nu value ≤ L ∧
      L ≤ upperEndpoint nu value ∧ upperEndpoint nu value ≤ (1 + nu) * L := by
  have hdplus : 0 < 1 + nu / 10 := by linarith
  have hdminus : 0 < 1 - nu / 10 := by linarith
  have hdfull : 0 < 1 + nu := by linarith
  have hc : 1 + nu / 10 ≤ (1 - nu / 10) * (1 + nu) := by nlinarith
  have hcm := mul_le_mul_of_nonneg_right hc hL
  unfold lowerEndpoint upperEndpoint
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (div_le_div_iff₀ hdfull hdplus).mpr
    have hm := mul_le_mul_of_nonneg_right hlo hdfull.le
    nlinarith
  · exact (div_le_iff₀ hdplus).mpr (by nlinarith)
  · exact (le_div_iff₀ hdminus).mpr (by nlinarith)
  · apply (div_le_iff₀ hdminus).mpr
    nlinarith

theorem interval_correct (I : Instance V) (g : Grid) (N : ℕ → Finset V)
    (nu A xi : ℝ) (B : ℕ) (gminus empirical : ℕ → ℝ)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hA : 1 ≤ A) (hxi : 0 ≤ xi)
    (hxiA : xi ≤ nu / (100 * A)) (hB : 100 * A / nu ≤ (B : ℝ))
    (hq : g.q = fineRatio nu) (hT : I.terminals.Nonempty)
    (hN : ∀ i < g.intervals, N i ⊆ I.terminals)
    (hcover : ∀ i < g.intervals, CoverOn I I.terminals (N i) (fineDelta nu * g.scale i))
    (hfirst : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, x ≠ y → g.first ≤ I.distance x y)
    (hlast : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, I.distance x y ≤ g.scale g.intervals)
    (hmass : weightedMass g N ≤ A * I.mst)
    (hcal : ∀ i < g.intervals, (1 - xi) * ((N i).card : ℝ) ≤ gminus i)
    (hcal1 : ∀ i < g.intervals, gminus i ≤ (N i).card)
    (he : ∀ i < g.intervals, |empirical i - scoreMean I (N i) (g.scale i) B| ≤ xi) :
    let value := estimate I.terminals.card g gminus empirical xi
    I.mst / (1 + nu) ≤ lowerEndpoint nu value ∧ lowerEndpoint nu value ≤ I.mst ∧
      I.mst ≤ upperEndpoint nu value ∧ upperEndpoint nu value ≤ (1 + nu) * I.mst := by
  obtain ⟨hlo, hhi⟩ := estimate_bounds I g N nu A xi B gminus empirical hnu hnu1 hA hxi
    hxiA hB hq hT hN hcover hfirst hlast hmass hcal hcal1 he
  exact endpoints_of_estimate I.mst _ nu I.mst_nonneg hnu hnu1 hlo hhi

theorem interval_correct_of_factory_sizes (I : Instance V) (g : Grid) (N : ℕ → Finset V)
    (nu xi R slack : ℝ) (B psi hop budget : ℕ) (gminus empirical : ℕ → ℝ)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hxi : 0 ≤ xi) (hslack : 0 ≤ slack)
    (hq : g.q = fineRatio nu) (hT : I.terminals.Nonempty)
    (hn : g.intervals ≤ budget) (hR : 0 ≤ R) (hRL : R ≤ I.mst)
    (hcap : g.scale g.intervals ≤ 4 * g.q * R)
    (hN : ∀ i < g.intervals, N i ⊆ I.terminals)
    (hcover : ∀ i < g.intervals, CoverOn I I.terminals (N i) (fineDelta nu * g.scale i))
    (hsize : ∀ i < g.intervals, ((N i).card : ℝ) ≤
      Real.exp 1 * (1 + (psi : ℝ) *
        (1 + 2 * hop * I.mst / (fineDelta nu * g.scale i))) + slack)
    (hfirst : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, x ≠ y → g.first ≤ I.distance x y)
    (hlast : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, I.distance x y ≤ g.scale g.intervals)
    (hxiA : xi ≤ nu / (100 *
      massAllowance g (fineDelta nu) (3 * (1 + (psi : ℝ)) + slack) psi hop budget))
    (hB : 100 * massAllowance g (fineDelta nu) (3 * (1 + (psi : ℝ)) + slack) psi hop budget / nu ≤
      (B : ℝ))
    (hcal : ∀ i < g.intervals, (1 - xi) * ((N i).card : ℝ) ≤ gminus i)
    (hcal1 : ∀ i < g.intervals, gminus i ≤ (N i).card)
    (he : ∀ i < g.intervals, |empirical i - scoreMean I (N i) (g.scale i) B| ≤ xi) :
    let value := estimate I.terminals.card g gminus empirical xi
    I.mst / (1 + nu) ≤ lowerEndpoint nu value ∧ lowerEndpoint nu value ≤ I.mst ∧
      I.mst ≤ upperEndpoint nu value ∧ upperEndpoint nu value ≤ (1 + nu) * I.mst := by
  have hd : 0 < fineDelta nu := by unfold fineDelta; positivity
  have hH : (1 : ℝ) ≤ 3 * (1 + (psi : ℝ)) + slack := by
    nlinarith [show (0 : ℝ) ≤ psi from Nat.cast_nonneg psi]
  have hmass := weightedMass_bound I g N (fineDelta nu) (3 * (1 + (psi : ℝ)) + slack)
    psi hop R budget hd (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hR hRL hn hcap (fun i hi => factory_size_bound I _ _ slack psi hop
      (mul_pos hd (g.scale_pos i)) (hsize i hi))
  exact interval_correct I g N nu _ xi B gminus empirical hnu hnu1
    (massAllowance_ge_one g _ _ _ _ _ hd hH (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    hxi hxiA hB hq hT hN hcover hfirst hlast hmass hcal hcal1 he

end SteinerUpperBound.MSTApproximation
