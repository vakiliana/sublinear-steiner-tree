module

public import SteinerUpperBound.LabelledMetricWorld
public import SteinerUpperBound.EstimatorParameters.CoverFamily

@[expose] public section

noncomputable section

namespace SteinerUpperBound.LabelledCovers

open SteinerLowerBound Covers QueryProgram LabelledMetricWorld
open scoped Classical

variable {n k s : ℕ}

noncomputable local instance : DecidableEq (Fin n) := Classical.decEq _
noncomputable local instance : DecidableEq (Fin (k + 1)) := Classical.decEq _
noncomputable local instance : DecidableEq (Fin (s + 1)) := Classical.decEq _
noncomputable local instance : DecidableEq (LabelledFactory.Coordinate s k) := Classical.decEq _
noncomputable local instance (I : Instance (Fin n)) : DecidableEq (Terminal I) := Classical.decEq _

def GoodRow (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1)) (rho : ℝ)
    (b : Fin (k + 1) → Bool) : Prop :=
  Geometry.CoverOn I I.terminals (retainedLabels label b) rho ∧
    ((retainedLabels label b).card : ℝ) ≤
      Real.exp 1 * (1 + (EstimatorParameters.coverTrials n : ℝ) *
        (1 + 2 * hopCount I.terminals.card * I.mst / rho)) + EstimatorParameters.coverSlack n

def Good (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (rho : Vector ℝ (s + 1)) (b : LabelledFactory.Coordinate s k → Bool) : Prop :=
  ∀ i, GoodRow I label (rho.get i) (fun j => b (i, j))

theorem terminal_card (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals) :
    I.terminals.card = k + 1 := by
  rw [← hT, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

theorem projected_goodRow (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (rho : ℝ) (b : Terminal I → Bool) (hg : ¬ EstimatorParameters.CoverBad I n rho b) :
    GoodRow I label rho (fun j => b (terminalEquiv I label hinj hT j)) := by
  have hc : IsCover I rho b := by
    unfold EstimatorParameters.CoverBad at hg
    tauto
  have hs : ((CategoricalCoupling.selected b).card : ℝ) ≤
      Real.exp 1 * (1 + (EstimatorParameters.coverTrials n : ℝ) *
        (1 + 2 * hopCount I.terminals.card * I.mst / rho)) + EstimatorParameters.coverSlack n := by
    unfold EstimatorParameters.CoverBad at hg
    exact le_of_lt (lt_of_not_ge (by tauto))
  constructor
  · exact coverOn_relabel I label hinj hT rho b hc
  · change ((retainedLabels label (FactoryEquivariance.masks
        (terminalEquiv I label hinj hT) b)).card : ℝ) ≤ _
    rw [retainedLabels_card I label hinj hT b]
    exact hs

theorem goodRow_size (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (rho : ℝ) (hr : 0 < rho) (b : Fin (k + 1) → Bool) (hg : GoodRow I label rho b) :
    ((retainedLabels label b).card : ℝ) ≤
      EstimatorParameters.Hc n + 6 * EstimatorParameters.coverTrials n *
        EstimatorParameters.hopBudget n * I.mst / rho := by
  have hl := MSTApproximation.factory_size_bound I _ rho (EstimatorParameters.coverSlack n)
    (EstimatorParameters.coverTrials n) (hopCount I.terminals.card) hr hg.2
  have hh : (hopCount I.terminals.card : ℝ) ≤ EstimatorParameters.hopBudget n := by
    exact_mod_cast EstimatorParameters.hopBudget_bounds n I.terminals.card
      (by simpa only [Fintype.card_fin] using Finset.card_le_univ I.terminals)
  have hm := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ 6 * (EstimatorParameters.coverTrials n : ℝ) * I.mst / rho by positivity [I.mst_nonneg])
  have he : (EstimatorParameters.Hc n : ℝ) =
      3 * (1 + (EstimatorParameters.coverTrials n : ℝ)) + EstimatorParameters.coverSlack n := by
    unfold EstimatorParameters.Hc
    push_cast
    ring
  rw [he]
  apply hl.trans
  apply add_le_add le_rfl
  convert hm using 1 <;> ring

theorem factory_failure (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (rho radii : Vector ℝ (s + 1)) (hr : ∀ i, 0 < rho.get i)
    (hcount : s + 1 ≤ EstimatorParameters.heightBudget n)
    (hradii : ∀ i, radii.get i = rho.get i / hopCount (k + 1)) (root : Fin (k + 1)) :
    (OracleProgram.bits
      (LabelledFactory.config label radii (EstimatorParameters.privateCap n (k + 1))
        (EstimatorParameters.coverTrials n)) I.weight
      (LabelledFactory.initialCache root)).prob {b | ¬ Good I label rho b} ≤ 1 / 4000000 := by
  let e := terminalEquiv I label hinj hT
  have hcard := terminal_card I label hinj hT
  have hkn : I.terminals.card ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ I.terminals
  rw [factory_bits_actual_rows I label hinj hT radii root]
  simp_rw [hradii, ← hcard]
  rw [Law.prob_map]
  apply (Law.prob_mono _ ?_).trans
    (EstimatorParameters.simultaneous_cover_failure I n hkn rho.get hr (e root)
      (by simpa only [Fintype.card_fin] using hcount))
  intro b hb
  by_contra hn
  apply hb
  intro i
  exact projected_goodRow I label hinj hT (rho.get i) (b i) (by
    intro hi
    exact hn ⟨i, hi⟩)

theorem cache_correct_on_support (label : Vector (Fin n) (k + 1)) (radii : Vector ℝ (s + 1))
    (cap trials : ℕ) (root : Fin (k + 1)) (w : Sym2 (Fin n) → ℝ)
    (bits : LabelledFactory.Coordinate s k → Bool)
    (hb : 0 < (OracleProgram.bits (LabelledFactory.config label radii cap trials) w
      (LabelledFactory.initialCache root)).mass bits) :
    Cache.Correct bits (LabelledFactory.initialCache root) :=
  Factory.cachedKernel_consistent _ _ bits hb

theorem root_on_support (label : Vector (Fin n) (k + 1)) (radii : Vector ℝ (s + 1))
    (cap trials : ℕ) (root : Fin (k + 1)) (w : Sym2 (Fin n) → ℝ)
    (bits : LabelledFactory.Coordinate s k → Bool)
    (hb : 0 < (OracleProgram.bits (LabelledFactory.config label radii cap trials) w
      (LabelledFactory.initialCache root)).mass bits) (i : Fin (s + 1)) :
    bits (i, root) = true :=
  cache_correct_on_support label radii cap trials root w bits hb (i, root) true
    (LabelledFactory.root_cached root i)

end SteinerUpperBound.LabelledCovers
