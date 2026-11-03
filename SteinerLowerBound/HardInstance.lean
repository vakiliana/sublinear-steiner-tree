module

public import SteinerLowerBound.HardParameters
public import SteinerLowerBound.MetricComparison.AllSizes
public import SteinerLowerBound.DistributionalLowerBound

@[expose] public section

namespace SteinerLowerBound

open HardDistribution ParameterGrowth
open scoped Classical ENNReal
open MeasureTheory

universe u

structure HardInstance (η : ℝ) (s n : ℕ) where
  family : HardFamily.Family η s
  gamma : ℝ
  coefficient : ℝ
  index : ℕ
  conditions : family.Conditions gamma coefficient index
  below : points family.d s gamma index ≤ n
  above : n ≤ MetricComparison.AllSizes.ratio s * points family.d s gamma index

namespace HardInstance

open MetricComparison

variable {η : ℝ} {s n : ℕ}

abbrev Specials (M : HardInstance η s n) := Fin (special M.family.d s M.index)
abbrev Clusters (M : HardInstance η s n) := Fin (clusters s M.index)
abbrev Slots (M : HardInstance η s n) := Fin (clusterSize s M.gamma M.index)
abbrev Centers (M : HardInstance η s n) :=
  Fin (special M.family.d s M.index * clusterSize s M.gamma M.index)
abbrev Padding (M : HardInstance η s n) :=
  Fin (n - points M.family.d s M.gamma M.index)
abbrev AllCenters (M : HardInstance η s n) := M.Centers ⊕ M.Padding
abbrev Points (M : HardInstance η s n) :=
  Public.Points M.Specials M.Clusters M.Slots M.AllCenters
abbrev Queries (M : HardInstance η s n) := Sym2 M.Points
abbrev Input (M : HardInstance η s n) :=
  (M.Centers → State M.Specials M.family.d) ×
    Equiv.Perm (Screening.Terminal M.Specials M.Clusters M.Slots)

instance (M : HardInstance η s n) : Nonempty M.Clusters :=
  ⟨⟨0, by have := M.conditions.clusters_large; omega⟩⟩

instance (M : HardInstance η s n) : Nonempty M.Slots :=
  ⟨⟨0, by have := clusterSize_pos s M.gamma M.index M.conditions.radius_floor; omega⟩⟩

noncomputable abbrev setup (M : HardInstance η s n) : Setup M.Specials M.family.weights.Carrier :=
  M.family.setup (I := M.Slots)
    (by simpa only [Specials, Fintype.card_fin] using M.conditions.special_degree)
    (by simpa only [Slots, Fintype.card_fin] using
      (M.family.radius_properties M.conditions.radius_large).2.1)

noncomputable def ell (M : HardInstance η s n) : ℝ :=
  ParameterGeometry.tiny (clusters s M.index) (clusterSize s M.gamma M.index)

theorem ell_pos (M : HardInstance η s n) : 0 < M.ell :=
  ParameterGeometry.tiny_pos _ _
    (by have := M.conditions.clusters_large; omega)
    (clusterSize_pos s M.gamma M.index M.conditions.radius_floor)

theorem ell_le_one (M : HardInstance η s n) : M.ell ≤ 1 :=
  ParameterGeometry.tiny_le_one _ _
    (by have := M.conditions.clusters_large; omega)
    (clusterSize_pos s M.gamma M.index M.conditions.radius_floor)

noncomputable def baseNeighbors (M : HardInstance η s n) (ω : M.Input) :
    M.Centers → Finset M.Specials :=
  fun c => neighbors M.family.d (ω.1 c)

noncomputable def neighbors (M : HardInstance η s n) (ω : M.Input) :
    M.AllCenters → Finset M.Specials :=
  MetricComparison.Padding.extend (M.baseNeighbors ω)

noncomputable def distance (M : HardInstance η s n) (ω : M.Input) :
    M.Points → M.Points → ℝ :=
  Public.distance ω.2 M.ell (M.neighbors ω)

noncomputable def metric (M : HardInstance η s n) (ω : M.Input) : MetricSpace M.Points :=
  Public.metricSpace ω.2 M.ell_pos (M.ell_le_one.trans (by norm_num)) (M.neighbors ω)

theorem metric_dist (M : HardInstance η s n) (ω : M.Input) (x y : M.Points) :
    @dist _ (M.metric ω).toDist x y = M.distance ω x y := rfl

noncomputable def oracle (M : HardInstance η s n) (ω : M.Input) :
    M.Queries → Screening.Reply :=
  Public.staticAnswer ω.2 (M.neighbors ω)

noncomputable def realOracle (M : HardInstance η s n) (ω : M.Input) :
    M.Queries → ℝ :=
  fun q => Public.replyValue M.ell (M.oracle ω q)

theorem realOracle_distance (M : HardInstance η s n) (ω : M.Input) (x y : M.Points) :
    M.realOracle ω (Sym2.mk x y) = M.distance ω x y :=
  Public.staticAnswer_metric ω.2 (M.neighbors ω) M.ell x y

noncomputable def optimum (M : HardInstance η s n) (ω : M.Input) : ℝ :=
  Public.optimum ω.2 M.ell (M.neighbors ω)

theorem optimum_unpadded (M : HardInstance η s n) (ω : M.Input) :
    M.optimum ω = Public.optimum ω.2 M.ell (M.baseNeighbors ω) :=
  Public.public_optimum_padding ω.2 M.ell_pos (M.ell_le_one.trans (by norm_num))
    (M.baseNeighbors ω)

noncomputable def terminals (M : HardInstance η s n) : Finset M.Points :=
  Public.terminalLabels

def geometryFactor (M : HardInstance η s n) : ℕ :=
  AllSizes.ratio s * (2 * M.family.d + 1)

theorem point_count (M : HardInstance η s n) : Fintype.card M.Points = n :=
  AllSizes.padded_point_count M.family.d s M.gamma M.index n M.below

theorem terminal_count_lower (M : HardInstance η s n) :
    n ≤ M.geometryFactor * M.terminals.card := by
  have h := AllSizes.padded_terminal_linear_bound M.family.d s M.gamma M.index n M.above
  change n ≤ AllSizes.ratio s * (M.family.d + 1) * M.terminals.card at h
  have hd : M.family.d + 1 ≤ 2 * M.family.d + 1 := by omega
  have hf := Nat.mul_le_mul_left (AllSizes.ratio s) hd
  exact h.trans (by
    dsimp only [geometryFactor]
    exact Nat.mul_le_mul_right M.terminals.card hf)

theorem terminal_count_upper (M : HardInstance η s n) : M.terminals.card ≤ n := by
  exact (Finset.card_le_univ M.terminals).trans M.point_count.le

theorem distance_scale (M : HardInstance η s n) :
    1 / (n : ℝ) ^ 3 ≤ M.ell ∧
      M.ell ≤ (M.geometryFactor : ℝ) ^ 3 / (n : ℝ) ^ 3 := by
  have h := AllSizes.tiny_bounds M.family.d s M.gamma M.index n
    M.conditions.index_pos M.conditions.radius_floor M.below M.above
  exact ⟨h.2.2.1, h.2.2.2⟩

theorem distance_values (M : HardInstance η s n) (ω : M.Input) (x y : M.Points)
    (hxy : x ≠ y) :
    M.distance ω x y = M.ell ∨ M.distance ω x y = 1 ∨ M.distance ω x y = 2 := by
  exact Point.distance_values M.ell (fun c => (M.neighbors ω c : Set M.Specials))
    (Public.place ω.2 x) (Public.place ω.2 y)
    (fun h => hxy ((Public.placeEquiv ω.2).injective h))

def Geometry (M : HardInstance η s n) (D : ℕ) : Prop :=
  Fintype.card M.Points = n ∧ n ≤ D * M.terminals.card ∧ M.terminals.card ≤ n ∧
    0 < M.ell ∧ M.ell ≤ 1 ∧
    1 / (n : ℝ) ^ 3 ≤ M.ell ∧ M.ell ≤ (D : ℝ) ^ 3 / (n : ℝ) ^ 3 ∧
    (∀ ω, ∃ m : MetricSpace M.Points, ∀ x y,
      @dist _ m.toDist x y = M.realOracle ω (Sym2.mk x y)) ∧
    (∀ ω x y, x ≠ y →
      M.distance ω x y = M.ell ∨ M.distance ω x y = 1 ∨ M.distance ω x y = 2)

theorem geometry (M : HardInstance η s n) : M.Geometry M.geometryFactor :=
  ⟨M.point_count, M.terminal_count_lower, M.terminal_count_upper, M.ell_pos, M.ell_le_one,
    M.distance_scale.1, M.distance_scale.2,
    fun ω => ⟨M.metric ω, fun x y =>
      (M.metric_dist ω x y).trans (M.realOracle_distance ω x y).symm⟩,
    M.distance_values⟩

theorem size_pos (M : HardInstance η s n) : 0 < n := by
  have hnonempty : Nonempty M.Points :=
    ⟨.inl (.inr (Classical.choice (inferInstance : Nonempty M.Clusters),
      Classical.choice (inferInstance : Nonempty M.Slots)))⟩
  exact (Fintype.card_pos_iff.mpr hnonempty).trans_le M.point_count.le

noncomputable def queryBudget (M : HardInstance η s n) : ℕ :=
  queries s M.gamma M.coefficient M.index

theorem queryBudget_pos (M : HardInstance η s n) : 0 < M.queryBudget := by
  have h := (Exponents.floor_bounds M.conditions.query_floor).1
  have hq : (1 : ℝ) ≤ M.queryBudget := by
    change (1 : ℝ) ≤ ⌊M.coefficient * (clusters s M.index : ℝ) *
      (clusterSize s M.gamma M.index : ℝ) ^ 2⌋₊
    linarith [M.conditions.query_floor]
  exact_mod_cast hq

def HardExponent (M : HardInstance η s n) (κ b : ℝ) : Prop :=
  ∀ (Γ : Type u) [MeasurableSpace Γ] (coins : Measure Γ) [IsProbabilityMeasure coins]
    (algorithm : Γ → DecisionTree M.Queries ℝ ℝ),
    (∀ ω, Measurable (fun γ => (algorithm γ).queries (M.realOracle ω))) →
    (∀ ω, Measurable (fun γ => (algorithm γ).output (M.realOracle ω))) →
    (∀ ω, 2 / 3 ≤ coins.real {γ |
      GoodEstimate (2 - η) (M.optimum ω) ((algorithm γ).output (M.realOracle ω))}) →
    ∃ ω, ENNReal.ofReal (κ * (n : ℝ) ^ b) <
      ∫⁻ γ, ((algorithm γ).queries (M.realOracle ω) : ℝ≥0∞) ∂coins

abbrev Hard (M : HardInstance η s n) (κ : ℝ) : Prop :=
  HardExponent.{u} M κ (Exponents.lowerExponent s)

theorem hard_smaller_exponent (M : HardInstance η s n) (κ b : ℝ)
    (hκ : 0 ≤ κ) (hb : b ≤ Exponents.lowerExponent s) (h : Hard.{u} M κ) :
    HardExponent.{u} M κ b := by
  intro Γ _ coins _ algorithm hqueries hout hgood
  obtain ⟨ω, hω⟩ := h Γ coins algorithm hqueries hout hgood
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by have := M.size_pos; omega)
  have hp := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn hb) hκ
  exact ⟨ω, (ENNReal.ofReal_le_ofReal hp).trans_lt hω⟩

end HardInstance

end SteinerLowerBound
