module

public import SteinerLowerBound.MetricComparison.PublicOptimum
public import SteinerLowerBound.ParameterGeometry

@[expose] public section

/-!
# From the floored construction sequence to every sufficiently large size

The actual sequence uses `floor (gamma * t^(s+2))`. Its adjacent size ratio
is at most `2^(2*s+6)`. A maximum of an explicitly finite set selects an
admissible construction size below any large requested size. Publicly named
far centers then give exactly the requested point count, preserving the
optimum and permitting query-efficient simulation as proved in `Padding`.
-/

namespace SteinerLowerBound.MetricComparison.AllSizes

open scoped BigOperators Classical
open ParameterGrowth

def ratio (s : ℕ) : ℕ := 2 ^ (2 * s + 6)

theorem ratio_pos (s : ℕ) : 0 < ratio s := by unfold ratio; positivity

theorem ratio_ge_one (s : ℕ) : 1 ≤ ratio s := ratio_pos s

theorem clusters_mono (s : ℕ) : Monotone (clusters s) :=
  fun _ _ ht => Nat.pow_le_pow_left ht _

theorem clusterSize_mono (s : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    Monotone (clusterSize s γ) := by
  intro t u htu
  apply Nat.floor_mono
  apply mul_le_mul_of_nonneg_left _ hγ
  exact pow_le_pow_left₀ (Nat.cast_nonneg t) (by exact_mod_cast htu) _

theorem points_mono (d s : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    Monotone (points d s γ) := by
  intro t u htu
  have hA := clusters_mono s htu
  have hR := clusterSize_mono s γ hγ htu
  exact Nat.add_le_add (Nat.mul_le_mul_left (d + 1) (Nat.mul_le_mul hA hR))
    (Nat.mul_le_mul_left d hA)

theorem points_ge_index (d s : ℕ) (γ : ℝ) (hd : 1 ≤ d) (t : ℕ) (ht : 1 ≤ t) :
    t ≤ points d s γ t := by
  have hh := ParameterGeometry.special_ge_t d s t hd ht
  unfold points
  omega

theorem points_unbounded (d s : ℕ) (γ : ℝ) (hd : 1 ≤ d) (t₀ N : ℕ) :
    ∃ t : ℕ, t₀ ≤ t ∧ N < points d s γ t := by
  let t := max (max t₀ (N + 1)) 1
  have ht₀ : t₀ ≤ t := (le_max_left t₀ (N + 1)).trans (le_max_left _ _)
  have htN : N + 1 ≤ t := (le_max_right t₀ (N + 1)).trans (le_max_left _ _)
  have ht : 1 ≤ t := le_max_right _ _
  exact ⟨t, ht₀, lt_of_lt_of_le (by omega) (points_ge_index d s γ hd t ht)⟩

theorem clusters_adjacent (s t : ℕ) (ht : 1 ≤ t) :
    clusters s (t + 1) ≤ 2 ^ (s + 3) * clusters s t := by
  calc
    _ ≤ (2 * t) ^ (s + 3) := Nat.pow_le_pow_left (by omega) _
    _ = _ := by simp only [clusters, mul_pow]

theorem radius_adjacent (s : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (t : ℕ) (ht : 1 ≤ t)
    (hR : 2 ≤ γ * (t : ℝ) ^ (s + 2)) :
    clusterSize s γ (t + 1) ≤ 2 ^ (s + 3) * clusterSize s γ t := by
  have ht' : (t + 1 : ℝ) ≤ 2 * t := by exact_mod_cast (show t + 1 ≤ 2 * t by omega)
  have hu : (clusterSize s γ (t + 1) : ℝ) ≤ γ * ((t + 1 : ℕ) : ℝ) ^ (s + 2) :=
    Nat.floor_le (by positivity)
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity : 0 ≤ (t + 1 : ℝ)) ht' (s + 2)) hγ
  have hl := mul_le_mul_of_nonneg_left (clusterSize_bounds s γ t hR).1
    (show (0 : ℝ) ≤ 2 ^ (s + 3) by positivity)
  have he : (2 : ℝ) ^ (s + 3) * ((γ / 2) * (t : ℝ) ^ (s + 2)) =
      γ * (2 * (t : ℝ)) ^ (s + 2) := by
    rw [show s + 3 = (s + 2) + 1 by omega, pow_succ, mul_pow]
    ring
  rw [he] at hl
  have hh : (clusterSize s γ (t + 1) : ℝ) ≤
      ((2 ^ (s + 3) : ℕ) : ℝ) * clusterSize s γ t := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    apply hu.trans
    simpa only [Nat.cast_add, Nat.cast_one] using hp.trans hl
  exact_mod_cast hh

theorem adjacent_ratio (d s : ℕ) (γ : ℝ) (hγ : 0 ≤ γ)
    (t : ℕ) (ht : 1 ≤ t) (hR : 2 ≤ γ * (t : ℝ) ^ (s + 2)) :
    points d s γ (t + 1) ≤ ratio s * points d s γ t := by
  let F := 2 ^ (s + 3)
  have hF : 1 ≤ F := by
    have hh : 0 < F := by dsimp only [F]; positivity
    omega
  have hFF : F * F = ratio s := by
    dsimp only [F, ratio]
    rw [← pow_add]
    congr 1
    omega
  have hFL : F ≤ ratio s := by nlinarith
  have hA := clusters_adjacent s t ht
  have hR' := radius_adjacent s γ hγ t ht hR
  have hK : ordinary s γ (t + 1) ≤ ratio s * ordinary s γ t := by
    have hh := Nat.mul_le_mul hA hR'
    change ordinary s γ (t + 1) ≤ _
    calc
      _ ≤ (F * clusters s t) * (F * clusterSize s γ t) := hh
      _ = _ := by rw [← hFF]; unfold ordinary; ring
  have hm : special d s (t + 1) ≤ ratio s * special d s t := by
    calc
      _ ≤ d * (F * clusters s t) := Nat.mul_le_mul_left d hA
      _ = F * special d s t := by unfold special; ring
      _ ≤ _ := Nat.mul_le_mul_right _ hFL
  calc
    _ ≤ (d + 1) * (ratio s * ordinary s γ t) + ratio s * special d s t :=
      Nat.add_le_add (Nat.mul_le_mul_left (d + 1) hK) hm
    _ = _ := by unfold points; ring

theorem padding_index (d s : ℕ) (γ : ℝ) (hd : 1 ≤ d) (hγ : 0 < γ)
    (t₀ : ℕ) (ht₀ : 1 ≤ t₀)
    (hfloor : ∀ t : ℕ, t₀ ≤ t → 2 ≤ γ * (t : ℝ) ^ (s + 2))
    (n : ℕ) (hn : points d s γ t₀ ≤ n) :
    ∃ t : ℕ, t₀ ≤ t ∧ points d s γ t ≤ n ∧ n ≤ ratio s * points d s γ t := by
  classical
  let J := (Finset.range (n + 1)).filter (fun t => t₀ ≤ t ∧ points d s γ t ≤ n)
  have htn : t₀ ≤ n := (points_ge_index d s γ hd t₀ ht₀).trans hn
  have hJ : J.Nonempty := by
    refine ⟨t₀, ?_⟩
    simp only [J, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, le_rfl, hn⟩
  let t := J.max' hJ
  have hmem : t ∈ J := Finset.max'_mem J hJ
  obtain ⟨_, ht, hnt⟩ := Finset.mem_filter.mp hmem
  have hnext : n < points d s γ (t + 1) := by
    by_contra hh
    have hbound : points d s γ (t + 1) ≤ n := by omega
    have hti : t + 1 ≤ n := (points_ge_index d s γ hd (t + 1) (by omega)).trans hbound
    have hmember : t + 1 ∈ J := by
      simp only [J, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, hbound⟩
    have hmax := Finset.le_max' J (t + 1) hmember
    change t + 1 ≤ t at hmax
    omega
  exact ⟨t, ht, hnt, hnext.le.trans
    (adjacent_ratio d s γ hγ.le t (ht₀.trans ht) (hfloor t ht))⟩

theorem queries_pos (s : ℕ) (γ c : ℝ) (t : ℕ)
    (hq : 2 ≤ c * (clusters s t : ℝ) * (clusterSize s γ t : ℝ) ^ 2) :
    1 ≤ queries s γ c t := by
  have hh := (Exponents.floor_bounds hq).1
  have h : (1 : ℝ) ≤ queries s γ c t := by
    change 1 ≤ (⌊c * (clusters s t : ℝ) * (clusterSize s γ t : ℝ) ^ 2⌋₊ : ℝ)
    linarith
  exact_mod_cast h

theorem query_scale_padding (d s : ℕ) (γ c : ℝ) (hγ : 0 < γ) (hc : 0 < c) :
    ∃ k : ℝ, 0 < k ∧ ∀ n t : ℕ,
      n ≤ ratio s * points d s γ t →
      2 ≤ γ * (t : ℝ) ^ (s + 2) →
      2 ≤ c * (clusters s t : ℝ) * (clusterSize s γ t : ℝ) ^ 2 →
      k * (n : ℝ) ^ Exponents.lowerExponent s ≤ (queries s γ c t : ℝ) / 10 := by
  obtain ⟨k, hk, hscale⟩ := query_exponent_scale d s γ c hγ hc
  have hL : (0 : ℝ) < ratio s := by exact_mod_cast ratio_pos s
  have hLp : 0 < (ratio s : ℝ) ^ Exponents.lowerExponent s := Real.rpow_pos_of_pos hL _
  have hb : 0 ≤ Exponents.lowerExponent s := by unfold Exponents.lowerExponent; positivity
  let k' := k / (ratio s : ℝ) ^ Exponents.lowerExponent s
  have hk' : 0 < k' := div_pos hk hLp
  refine ⟨k', hk', ?_⟩
  intro n t hn hR hq
  have hn' : (n : ℝ) ≤ (ratio s : ℝ) * points d s γ t := by exact_mod_cast hn
  have hnp := Real.rpow_le_rpow (Nat.cast_nonneg n) hn' hb
  rw [Real.mul_rpow hL.le (Nat.cast_nonneg _)] at hnp
  have hh := mul_le_mul_of_nonneg_left hnp hk'.le
  have he : k' * ((ratio s : ℝ) ^ Exponents.lowerExponent s *
      (points d s γ t : ℝ) ^ Exponents.lowerExponent s) =
        k * (points d s γ t : ℝ) ^ Exponents.lowerExponent s := by
    dsimp only [k']
    field_simp [hLp.ne']
  rw [he] at hh
  exact hh.trans (hscale t hR hq)

theorem all_sizes_scale (d s : ℕ) (γ c : ℝ) (hd : 1 ≤ d) (hγ : 0 < γ) (hc : 0 < c)
    (t₀ : ℕ) (ht₀ : 1 ≤ t₀)
    (hfloor : ∀ t : ℕ, t₀ ≤ t →
      2 ≤ γ * (t : ℝ) ^ (s + 2) ∧
      2 ≤ c * (clusters s t : ℝ) * (clusterSize s γ t : ℝ) ^ 2) :
    ∃ k : ℝ, 0 < k ∧ ∀ n : ℕ, points d s γ t₀ ≤ n →
      ∃ t : ℕ, t₀ ≤ t ∧ points d s γ t ≤ n ∧
        n ≤ ratio s * points d s γ t ∧ 1 ≤ queries s γ c t ∧
        k * (n : ℝ) ^ Exponents.lowerExponent s ≤ (queries s γ c t : ℝ) / 10 := by
  obtain ⟨k, hk, hscale⟩ := query_scale_padding d s γ c hγ hc
  refine ⟨k, hk, ?_⟩
  intro n hn
  obtain ⟨t, ht, htn, hnt⟩ := padding_index d s γ hd hγ t₀ ht₀
    (fun t ht => (hfloor t ht).1) n hn
  obtain ⟨hR, hq⟩ := hfloor t ht
  exact ⟨t, ht, htn, hnt, queries_pos s γ c t hq, hscale n t hnt hR hq⟩

theorem eventual_all_sizes (d s : ℕ) (γ c : ℝ) (hd : 1 ≤ d)
    (hγ : 0 < γ) (hc : 0 < c) (tmin : ℕ) :
    ∃ k : ℝ, 0 < k ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ t : ℕ, tmin ≤ t ∧ 1 ≤ t ∧
        2 ≤ γ * (t : ℝ) ^ (s + 2) ∧
        2 ≤ c * (clusters s t : ℝ) * (clusterSize s γ t : ℝ) ^ 2 ∧
        points d s γ t ≤ n ∧ n ≤ ratio s * points d s γ t ∧
        1 ≤ queries s γ c t ∧
        k * (n : ℝ) ^ Exponents.lowerExponent s ≤ (queries s γ c t : ℝ) / 10 := by
  obtain ⟨tf, htf, hfloor⟩ := eventual_floor_conditions s γ c hγ hc
  let t₀ := max tmin tf
  have ht₀ : 1 ≤ t₀ := htf.trans (le_max_right _ _)
  have hf : ∀ t : ℕ, t₀ ≤ t →
      2 ≤ γ * (t : ℝ) ^ (s + 2) ∧
      2 ≤ c * (clusters s t : ℝ) * (clusterSize s γ t : ℝ) ^ 2 :=
    fun t ht => hfloor t ((le_max_right tmin tf).trans ht)
  obtain ⟨k, hk, hs⟩ := all_sizes_scale d s γ c hd hγ hc t₀ ht₀ hf
  refine ⟨k, hk, points d s γ t₀, ?_⟩
  intro n hn
  obtain ⟨t, ht, htn, hnt, hqp, hqs⟩ := hs n hn
  obtain ⟨hR, hq⟩ := hf t ht
  exact ⟨t, (le_max_left tmin tf).trans ht, ht₀.trans ht, hR, hq, htn, hnt, hqp, hqs⟩

noncomputable def terminals (d s : ℕ) (γ : ℝ) (t : ℕ) : ℕ :=
  ordinary s γ t + special d s t

theorem points_le_terminals (d s : ℕ) (γ : ℝ) (t : ℕ) :
    points d s γ t ≤ (d + 1) * terminals d s γ t := by
  unfold points terminals
  nlinarith

theorem terminal_linear_bound (d s : ℕ) (γ : ℝ) (n t : ℕ)
    (hn : n ≤ ratio s * points d s γ t) :
    n ≤ ratio s * (d + 1) * terminals d s γ t := by
  exact hn.trans (by
    have hh := Nat.mul_le_mul_left (ratio s) (points_le_terminals d s γ t)
    simpa only [Nat.mul_assoc] using hh)

abbrev BasePoints (d s : ℕ) (γ : ℝ) (t : ℕ) :=
  Public.Points (Fin (special d s t)) (Fin (clusters s t)) (Fin (clusterSize s γ t))
    (Fin (special d s t * clusterSize s γ t))

abbrev PaddedPoints (d s : ℕ) (γ : ℝ) (t n : ℕ) :=
  Public.Points (Fin (special d s t)) (Fin (clusters s t)) (Fin (clusterSize s γ t))
    (Fin (special d s t * clusterSize s γ t) ⊕ Fin (n - points d s γ t))

noncomputable def paddedTerminals (d s : ℕ) (γ : ℝ) (t n : ℕ) :
    Finset (PaddedPoints d s γ t n) :=
  Public.terminalLabels

theorem base_point_count (d s : ℕ) (γ : ℝ) (t : ℕ) :
    Fintype.card (BasePoints d s γ t) = points d s γ t := by
  rw [Public.point_count]
  simp only [← Nat.card_eq_fintype_card, Nat.card_fin]
  unfold points ordinary special
  ring

theorem padded_point_count (d s : ℕ) (γ : ℝ) (t n : ℕ)
    (hn : points d s γ t ≤ n) :
    Fintype.card (PaddedPoints d s γ t n) = n := by
  rw [Public.point_count_padding]
  have hpad : Fintype.card (Fin (n - points d s γ t)) = n - points d s γ t := by
    rw [← Nat.card_eq_fintype_card, Nat.card_fin]
  rw [hpad]
  change Fintype.card (BasePoints d s γ t) + (n - points d s γ t) = n
  rw [base_point_count, Nat.add_sub_of_le hn]

theorem padded_terminal_count (d s : ℕ) (γ : ℝ) (t n : ℕ) :
    (Public.terminalLabels (S := Fin (special d s t)) (G := Fin (clusters s t))
      (I := Fin (clusterSize s γ t))
      (C := Fin (special d s t * clusterSize s γ t) ⊕ Fin (n - points d s γ t))).card =
        terminals d s γ t := by
  rw [Public.terminal_count]
  simp only [Fintype.card_fin, terminals, ordinary]
  omega

theorem padded_terminal_linear_bound (d s : ℕ) (γ : ℝ) (t n : ℕ)
    (hn : n ≤ ratio s * points d s γ t) :
    n ≤ ratio s * (d + 1) * (paddedTerminals d s γ t n).card := by
  rw [paddedTerminals, padded_terminal_count]
  exact terminal_linear_bound d s γ n t hn

theorem tiny_bounds (d s : ℕ) (γ : ℝ) (t n : ℕ)
    (ht : 1 ≤ t) (hR : 2 ≤ γ * (t : ℝ) ^ (s + 2))
    (hnt : points d s γ t ≤ n) (htn : n ≤ ratio s * points d s γ t) :
    0 < ParameterGeometry.tiny (clusters s t) (clusterSize s γ t) ∧
      ParameterGeometry.tiny (clusters s t) (clusterSize s γ t) ≤ 1 ∧
      1 / (n : ℝ) ^ 3 ≤ ParameterGeometry.tiny (clusters s t) (clusterSize s γ t) ∧
      ParameterGeometry.tiny (clusters s t) (clusterSize s γ t) ≤
        ((ratio s * (2 * d + 1) : ℕ) : ℝ) ^ 3 / (n : ℝ) ^ 3 := by
  have hA : 1 ≤ clusters s t := by
    unfold clusters
    have hh := Nat.pow_le_pow_left ht (s + 3)
    simpa only [one_pow] using hh
  have hRp : 1 ≤ clusterSize s γ t := clusterSize_pos s γ t hR
  have hK : 1 ≤ ordinary s γ t := by
    unfold ordinary
    nlinarith
  have hKn : ordinary s γ t ≤ n := by
    have hh : ordinary s γ t ≤ points d s γ t := by unfold points; nlinarith
    exact hh.trans hnt
  have hnK : n ≤ (ratio s * (2 * d + 1)) * ordinary s γ t := by
    have hh := Nat.mul_le_mul_left (ratio s) (points_le d s γ t hRp)
    exact htn.trans (by simpa only [Nat.mul_assoc] using hh)
  obtain ⟨hlo, hhi⟩ := ParameterGeometry.distance_scale n (ordinary s γ t)
    (ratio s * (2 * d + 1)) hK hKn hnK
  exact ⟨ParameterGeometry.tiny_pos _ _ hA hRp, ParameterGeometry.tiny_le_one _ _ hA hRp,
    by simpa only [ParameterGeometry.tiny, ordinary] using hlo,
    by simpa only [ParameterGeometry.tiny, ordinary] using hhi⟩

theorem eventual_padded_sizes (d s : ℕ) (γ c : ℝ) (hd : 1 ≤ d)
    (hγ : 0 < γ) (hc : 0 < c) (tmin : ℕ) :
    ∃ k : ℝ, 0 < k ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ t : ℕ, tmin ≤ t ∧ 1 ≤ t ∧
        2 ≤ γ * (t : ℝ) ^ (s + 2) ∧
        2 ≤ c * (clusters s t : ℝ) * (clusterSize s γ t : ℝ) ^ 2 ∧
        Fintype.card (PaddedPoints d s γ t n) = n ∧
        n ≤ ratio s * (d + 1) * (paddedTerminals d s γ t n).card ∧
        1 ≤ queries s γ c t ∧
        k * (n : ℝ) ^ Exponents.lowerExponent s ≤ (queries s γ c t : ℝ) / 10 ∧
        0 < ParameterGeometry.tiny (clusters s t) (clusterSize s γ t) ∧
        ParameterGeometry.tiny (clusters s t) (clusterSize s γ t) ≤ 1 ∧
        1 / (n : ℝ) ^ 3 ≤ ParameterGeometry.tiny (clusters s t) (clusterSize s γ t) ∧
        ParameterGeometry.tiny (clusters s t) (clusterSize s γ t) ≤
          ((ratio s * (2 * d + 1) : ℕ) : ℝ) ^ 3 / (n : ℝ) ^ 3 := by
  obtain ⟨k, hk, N, hs⟩ := eventual_all_sizes d s γ c hd hγ hc tmin
  refine ⟨k, hk, N, ?_⟩
  intro n hn
  obtain ⟨t, hmin, ht, hR, hq, hnt, htn, hqp, hscale⟩ := hs n hn
  obtain ⟨htiny, htiny₁, hlo, hhi⟩ := tiny_bounds d s γ t n ht hR hnt htn
  exact ⟨t, hmin, ht, hR, hq, padded_point_count d s γ t n hnt,
    padded_terminal_linear_bound d s γ t n htn, hqp, hscale, htiny, htiny₁, hlo, hhi⟩

end SteinerLowerBound.MetricComparison.AllSizes
