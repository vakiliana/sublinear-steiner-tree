module

public import SteinerUpperBound.TreeGeometry.Counts
public import SteinerUpperBound.TreeGeometry.Packing
public import SteinerLowerBound.QueryModel

@[expose] public section

namespace SteinerUpperBound.TreeGeometry

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*}

namespace Flooring

noncomputable def distance (I : Instance V) (lam : ℝ) (x y : V) : ℝ :=
  if x = y then 0 else max (I.distance x y) lam

@[simp] theorem distance_self (I : Instance V) (lam : ℝ) (x : V) :
    distance I lam x x = 0 := by
  classical
  simp [distance]

theorem distance_of_ne (I : Instance V) (lam : ℝ) {x y : V} (h : x ≠ y) :
    distance I lam x y = max (I.distance x y) lam := by
  classical
  simp [distance, h]

theorem distance_comm (I : Instance V) (lam : ℝ) (x y : V) :
    distance I lam x y = distance I lam y x := by
  classical
  simp only [distance, eq_comm, I.distance_comm x y]

theorem distance_nonneg (I : Instance V) (lam : ℝ) (x y : V) :
    0 ≤ distance I lam x y := by
  classical
  by_cases h : x = y
  · simp [distance, h]
  · rw [distance_of_ne I lam h]
    exact (I.distance_nonneg x y).trans (le_max_left _ _)

theorem original_le_distance (I : Instance V) (lam : ℝ) (x y : V) :
    I.distance x y ≤ distance I lam x y := by
  by_cases h : x = y
  · subst y
    simp [I.distance_self]
  · rw [distance_of_ne I lam h]
    exact le_max_left _ _

theorem distance_le_add (I : Instance V) (lam : ℝ) (hlam : 0 ≤ lam) (x y : V) :
    distance I lam x y ≤ I.distance x y + lam := by
  by_cases h : x = y
  · subst y
    simpa only [distance_self, I.distance_self, zero_add] using hlam
  · rw [distance_of_ne I lam h]
    exact max_le (by linarith) (by linarith [I.distance_nonneg x y])

theorem distance_triangle (I : Instance V) (lam : ℝ) (x y z : V) :
    distance I lam x z ≤ distance I lam x y + distance I lam y z := by
  by_cases hxz : x = z
  · subst z
    simpa only [distance_self] using
      add_nonneg (distance_nonneg I lam x y) (distance_nonneg I lam y x)
  by_cases hxy : x = y
  · subst y
    simp
  by_cases hyz : y = z
  · subst z
    simp
  rw [distance_of_ne I lam hxz]
  apply max_le
  · exact (I.distance_triangle x y z).trans
      (add_le_add (original_le_distance I lam x y) (original_le_distance I lam y z))
  · have hlam : lam ≤ distance I lam x y := by
      rw [distance_of_ne I lam hxy]
      exact le_max_right _ _
    linarith [distance_nonneg I lam y z]

theorem eq_of_distance_eq_zero (I : Instance V) (lam : ℝ) {x y : V}
    (h : distance I lam x y = 0) : x = y := by
  by_contra hxy
  have hd := original_le_distance I lam x y
  have hp := I.distance_pos x y hxy
  linarith

@[instance_reducible]
noncomputable def metric (I : Instance V) (lam : ℝ) : MetricSpace V where
  dist := distance I lam
  dist_self := distance_self I lam
  dist_comm := distance_comm I lam
  dist_triangle := distance_triangle I lam
  eq_of_dist_eq_zero := eq_of_distance_eq_zero I lam

noncomputable abbrev floored (I : Instance V) (lam : ℝ) : Instance V :=
  ⟨metric I lam, I.terminals⟩

@[simp] theorem instance_terminals (I : Instance V) (lam : ℝ) :
    (floored I lam).terminals = I.terminals := rfl

@[simp] theorem instance_distance (I : Instance V) (lam : ℝ) (x y : V) :
    (floored I lam).distance x y = distance I lam x y := rfl

theorem weight_mono (I : Instance V) (lam : ℝ) (e : Sym2 V) :
    I.weight e ≤ (floored I lam).weight e := by
  rcases e with ⟨x, y⟩
  simpa only [Instance.weight_mk, instance_distance] using original_le_distance I lam x y

theorem weight_le_add (I : Instance V) (lam : ℝ) (hlam : 0 ≤ lam) (e : Sym2 V) :
    (floored I lam).weight e ≤ I.weight e + lam := by
  rcases e with ⟨x, y⟩
  simpa only [Instance.weight_mk, instance_distance] using distance_le_add I lam hlam x y

/-- Diagonal queries require no oracle call; each other floored-distance query
uses exactly the corresponding original-distance query. -/
noncomputable def query (lam : ℝ) (x y : V) : DecisionTree (V × V) ℝ ℝ :=
  if x = y then .leaf 0 else .query (x, y) (fun d => .leaf (max d lam))

theorem query_correct (I : Instance V) (lam : ℝ) (x y : V) :
    (query lam x y).output (fun q => I.distance q.1 q.2) = (floored I lam).distance x y := by
  classical
  by_cases h : x = y <;> simp [query, DecisionTree.output, instance_distance, distance, h]

theorem query_queries_le_one (oracle : V × V → ℝ) (lam : ℝ) (x y : V) :
    (query lam x y).queries oracle ≤ 1 := by
  classical
  by_cases h : x = y <;>
    simp [query, DecisionTree.queries, DecisionTree.transcript, h]

noncomputable def simulate {R : Type*} (lam : ℝ) :
    DecisionTree (V × V) ℝ R → DecisionTree (V × V) ℝ R
  | .leaf r => .leaf r
  | .query q next =>
    if q.1 = q.2 then simulate lam (next 0)
    else .query q (fun d => simulate lam (next (max d lam)))

theorem simulate_output {R : Type*} (I : Instance V) (lam : ℝ)
    (t : DecisionTree (V × V) ℝ R) :
    (simulate lam t).output (fun q => I.distance q.1 q.2) =
      t.output (fun q => (floored I lam).distance q.1 q.2) := by
  classical
  induction t with
  | leaf r => rfl
  | query q next ih =>
    by_cases h : q.1 = q.2
    · simpa [simulate, DecisionTree.output, instance_distance, distance, h] using ih 0
    · simpa [simulate, DecisionTree.output, instance_distance, distance, h] using
        ih (max (I.distance q.1 q.2) lam)

theorem simulate_queries_le {R : Type*} (I : Instance V) (lam : ℝ)
    (t : DecisionTree (V × V) ℝ R) :
    (simulate lam t).queries (fun q => I.distance q.1 q.2) ≤
      t.queries (fun q => (floored I lam).distance q.1 q.2) := by
  classical
  induction t with
  | leaf r => exact le_rfl
  | query q next ih =>
    by_cases h : q.1 = q.2
    · have hh := ih 0
      simp only [simulate, ↓reduceIte, DecisionTree.queries, DecisionTree.transcript,
        List.length_cons, instance_distance, distance, h] at hh ⊢
      omega
    · simpa [simulate, DecisionTree.queries, DecisionTree.transcript, instance_distance,
        distance, h] using Nat.succ_le_succ (ih (max (I.distance q.1 q.2) lam))

theorem optimum_mono [Fintype V] (I : Instance V) (lam : ℝ) :
    I.optimum ≤ (floored I lam).optimum := by
  obtain ⟨G, hG, he⟩ := (floored I lam).optimum_attained
  apply (I.optimum_le G hG).trans
  rw [← he]
  exact Finset.sum_le_sum fun e _ => weight_mono I lam e

theorem tree_cost_le [Fintype V] (I : Instance V) (lam : ℝ) (hlam : 0 ≤ lam)
    (S : TreeSolution I) :
    GraphCost.cost (floored I lam).weight S.ambient ≤
      S.cost + (S.graph.edgeFinset.card : ℝ) * lam := by
  rw [TreeSolution.ambient, cost_map_eq _ _ Subtype.val_injective]
  have hh : (∑ e ∈ S.graph.edgeFinset, (floored I lam).weight (e.map Subtype.val)) ≤
      ∑ e ∈ S.graph.edgeFinset, (I.weight (e.map Subtype.val) + lam) :=
    Finset.sum_le_sum fun e _ => weight_le_add I lam hlam _
  simpa only [TreeSolution.cost, GraphCost.cost, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul] using hh

theorem optimum_le_add [Fintype V] (I : Instance V) (lam : ℝ) (hlam : 0 ≤ lam) :
    (floored I lam).optimum ≤ I.optimum + 2 * (I.terminals.card : ℝ) * lam := by
  classical
  by_cases hk : I.terminals.card ≤ 1
  · rw [(floored I lam).optimum_eq_zero hk, I.optimum_eq_zero hk]
    positivity
  · have hk2 : 2 ≤ I.terminals.card := by omega
    have hT : I.terminals.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨S, hS, hclean⟩ := clean_optimum_tree_attained I hT
    have hcount : S.graph.edgeFinset.card ≤ 2 * I.terminals.card := by
      have hh := S.edges_card_le hclean hk2
      omega
    have hcountR : (S.graph.edgeFinset.card : ℝ) ≤ 2 * (I.terminals.card : ℝ) := by
      exact_mod_cast hcount
    calc
      _ ≤ GraphCost.cost (floored I lam).weight S.ambient :=
        (floored I lam).optimum_le S.ambient S.ambient_feasible
      _ ≤ S.cost + (S.graph.edgeFinset.card : ℝ) * lam := tree_cost_le I lam hlam S
      _ ≤ _ := by rw [hS]; gcongr

end Flooring

noncomputable def terminalRadius (I : Instance V) (x₀ : V) : ℝ :=
  (insert 0 (I.terminals.image (I.distance x₀))).max' (by simp)

theorem terminalRadius_nonneg (I : Instance V) (x₀ : V) :
    0 ≤ terminalRadius I x₀ := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem distance_le_terminalRadius (I : Instance V) (x₀ : V) {x : V}
    (hx : x ∈ I.terminals) : I.distance x₀ x ≤ terminalRadius I x₀ := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hx, rfl⟩))

theorem terminalRadius_le_optimum [Fintype V] (I : Instance V) (x₀ : V)
    (h₀ : x₀ ∈ I.terminals) : terminalRadius I x₀ ≤ I.optimum := by
  classical
  apply Finset.max'_le
  intro d hd
  rcases Finset.mem_insert.mp hd with h | h
  · simpa only [h] using I.optimum_nonneg
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
    exact terminal_distance_le_optimum I h₀ hx

theorem terminalRadius_le_mst [Fintype V] (I : Instance V) (x₀ : V)
    (h₀ : x₀ ∈ I.terminals) : terminalRadius I x₀ ≤ I.mst :=
  (terminalRadius_le_optimum I x₀ h₀).trans I.optimum_le_mst

theorem terminalRadius_pos (I : Instance V) (x₀ : V)
    (h₀ : x₀ ∈ I.terminals) (hk : 2 ≤ I.terminals.card) :
    0 < terminalRadius I x₀ := by
  classical
  have hne : (I.terminals.erase x₀).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem h₀]
    omega
  obtain ⟨x, hx⟩ := hne
  obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
  exact (I.distance_pos x₀ x hne.symm).trans_le (distance_le_terminalRadius I x₀ hx)

theorem terminal_distance_le_twice_radius (I : Instance V) (x₀ : V)
    {x y : V} (hx : x ∈ I.terminals) (hy : y ∈ I.terminals) :
    I.distance x y ≤ 2 * terminalRadius I x₀ := by
  have h1 := distance_le_terminalRadius I x₀ hx
  have h2 := distance_le_terminalRadius I x₀ hy
  have ht := I.distance_triangle x x₀ y
  rw [I.distance_comm x x₀] at ht
  linarith

noncomputable def terminalDiameter (I : Instance V) : ℝ :=
  (insert 0 ((I.terminals.product I.terminals).image
    (fun p => I.distance p.1 p.2))).max' (by simp)

theorem terminalDiameter_le_twice_radius (I : Instance V) (x₀ : V) :
    terminalDiameter I ≤ 2 * terminalRadius I x₀ := by
  classical
  apply Finset.max'_le
  intro d hd
  rcases Finset.mem_insert.mp hd with h | h
  · rw [h]
    positivity [terminalRadius_nonneg I x₀]
  · obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp h
    exact terminal_distance_le_twice_radius I x₀
      (Finset.mem_product.mp hxy).1 (Finset.mem_product.mp hxy).2

namespace Flooring

noncomputable def normalizedScale (I : Instance V) (x₀ : V) (η : ℝ) : ℝ :=
  (η / 100) * terminalRadius I x₀ / (I.terminals.card : ℝ)

theorem normalizedScale_pos (I : Instance V) (x₀ : V)
    (h₀ : x₀ ∈ I.terminals) (hk : 2 ≤ I.terminals.card) (η : ℝ) (hη : 0 < η) :
    0 < normalizedScale I x₀ η := by
  have hr := terminalRadius_pos I x₀ h₀ hk
  have hkR : 0 < (I.terminals.card : ℝ) := by exact_mod_cast (show 0 < I.terminals.card by omega)
  unfold normalizedScale
  positivity

theorem transfer_estimate [Fintype V] (I : Instance V) (x₀ : V)
    (h₀ : x₀ ∈ I.terminals) (hk : 2 ≤ I.terminals.card)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (E : ℝ)
    (hlo : (floored I (normalizedScale I x₀ η)).optimum ≤ E)
    (hhi : E ≤ (2 - η) * (floored I (normalizedScale I x₀ η)).optimum) :
    I.optimum ≤ E ∧ E ≤ (2 - η / 2) * I.optimum := by
  have hlam := (normalizedScale_pos I x₀ h₀ hk η hη0).le
  refine ⟨(optimum_mono I _).trans hlo, ?_⟩
  have hkR : (I.terminals.card : ℝ) ≠ 0 := by
    exact_mod_cast (show I.terminals.card ≠ 0 by omega)
  have hr : terminalRadius I x₀ ≤ 2 * I.optimum :=
    (terminalRadius_le_mst I x₀ h₀).trans (mst_le_twice_optimum I)
  have herror : 2 * (I.terminals.card : ℝ) * normalizedScale I x₀ η ≤
      (η / 25) * I.optimum := by
    calc
      _ = (η / 50) * terminalRadius I x₀ := by
        unfold normalizedScale
        field_simp
        ring
      _ ≤ (η / 50) * (2 * I.optimum) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring
  have hfloor : (floored I (normalizedScale I x₀ η)).optimum ≤
      (1 + η / 25) * I.optimum := by
    have hh := optimum_le_add I (normalizedScale I x₀ η) hlam
    nlinarith
  have hfactor : (2 - η) * (1 + η / 25) ≤ 2 - η / 2 := by
    nlinarith [sq_nonneg η]
  calc
    E ≤ (2 - η) * (floored I (normalizedScale I x₀ η)).optimum := hhi
    _ ≤ (2 - η) * ((1 + η / 25) * I.optimum) :=
      mul_le_mul_of_nonneg_left hfloor (by linarith)
    _ = ((2 - η) * (1 + η / 25)) * I.optimum := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor I.optimum_nonneg

end Flooring

end SteinerUpperBound.TreeGeometry
