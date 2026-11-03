module

public import SteinerUpperBound.EstimatorParameters.Fixed
public import SteinerUpperBound.QueryProgram.MetricSimulation

@[expose] public section

namespace SteinerUpperBound.EstimatorParameters

open SteinerLowerBound QueryProgram
open scoped Classical

variable {V Q Out : Type*}

noncomputable def rowValue (w : Sym2 V → ℝ) (root : V) : List V → ℝ → ℝ
  | [], r => r
  | x :: xs, r => rowValue w root xs (max r (w s(root, x)))

noncomputable def rootRow (root : V) : List V → ℝ → Code (Sym2 V) Q ℝ
  | [], r => .tick 0 (.pure r)
  | x :: xs, r => .metric s(root, x) (fun d => .tick 1 (rootRow root xs (max r d)))

noncomputable abbrev rowResult (w : Sym2 V → ℝ) (root : V) (l : List V) (r : ℝ) : Outcome ℝ :=
  ⟨rowValue w root l r, 3 * l.length + 1, l.length, 0, 0⟩

theorem rootRow_evaluates (w : Sym2 V → ℝ) (bits : Q → Bool) (root : V) (l : List V) (r : ℝ) :
    Code.Evaluates w bits (rootRow root l r) (rowResult w root l r) := by
  induction l generalizing r with
  | nil => intro F; rfl
  | cons x xs ih =>
    intro F
    simp only [rootRow, Code.evaluate]
    rw [ih]
    simp only [Outcome.add, rowResult, rowValue, List.length_cons]
    congr 2 <;> omega

theorem rootRow_queries (w : Sym2 V → ℝ) (bits : Q → Bool) (root : V) (l : List V) :
    (rootRow root l 0).evaluate w bits (fun o => (o.metricQueries : ℝ)) = l.length := by
  rw [rootRow_evaluates]

theorem rootRow_work (w : Sym2 V → ℝ) (bits : Q → Bool) (root : V) (l : List V) :
    (rootRow root l 0).evaluate w bits (fun o => (o.work : ℝ)) = (3 * l.length + 1 : ℕ) := by
  rw [rootRow_evaluates]

theorem rowValue_acc (w : Sym2 V → ℝ) (root : V) (l : List V) (r : ℝ) :
    r ≤ rowValue w root l r := by
  induction l generalizing r with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left _ _).trans (ih _)

theorem rowValue_mem (w : Sym2 V → ℝ) (root : V) (l : List V) (r : ℝ) {x : V} (hx : x ∈ l) :
    w s(root, x) ≤ rowValue w root l r := by
  induction l generalizing r with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with hxy | hx
    · subst x
      exact (le_max_right _ _).trans (rowValue_acc w root ys _)
    · exact ih _ hx

theorem rowValue_le (w : Sym2 V → ℝ) (root : V) (l : List V) (r upper : ℝ)
    (hr : r ≤ upper) (hw : ∀ x ∈ l, w s(root, x) ≤ upper) :
    rowValue w root l r ≤ upper := by
  induction l generalizing r with
  | nil => exact hr
  | cons x xs ih =>
    exact ih _ (max_le hr (hw x List.mem_cons_self)) (fun y hy => hw y (List.mem_cons_of_mem _ hy))

theorem rowValue_eq_radius (I : Instance V) (root : V) (l : List V) (hT : l.toFinset = I.terminals) :
    rowValue I.weight root l 0 = TreeGeometry.terminalRadius I root := by
  classical
  apply le_antisymm
  · apply rowValue_le I.weight root l 0 _ (TreeGeometry.terminalRadius_nonneg I root)
    intro x hx
    rw [Instance.weight_mk]
    exact TreeGeometry.distance_le_terminalRadius I root (hT ▸ List.mem_toFinset.mpr hx)
  · unfold TreeGeometry.terminalRadius
    apply Finset.max'_le
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact rowValue_acc I.weight root l 0
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
      have hxl : x ∈ l := List.mem_toFinset.mp (hT.symm ▸ hx)
      simpa only [Instance.weight_mk] using rowValue_mem I.weight root l 0 hxl

theorem observed_radius_geometry [Fintype V] (I : Instance V) (root : V) (l : List V)
    (hT : l.toFinset = I.terminals) (hroot : root ∈ I.terminals) (hk : 2 ≤ I.terminals.card) :
    let R := rowValue I.weight root l 0
    0 < R ∧ R ≤ I.mst ∧ TreeGeometry.terminalDiameter I ≤ 2 * R := by
  rw [rowValue_eq_radius I root l hT]
  exact ⟨TreeGeometry.terminalRadius_pos I root hroot hk, TreeGeometry.terminalRadius_le_mst I root hroot,
    TreeGeometry.terminalDiameter_le_twice_radius I root⟩

noncomputable def floorScale (k : ℕ) (R : ℝ) : ℝ := zeta * R / k

theorem floorScale_pos (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R) : 0 < floorScale k R := by
  have hz : 0 < zeta := by norm_num [zeta, zetaQ, cQ]
  unfold floorScale
  positivity

theorem floorScale_le (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R) : floorScale k R ≤ R := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hz : zeta ≤ 1 := by norm_num [zeta, zetaQ, cQ]
  unfold floorScale
  apply (div_le_iff₀ (show (0 : ℝ) < k by exact_mod_cast hk)).mpr
  have h1 := mul_le_mul_of_nonneg_right hz hR
  have h2 := mul_le_mul_of_nonneg_left hkR hR
  nlinarith

theorem observed_scale_eq (I : Instance V) (root : V) (l : List V)
    (hn : l.Nodup) (hT : l.toFinset = I.terminals) :
    floorScale l.length (rowValue I.weight root l 0) = TreeGeometry.Flooring.normalizedScale I root c := by
  have hcard : l.length = I.terminals.card := by
    rw [← hT]
    exact (List.toFinset_card_of_nodup hn).symm
  rw [rowValue_eq_radius I root l hT, hcard]
  unfold floorScale TreeGeometry.Flooring.normalizedScale
  have hz : zeta = c / 100 := by norm_num [zeta, zetaQ, c, cQ]
  rw [hz]

noncomputable def floorResponse (lam : ℝ) (q : Sym2 V) (d : ℝ) : ℝ :=
  if q.IsDiag then 0 else max d lam

theorem floorResponse_correct (I : Instance V) (lam : ℝ) (q : Sym2 V) :
    floorResponse lam q (I.weight q) = (TreeGeometry.Flooring.floored I lam).weight q := by
  rcases q with ⟨x, y⟩
  simp only [floorResponse, Sym2.mk_isDiag_iff, Instance.weight_mk,
    TreeGeometry.Flooring.instance_distance, TreeGeometry.Flooring.distance]

theorem floored_diameter_le (I : Instance V) (root : V) (lam : ℝ)
    (hlam : lam ≤ TreeGeometry.terminalRadius I root) :
    TreeGeometry.terminalDiameter (TreeGeometry.Flooring.floored I lam) ≤
      2 * TreeGeometry.terminalRadius I root := by
  classical
  have hR := TreeGeometry.terminalRadius_nonneg I root
  unfold TreeGeometry.terminalDiameter
  apply Finset.max'_le
  intro d hd
  rcases Finset.mem_insert.mp hd with rfl | hd
  · positivity
  · obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hd
    have hmem : x ∈ I.terminals ∧ y ∈ I.terminals := Finset.mem_product.mp hxy
    have horig := TreeGeometry.terminal_distance_le_twice_radius I root hmem.1 hmem.2
    by_cases h : x = y
    · subst y
      simp only [TreeGeometry.Flooring.instance_distance, TreeGeometry.Flooring.distance_self]
      positivity
    · rw [TreeGeometry.Flooring.instance_distance, TreeGeometry.Flooring.distance_of_ne I lam h]
      exact max_le horig (by linarith)

theorem flooring_value (I : Instance V) (bits : Q → Bool) (lam : ℝ)
    (p : Code (Sym2 V) Q Out) (F : Out → ℝ) :
    (p.mapMetric (floorResponse lam) 2).evaluate I.weight bits (fun o => F o.value) =
      p.evaluate (TreeGeometry.Flooring.floored I lam).weight bits (fun o => F o.value) := by
  rw [Code.mapMetric_value]
  have he : (fun q => floorResponse lam q (I.weight q)) = (TreeGeometry.Flooring.floored I lam).weight :=
    funext (floorResponse_correct I lam)
  rw [he]

theorem flooring_queries (I : Instance V) (bits : Q → Bool) (lam : ℝ)
    (p : Code (Sym2 V) Q Out) :
    (p.mapMetric (floorResponse lam) 2).evaluate I.weight bits (fun o => (o.metricQueries : ℝ)) =
      p.evaluate (TreeGeometry.Flooring.floored I lam).weight bits (fun o => (o.metricQueries : ℝ)) := by
  rw [Code.mapMetric_queries]
  have he : (fun q => floorResponse lam q (I.weight q)) = (TreeGeometry.Flooring.floored I lam).weight :=
    funext (floorResponse_correct I lam)
  rw [he]

theorem flooring_work (I : Instance V) (bits : Q → Bool) (lam : ℝ)
    (p : Code (Sym2 V) Q Out) :
    (p.mapMetric (floorResponse lam) 2).evaluate I.weight bits (fun o => (o.work : ℝ)) =
      p.evaluate (TreeGeometry.Flooring.floored I lam).weight bits (fun o => (o.work : ℝ)) +
        3 * p.evaluate (TreeGeometry.Flooring.floored I lam).weight bits (fun o => (o.metricQueries : ℝ)) := by
  rw [Code.mapMetric_work]
  have he : (fun q => floorResponse lam q (I.weight q)) = (TreeGeometry.Flooring.floored I lam).weight :=
    funext (floorResponse_correct I lam)
  rw [he]
  norm_num

noncomputable def normalize (root : V) (l : List V) (next : ℝ → ℝ → Code (Sym2 V) Q Out) :
    Code (Sym2 V) Q Out :=
  (rootRow root l 0).bind (fun R =>
    .tick 3 ((next R (floorScale l.length R)).mapMetric (floorResponse (floorScale l.length R)) 2))

theorem normalize_value (I : Instance V) (bits : Q → Bool) (root : V) (l : List V)
    (next : ℝ → ℝ → Code (Sym2 V) Q Out) (F : Out → ℝ) :
    let R := rowValue I.weight root l 0
    let lam := floorScale l.length R
    (normalize root l next).evaluate I.weight bits (fun o => F o.value) =
      (next R lam).evaluate (TreeGeometry.Flooring.floored I lam).weight bits (fun o => F o.value) := by
  dsimp only
  rw [normalize, Code.evaluate_bind, rootRow_evaluates]
  simp only [Code.evaluate, Outcome.combine, Outcome.add]
  exact flooring_value I bits _ _ F

end SteinerUpperBound.EstimatorParameters
