module

public import SteinerUpperBound.MSTProfile

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerUpperBound.TerminalMST

open SteinerLowerBound MeasureTheory
open scoped Classical Interval BigOperators

variable {V : Type*} [Fintype V]

noncomputable def layer (b x : ℝ) : ℝ := if x ≤ b then 1 else 0

theorem layer_integrable (b lo hi : ℝ) : IntervalIntegrable (layer b) volume lo hi := by
  have hm : Measurable (layer b) :=
    Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume lo hi).mono_fun'
    hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by by_cases h : x ≤ b <;> simp [layer, h])

theorem integral_layer (b M : ℝ) (hb : 0 ≤ b) (hM : b ≤ M) :
    (∫ x in (0 : ℝ)..M, layer b x) = b := by
  have he : layer b = {x : ℝ | x ≤ b}.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases h : x ≤ b <;> simp [layer, Set.indicator, h]
  rw [he, intervalIntegral.integral_indicator ⟨hb, hM⟩, intervalIntegral.integral_const]
  simp

omit [Fintype V] in
theorem heavy_cons_real (e : Sym2 V) (l : List (Sym2 V)) (w : Sym2 V → ℝ) (a : ℝ) :
    (heavy (e :: l) w a : ℝ) = layer (w e) a + (heavy l w a : ℝ) := by
  by_cases h : a ≤ w e <;>
    simp [heavy, WeightedSelection.count, layer, h, Nat.cast_add, add_comm]

omit [Fintype V] in
theorem heavy_integrable (l : List (Sym2 V)) (w : Sym2 V → ℝ) (lo hi : ℝ) :
    IntervalIntegrable (fun a => (heavy l w a : ℝ)) volume lo hi := by
  induction l with
  | nil => simpa [heavy, WeightedSelection.count] using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume lo hi)
  | cons e l ih =>
      have he : (fun a => (heavy (e :: l) w a : ℝ)) =
          fun a => layer (w e) a + (heavy l w a : ℝ) := funext (heavy_cons_real e l w)
      rw [he]
      exact (layer_integrable (w e) lo hi).add ih

omit [Fintype V] in
theorem integral_heavy (l : List (Sym2 V)) (w : Sym2 V → ℝ) (M : ℝ)
    (hw : ∀ e ∈ l, 0 ≤ w e ∧ w e ≤ M) :
    (∫ a in (0 : ℝ)..M, (heavy l w a : ℝ)) = (l.map w).sum := by
  induction l with
  | nil => simp [heavy, WeightedSelection.count]
  | cons e l ih =>
      have htail : ∀ f ∈ l, 0 ≤ w f ∧ w f ≤ M := fun f hf =>
        hw f (List.mem_cons_of_mem _ hf)
      have he : (fun a => (heavy (e :: l) w a : ℝ)) =
          fun a => layer (w e) a + (heavy l w a : ℝ) := funext (heavy_cons_real e l w)
      rw [he, intervalIntegral.integral_add (layer_integrable (w e) 0 M) (heavy_integrable l w 0 M),
        integral_layer (w e) M (hw e List.mem_cons_self).1 (hw e List.mem_cons_self).2,
        ih htail]
      rfl

noncomputable def curve (w : Sym2 V → ℝ) (T : Finset V) (a : ℝ) : ℝ :=
  ((T.card - 1 : ℕ) : ℝ) - GraphRank.rank (below w T a)

theorem curve_heavy (w : Sym2 V → ℝ) (T : Finset V) (a : ℝ) :
    curve w T a = (heavy (SpanningForest.picked (input w T) ⊥) w a : ℝ) := by
  have h : (heavy (SpanningForest.picked (input w T) ⊥) w a : ℝ) +
      GraphRank.rank (below w T a) = ((T.card - 1 : ℕ) : ℝ) := by
    exact_mod_cast heavy_profile w T a
  unfold curve
  linarith

theorem curve_integrable (w : Sym2 V → ℝ) (T : Finset V) (lo hi : ℝ) :
    IntervalIntegrable (curve w T) volume lo hi := by
  have he : curve w T = fun a => (heavy (SpanningForest.picked (input w T) ⊥) w a : ℝ) :=
    funext (curve_heavy w T)
  rw [he]
  exact heavy_integrable _ _ _ _

theorem integral_curve (w : Sym2 V → ℝ) (T : Finset V) (hw : ∀ e, 0 ≤ w e)
    (M : ℝ) (hM : ∀ e ∈ (Network.completeOn T).edgeSet, w e ≤ M) :
    value w T = ∫ a in (0 : ℝ)..M, curve w T a := by
  have hb : ∀ e ∈ SpanningForest.picked (input w T) ⊥, 0 ≤ w e ∧ w e ≤ M := by
    intro e he
    exact ⟨hw e, hM e ((input_mem w T e).mp
      ((SpanningForest.picked_sublist _ _).subset he))⟩
  rw [value_eq_sum w T hw]
  calc
    _ = ∫ a in (0 : ℝ)..M, (heavy (SpanningForest.picked (input w T) ⊥) w a : ℝ) :=
      (integral_heavy _ _ _ hb).symm
    _ = _ := intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall
      (fun a _ => (curve_heavy w T a).symm))

noncomputable def zeroed (w : Sym2 V → ℝ) (F : SimpleGraph V) (e : Sym2 V) : ℝ :=
  if e ∈ F.edgeSet then 0 else w e

theorem zeroed_nonneg (w : Sym2 V → ℝ) (F : SimpleGraph V) (hw : ∀ e, 0 ≤ w e) :
    ∀ e, 0 ≤ zeroed w F e := by
  intro e
  unfold zeroed
  split_ifs
  · rfl
  · exact hw e

theorem zeroed_le (w : Sym2 V → ℝ) (F : SimpleGraph V) (hw : ∀ e, 0 ≤ w e) :
    ∀ e, zeroed w F e ≤ w e := by
  intro e
  unfold zeroed
  split_ifs
  · exact hw e
  · rfl

theorem zeroed_bot (w : Sym2 V → ℝ) : zeroed w (⊥ : SimpleGraph V) = w := by
  funext e
  simp only [zeroed, SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false, if_false]

theorem zeroed_sup (w : Sym2 V → ℝ) (G F : SimpleGraph V) :
    zeroed (zeroed w G) F = zeroed w (G ⊔ F) := by
  funext e
  by_cases hG : e ∈ G.edgeSet <;> by_cases hF : e ∈ F.edgeSet <;>
    simp [zeroed, SimpleGraph.edgeSet_sup, hG, hF]

theorem below_zeroed (w : Sym2 V → ℝ) (T : Finset V) (F : SimpleGraph V)
    (hF : Network.TerminalOnly T F) (a : ℝ) (ha : 0 < a) :
    below (zeroed w F) T a = below w T a ⊔ F := by
  ext x y
  simp only [below_adj, SimpleGraph.sup_adj]
  by_cases hxy : F.Adj x y
  · obtain ⟨hx, hy⟩ := hF x y hxy
    have he : Sym2.mk x y ∈ F.edgeSet := (SimpleGraph.mem_edgeSet F).mpr hxy
    simp [zeroed, he, hx, hy, hxy, hxy.ne, ha]
  · have he : Sym2.mk x y ∉ F.edgeSet := fun h => hxy ((SimpleGraph.mem_edgeSet F).mp h)
    simp [zeroed, he, hxy]

theorem curve_difference (w : Sym2 V → ℝ) (T : Finset V) (F : SimpleGraph V)
    (hF : Network.TerminalOnly T F) (a : ℝ) (ha : 0 < a) :
    curve w T a - curve (zeroed w F) T a = GraphRank.gain (below w T a) F := by
  unfold curve GraphRank.gain
  rw [below_zeroed w T F hF a ha]
  ring

theorem gain_integrable (w : Sym2 V → ℝ) (T : Finset V) (F : SimpleGraph V)
    (hF : Network.TerminalOnly T F) (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) :
    IntervalIntegrable (fun a => GraphRank.gain (below w T a) F) volume lo hi := by
  apply ((curve_integrable w T lo hi).sub (curve_integrable (zeroed w F) T lo hi)).congr
  intro a ha
  rw [Set.uIoc_of_le hlohi] at ha
  exact curve_difference w T F hF a (hlo.trans_lt ha.1)

theorem value_difference_integral (w : Sym2 V → ℝ) (T : Finset V) (F : SimpleGraph V)
    (hw : ∀ e, 0 ≤ w e) (hF : Network.TerminalOnly T F)
    (M : ℝ) (hM₀ : 0 ≤ M) (hM : ∀ e ∈ (Network.completeOn T).edgeSet, w e ≤ M) :
    value w T - value (zeroed w F) T =
      ∫ a in (0 : ℝ)..M, GraphRank.gain (below w T a) F := by
  have hM' : ∀ e ∈ (Network.completeOn T).edgeSet, zeroed w F e ≤ M :=
    fun e he => (zeroed_le w F hw e).trans (hM e he)
  rw [integral_curve w T hw M hM, integral_curve (zeroed w F) T (zeroed_nonneg w F hw) M hM',
    ← intervalIntegral.integral_sub (curve_integrable w T 0 M)
      (curve_integrable (zeroed w F) T 0 M)]
  apply intervalIntegral.integral_congr_ae
  refine Filter.Eventually.of_forall (fun a ha => ?_)
  rw [Set.uIoc_of_le hM₀] at ha
  exact curve_difference w T F hF a ha.1

end SteinerUpperBound.TerminalMST
