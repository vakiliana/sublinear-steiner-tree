module

public import SteinerUpperBound.GraphRank
public import SteinerUpperBound.TreeGeometry
public import SteinerUpperBound.Structural.Saving

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators
open MeasureTheory

noncomputable abbrev e0 : ℝ := 1 / 10000
noncomputable abbrev chi : ℝ := 2 - e0
noncomputable abbrev p : ℝ := 2 * chi - 2
noncomputable abbrev b0 : ℝ := p - 1
noncomputable abbrev omega : ℝ := 101 / 100
noncomputable abbrev alpha0 : ℝ := 1 / 100
noncomputable abbrev delta0 : ℝ := 1 / 100
noncomputable abbrev theta0 : ℝ := 1 / 20
noncomputable abbrev sigma0 : ℝ := 1 / 1000

variable {V : Type*} [Fintype V]

noncomputable def threshold (I : Instance V) (a : ℝ) : SimpleGraph V :=
  GraphRank.ofEdges ((Network.completeOn I.terminals).edgeFinset.filter
    (fun e => I.weight e < a))

theorem threshold_adj (I : Instance V) (a : ℝ) (x y : V) :
    (threshold I a).Adj x y ↔
      x ≠ y ∧ x ∈ I.terminals ∧ y ∈ I.terminals ∧ I.distance x y < a := by
  classical
  simp only [threshold, GraphRank.ofEdges, SimpleGraph.fromEdgeSet_adj,
    Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet, Network.completeOn_adj, Instance.weight_mk]
  tauto

theorem threshold_mono (I : Instance V) {a b : ℝ} (hab : a ≤ b) :
    threshold I a ≤ threshold I b := by
  intro x y hxy
  obtain ⟨hne, hx, hy, hd⟩ := (threshold_adj I a x y).mp hxy
  exact (threshold_adj I b x y).mpr ⟨hne, hx, hy, hd.trans_le hab⟩

noncomputable def horizon (I : Instance V) : ℝ :=
  1 + ∑ x ∈ I.terminals, ∑ y ∈ I.terminals, I.distance x y

theorem horizon_pos (I : Instance V) : 0 < horizon I := by
  have hs : 0 ≤ ∑ x ∈ I.terminals, ∑ y ∈ I.terminals, I.distance x y :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => I.distance_nonneg x y
  unfold horizon
  linarith

theorem distance_lt_horizon (I : Instance V) {x y : V}
    (hx : x ∈ I.terminals) (hy : y ∈ I.terminals) :
    I.distance x y < horizon I := by
  have h1 := Finset.single_le_sum (fun y _ => I.distance_nonneg x y) hy
  have h2 : (∑ y ∈ I.terminals, I.distance x y) ≤
      ∑ x ∈ I.terminals, ∑ y ∈ I.terminals, I.distance x y := Finset.single_le_sum
    (fun x _ => Finset.sum_nonneg fun y _ => I.distance_nonneg x y) hx
  unfold horizon
  linarith

theorem measurable_filter_function {α : Type*} (s : Finset α) (w : α → ℝ)
    (F : Finset α → ℝ) :
    Measurable (fun a : ℝ => F (s.filter (fun e => w e < a))) := by
  classical
  induction s using Finset.induction_on generalizing F with
  | empty => simpa only [Finset.filter_empty] using measurable_const
  | @insert e s he ih =>
    have hset : MeasurableSet {a : ℝ | w e < a} :=
      measurableSet_lt measurable_const measurable_id
    have hh : Measurable ({a : ℝ | w e < a}.piecewise
        (fun a => F (insert e (s.filter (fun z => w z < a))))
        (fun a => F (s.filter (fun z => w z < a)))) :=
      Measurable.piecewise hset (ih (fun S => F (insert e S))) (ih F)
    convert hh using 1
    ext a
    by_cases h : w e < a <;> simp [Finset.filter_insert, Set.piecewise, h]

theorem gain_le_card (G F : SimpleGraph V) :
    GraphRank.gain G F ≤ (Fintype.card V : ℝ) := by
  have hh : GraphRank.rank (G ⊔ F) ≤ Fintype.card V := by
    have h := GraphRank.rank_add_components (G ⊔ F)
    simp only [Nat.card_eq_fintype_card] at h
    omega
  have hhR : (GraphRank.rank (G ⊔ F) : ℝ) ≤ Fintype.card V := by exact_mod_cast hh
  unfold GraphRank.gain
  have hn : 0 ≤ (GraphRank.rank G : ℝ) := Nat.cast_nonneg _
  linarith

theorem gain_measurable (I : Instance V) (earlier F : SimpleGraph V) :
    Measurable (fun a => GraphRank.gain (threshold I a ⊔ earlier) F) :=
  measurable_filter_function _ I.weight (fun s => GraphRank.gain (GraphRank.ofEdges s ⊔ earlier) F)

theorem gain_intervalIntegrable (I : Instance V) (earlier F : SimpleGraph V) (a b : ℝ) :
    IntervalIntegrable (fun t => GraphRank.gain (threshold I t ⊔ earlier) F) volume a b := by
  have hi : IntegrableOn (fun t => GraphRank.gain (threshold I t ⊔ earlier) F) (Set.uIcc a b) :=
    IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
      (gain_measurable I earlier F).aestronglyMeasurable
      (Fintype.card V) (Filter.Eventually.of_forall (fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (GraphRank.gain_nonneg _ _)]
        exact gain_le_card _ _))
  exact intervalIntegrable_iff.mpr
    (hi.mono_set Set.uIoc_subset_uIcc)

noncomputable def benefitWith (I : Instance V) (earlier : SimpleGraph V) (Y : Finset V) : ℝ :=
  ∫ a in (0 : ℝ)..horizon I, GraphRank.gain (threshold I a ⊔ earlier) (Network.completeOn Y)

noncomputable def benefit (I : Instance V) (Y : Finset V) : ℝ :=
  benefitWith I ⊥ Y

theorem benefitWith_nonneg (I : Instance V) (earlier : SimpleGraph V) (Y : Finset V) :
    0 ≤ benefitWith I earlier Y :=
  intervalIntegral.integral_nonneg (horizon_pos I).le
    (fun _ _ => GraphRank.gain_nonneg _ _)

theorem benefit_nonneg (I : Instance V) (Y : Finset V) : 0 ≤ benefit I Y :=
  benefitWith_nonneg I ⊥ Y

theorem benefitWith_antitone (I : Instance V) {earlier later : SimpleGraph V}
    (h : earlier ≤ later) (Y : Finset V) :
    benefitWith I later Y ≤ benefitWith I earlier Y := by
  apply intervalIntegral.integral_mono_on (horizon_pos I).le
    (gain_intervalIntegrable I later _ _ _) (gain_intervalIntegrable I earlier _ _ _)
  intro a _
  exact GraphRank.gain_antitone (sup_le_sup_left h _) _

theorem benefitWith_le_benefit (I : Instance V) (earlier : SimpleGraph V) (Y : Finset V) :
    benefitWith I earlier Y ≤ benefit I Y :=
  benefitWith_antitone I bot_le Y

def OneCenterNetwork (Y : Finset V) (G : SimpleGraph V) : Prop :=
  Network.Feasible Y G ∧ ∃ U : Finset V, U.card ≤ 1 ∧ Network.TerminalOnly (Y ∪ U) G

theorem completeOn_oneCenter (Y : Finset V) : OneCenterNetwork Y (Network.completeOn Y) := by
  refine ⟨Network.completeOn_feasible Y, ∅, by simp, ?_⟩
  simpa only [Finset.union_empty] using Network.completeOn_terminalOnly Y

noncomputable def localCost (I : Instance V) (Y : Finset V) : ℝ :=
  Network.minimum I.weight (OneCenterNetwork Y) ⟨_, completeOn_oneCenter Y⟩

theorem localCost_attained (I : Instance V) (Y : Finset V) :
    ∃ G, OneCenterNetwork Y G ∧ GraphCost.cost I.weight G = localCost I Y :=
  Network.minimum_attained _ _ _

theorem localCost_le (I : Instance V) (Y : Finset V) (G : SimpleGraph V)
    (hG : OneCenterNetwork Y G) : localCost I Y ≤ GraphCost.cost I.weight G :=
  Network.minimum_le _ _ _ G hG

theorem localCost_nonneg (I : Instance V) (Y : Finset V) : 0 ≤ localCost I Y :=
  Network.minimum_nonneg _ _ _ I.weight_nonneg

noncomputable def component (I : Instance V) (a : ℝ) (x : V) : Finset V :=
  I.terminals.filter (fun y => (threshold I a).Reachable x y)

noncomputable def components (I : Instance V) (a : ℝ) : Finset (Finset V) :=
  I.terminals.image (component I a)

theorem mem_component (I : Instance V) (a : ℝ) (x y : V) :
    y ∈ component I a x ↔ y ∈ I.terminals ∧ (threshold I a).Reachable x y := by
  classical
  exact Finset.mem_filter

theorem component_self (I : Instance V) (a : ℝ) {x : V} (hx : x ∈ I.terminals) :
    x ∈ component I a x :=
  (mem_component I a x x).mpr ⟨hx, SimpleGraph.Reachable.refl x⟩

theorem component_eq_of_reachable (I : Instance V) (a : ℝ) {x y : V}
    (hxy : (threshold I a).Reachable x y) : component I a x = component I a y := by
  ext z
  rw [mem_component, mem_component]
  exact and_congr_right (fun _ => ⟨fun h => hxy.symm.trans h, fun h => hxy.trans h⟩)

theorem components_nonempty (I : Instance V) (a : ℝ) {C : Finset V}
    (hC : C ∈ components I a) : C.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hC
  exact ⟨x, component_self I a hx⟩

noncomputable def row (I : Instance V) (a : ℝ) (v : V) : Finset (Finset V) :=
  (components I a).filter (fun C => ∃ x ∈ C, I.distance v x ≤ 3 * a / 5)

noncomputable def eligible (I : Instance V) (a : ℝ) : Finset V :=
  Finset.univ.filter (fun v => 3 ≤ (row I a v).card)

noncomputable def rowSaving (I : Instance V) (a : ℝ) : ℝ :=
  saving (eligible I a) (row I a) (components I a)

noncomputable def localAdvantage (I : Instance V) (C : Finset V) : ℝ :=
  (insert 0 ((C.powerset.filter (fun Y => 2 ≤ Y.card ∧ Y.card ≤ 4)).image
    (fun Y => max (benefit I Y - localCost I Y) 0))).max' (by simp)

theorem localAdvantage_nonneg (I : Instance V) (C : Finset V) :
    0 ≤ localAdvantage I C := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem localAdvantage_witness (I : Instance V) (C Y : Finset V)
    (hY : Y ⊆ C) (h2 : 2 ≤ Y.card) (h4 : Y.card ≤ 4) :
    benefit I Y - localCost I Y ≤ localAdvantage I C := by
  classical
  unfold localAdvantage
  apply (le_max_left (benefit I Y - localCost I Y) (0 : ℝ)).trans
  apply Finset.le_max'
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  refine ⟨Y, ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hY, h2, h4⟩

structure Grid where
  intervals : ℕ
  scale : Fin (intervals + 1) → ℝ
  positive : ∀ i, 0 < scale i
  ratio : ∀ i : Fin intervals, scale i.succ = omega * scale i.castSucc

noncomputable def terminalDistances (I : Instance V) : Finset ℝ :=
  ((I.terminals.product I.terminals).filter (fun xy => xy.1 ≠ xy.2)).image
    (fun xy => I.distance xy.1 xy.2)

noncomputable def minimumTerminalDistance (I : Instance V) : ℝ :=
  if h : (terminalDistances I).Nonempty then (terminalDistances I).min' h else 0

def Grid.Covers (g : Grid) (I : Instance V) : Prop :=
  g.scale 0 < minimumTerminalDistance I / 2 ∧
    2 * TreeGeometry.terminalDiameter I < g.scale (Fin.last g.intervals)

noncomputable def gamma (I : Instance V) (g : Grid) : ℝ :=
  ∑ i, g.scale i * rowSaving I (g.scale i)

noncomputable def lambda (I : Instance V) (g : Grid) : ℝ :=
  ∑ i, g.scale i * ((components I (g.scale i)).filter
    (fun C => sigma0 * g.scale i ≤ localAdvantage I C)).card

theorem gamma_nonneg (I : Instance V) (g : Grid) : 0 ≤ gamma I g :=
  Finset.sum_nonneg fun i _ => mul_nonneg (g.positive i).le (saving_nonneg _ _ _)

theorem lambda_nonneg (I : Instance V) (g : Grid) : 0 ≤ lambda I g :=
  Finset.sum_nonneg fun i _ => mul_nonneg (g.positive i).le (Nat.cast_nonneg _)

end SteinerUpperBound.Structural
