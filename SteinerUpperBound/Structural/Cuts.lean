module

public import SteinerUpperBound.Structural.Statistics

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators
open MeasureTheory

variable {V : Type*} [Fintype V]

def ClosedCut (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ x y, G.Adj x y → (x ∈ S ↔ y ∈ S)

theorem ClosedCut.reachable {G : SimpleGraph V} {S : Set V}
    (h : ClosedCut G S) {x y : V} (hxy : G.Reachable x y) :
    x ∈ S ↔ y ∈ S := by
  obtain ⟨w⟩ := hxy
  induction w with
  | nil => exact Iff.rfl
  | @cons a b c hab w ih => exact (h a b hab).trans ih

theorem ClosedCut.not_reachable {G : SimpleGraph V} {S : Set V}
    (h : ClosedCut G S) {x y : V} (hx : x ∈ S) (hy : y ∉ S) :
    ¬ G.Reachable x y :=
  fun hxy => hy ((h.reachable hxy).mp hx)

theorem ClosedCut.sup {G H : SimpleGraph V} {S : Set V}
    (hG : ClosedCut G S) (hH : ClosedCut H S) : ClosedCut (G ⊔ H) S := by
  intro x y h
  exact h.elim (hG x y) (hH x y)

theorem reachable_cut_closed (G : SimpleGraph V) (z : V) :
    ClosedCut G {x | G.Reachable z x} := by
  intro x y hxy
  exact ⟨fun h => h.trans hxy.reachable, fun h => h.trans hxy.symm.reachable⟩

theorem closedCut_edge_of_outside (G : SimpleGraph V) (z x y : V)
    (hx : ¬ G.Reachable z x) (hy : ¬ G.Reachable z y) :
    ClosedCut (SimpleGraph.edge x y) {v | G.Reachable z v} := by
  intro a b hab
  rcases (SimpleGraph.edge_adj x y a b).mp hab with ⟨h | h, _⟩
  · rcases h with ⟨rfl, rfl⟩
    exact iff_of_false hx hy
  · rcases h with ⟨rfl, rfl⟩
    exact iff_of_false hy hx

theorem gain_ge_one (G : SimpleGraph V) (Y : Finset V) {x y : V}
    (hx : x ∈ Y) (hy : y ∈ Y) (hxy : ¬ G.Reachable x y) :
    1 ≤ GraphRank.gain G (Network.completeOn Y) := by
  have hne : x ≠ y := fun h => hxy (h ▸ SimpleGraph.Reachable.refl x)
  have he : SimpleGraph.edge x y ≤ Network.completeOn Y := by
    intro a b hab
    rcases (SimpleGraph.edge_adj x y a b).mp hab with ⟨h | h, _⟩
    · rcases h with ⟨rfl, rfl⟩
      exact (Network.completeOn_adj _ _ _).mpr ⟨hne, hx, hy⟩
    · rcases h with ⟨rfl, rfl⟩
      exact (Network.completeOn_adj _ _ _).mpr ⟨hne.symm, hy, hx⟩
  have hr := GraphRank.rank_mono (sup_le_sup_left he G)
  rw [GraphRank.rank_add_edge G x y hxy] at hr
  have hrR : (GraphRank.rank G : ℝ) + 1 ≤
      GraphRank.rank (G ⊔ Network.completeOn Y) := by exact_mod_cast hr
  unfold GraphRank.gain
  linarith

theorem gain_ge_two (G : SimpleGraph V) (Y : Finset V) {x y z : V}
    (hx : x ∈ Y) (hy : y ∈ Y) (hz : z ∈ Y)
    (hxy : ¬ G.Reachable x y) (hzx : ¬ G.Reachable z x) (hzy : ¬ G.Reachable z y) :
    2 ≤ GraphRank.gain G (Network.completeOn Y) := by
  have he x y (hx : x ∈ Y) (hy : y ∈ Y) :
      SimpleGraph.edge x y ≤ Network.completeOn Y := by
    intro a b hab
    rcases (SimpleGraph.edge_adj x y a b).mp hab with ⟨h | h, hne⟩
    · rcases h with ⟨rfl, rfl⟩
      exact (Network.completeOn_adj _ _ _).mpr ⟨hne, hx, hy⟩
    · rcases h with ⟨rfl, rfl⟩
      exact (Network.completeOn_adj _ _ _).mpr ⟨hne, hy, hx⟩
  have hcut := (reachable_cut_closed G z).sup (closedCut_edge_of_outside G z x y hzx hzy)
  have hzy' : ¬ (G ⊔ SimpleGraph.edge x y).Reachable z y :=
    hcut.not_reachable (SimpleGraph.Reachable.refl z) hzy
  have hr := GraphRank.rank_mono
    (show (G ⊔ SimpleGraph.edge x y) ⊔ SimpleGraph.edge z y ≤
        G ⊔ Network.completeOn Y from
      sup_le (sup_le le_sup_left ((he x y hx hy).trans le_sup_right))
        ((he z y hz hy).trans le_sup_right))
  rw [GraphRank.rank_add_edge _ z y hzy', GraphRank.rank_add_edge G x y hxy] at hr
  have hrR : (GraphRank.rank G : ℝ) + 2 ≤
      GraphRank.rank (G ⊔ Network.completeOn Y) := by exact_mod_cast hr
  unfold GraphRank.gain
  linarith

theorem threshold_closedCut (I : Instance V) (S : Set V) (r a : ℝ) (ha : a ≤ r)
    (hbar : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals,
      x ∈ S → y ∉ S → r ≤ I.distance x y) :
    ClosedCut (threshold I a) S := by
  intro x y hxy
  obtain ⟨_, hx, hy, hd⟩ := (threshold_adj I a x y).mp hxy
  constructor
  · intro hxS
    by_contra hyS
    linarith [hbar x hx y hy hxS hyS]
  · intro hyS
    by_contra hxS
    have hh := hbar y hy x hx hyS hxS
    rw [I.distance_comm y x] at hh
    linarith

theorem threshold_sup_closedCut (I : Instance V) (earlier : SimpleGraph V)
    (S : Set V) (r a : ℝ) (ha : a ≤ r)
    (hbar : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals,
      x ∈ S → y ∉ S → r ≤ I.distance x y)
    (he : ClosedCut earlier S) : ClosedCut (threshold I a ⊔ earlier) S :=
  (threshold_closedCut I S r a ha hbar).sup he

theorem benefit_three_ports (I : Instance V) (earlier : SimpleGraph V)
    (Y : Finset V) {x y z : V} (hx : x ∈ Y) (hy : y ∈ Y) (hz : z ∈ Y)
    (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (haM : a ≤ horizon I)
    (hxy : ∀ t ∈ Set.Icc 0 b, ¬ (threshold I t ⊔ earlier).Reachable x y)
    (hzx : ∀ t ∈ Set.Icc 0 a, ¬ (threshold I t ⊔ earlier).Reachable z x)
    (hzy : ∀ t ∈ Set.Icc 0 a, ¬ (threshold I t ⊔ earlier).Reachable z y) :
    a + b ≤ benefitWith I earlier Y := by
  let f := fun t => GraphRank.gain (threshold I t ⊔ earlier) (Network.completeOn Y)
  have hf u v : IntervalIntegrable f volume u v := gain_intervalIntegrable I earlier _ u v
  have h1 : 2 * b ≤ ∫ t in (0 : ℝ)..b, f t := by
    calc
      _ = ∫ _t in (0 : ℝ)..b, (2 : ℝ) := by simp; ring
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on hb intervalIntegrable_const (hf _ _)
        intro t ht
        have hta : t ∈ Set.Icc 0 a := ⟨ht.1, ht.2.trans hba⟩
        exact gain_ge_two _ Y hx hy hz (hxy t ht) (hzx t hta) (hzy t hta)
  have h2 : a - b ≤ ∫ t in b..a, f t := by
    calc
      _ = ∫ _t in b..a, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on hba intervalIntegrable_const (hf _ _)
        intro t ht
        exact gain_ge_one _ Y hz hx (hzx t ⟨hb.trans ht.1, ht.2⟩)
  have h3 : 0 ≤ ∫ t in a..horizon I, f t :=
    intervalIntegral.integral_nonneg haM (fun t _ => GraphRank.gain_nonneg _ _)
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals (hf 0 b) (hf b a)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (hf 0 a) (hf a (horizon I))
  change a + b ≤ ∫ t in (0 : ℝ)..horizon I, f t
  linarith

end SteinerUpperBound.Structural
