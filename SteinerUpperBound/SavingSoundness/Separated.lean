module

public import SteinerUpperBound.SavingSoundness.Scale

@[expose] public section

namespace SteinerUpperBound.SavingSoundness

open SteinerLowerBound Covers.Geometry MeasureTheory
open scoped Classical BigOperators Interval

variable {V : Type*} [Fintype V]

structure ScaleData (I : Instance V) where
  a : ℝ
  rho : ℝ
  retained : Finset V
  positive : 0 < a
  rho_nonneg : 0 ≤ rho
  rho_small : 64 * rho ≤ a
  subset : retained ⊆ I.terminals
  cover : CoverOn I I.terminals retained rho

noncomputable def scaleLinks (I : Instance V) (s : ScaleData I) : SimpleGraph V :=
  Classical.choose (exists_scale_networks I s.retained s.a s.rho s.positive
    s.rho_nonneg s.rho_small s.cover s.subset)

noncomputable def scaleStars (I : Instance V) (s : ScaleData I) : SimpleGraph V :=
  Classical.choose (Classical.choose_spec (exists_scale_networks I s.retained s.a s.rho
    s.positive s.rho_nonneg s.rho_small s.cover s.subset))

theorem scale_spec (I : Instance V) (s : ScaleData I) :
    Network.TerminalOnly I.terminals (scaleLinks I s) ∧
      (∀ x y, (scaleLinks I s).Adj x y → (scaleStars I s).Reachable x y) ∧
      (∀ x y, (scaleLinks I s).Adj x y → I.distance x y ≤ 5 * s.a / 4) ∧
      ∀ earlier : SimpleGraph V, earlier ≤ Structural.threshold I (s.a - 2 * s.rho) →
        s.a * retainedSaving I s.retained s.a / 32 + GraphCost.cost I.weight (scaleStars I s) ≤
          integratedGain I earlier (scaleLinks I s) :=
  Classical.choose_spec (Classical.choose_spec (exists_scale_networks I s.retained s.a s.rho
    s.positive s.rho_nonneg s.rho_small s.cover s.subset))

def Separated {I : Instance V} (s t : ScaleData I) : Prop := 5 * s.a / 4 < t.a - 2 * t.rho

theorem scaleLinks_short (I : Instance V) (s t : ScaleData I) (h : Separated s t) :
    scaleLinks I s ≤ Structural.threshold I (t.a - 2 * t.rho) := by
  intro x y hxy
  have hs := scale_spec I s
  obtain ⟨hx, hy⟩ := hs.1 x y hxy
  exact (Structural.threshold_adj I _ x y).mpr
    ⟨hxy.ne, hx, hy, (hs.2.2.1 x y hxy).trans_lt h⟩

theorem integratedGain_sup (I : Instance V) (earlier F H : SimpleGraph V) :
    integratedGain I earlier (F ⊔ H) =
      integratedGain I earlier F + integratedGain I (earlier ⊔ F) H := by
  unfold integratedGain
  rw [← intervalIntegral.integral_add
    (Structural.gain_intervalIntegrable I earlier F _ _)
    (Structural.gain_intervalIntegrable I (earlier ⊔ F) H _ _)]
  apply intervalIntegral.integral_congr_ae
  exact Filter.Eventually.of_forall (fun t _ => by
    simp only [GraphRank.gain, sup_assoc]
    ring)

noncomputable def listLinks (I : Instance V) : List (ScaleData I) → SimpleGraph V
  | [] => ⊥
  | s :: l => scaleLinks I s ⊔ listLinks I l

noncomputable def listStars (I : Instance V) : List (ScaleData I) → SimpleGraph V
  | [] => ⊥
  | s :: l => scaleStars I s ⊔ listStars I l

noncomputable def scaleCharge (I : Instance V) (s : ScaleData I) : ℝ :=
  s.a * retainedSaving I s.retained s.a / 32

theorem listLinks_terminalOnly (I : Instance V) (l : List (ScaleData I)) :
    Network.TerminalOnly I.terminals (listLinks I l) := by
  induction l with
  | nil => exact Network.bot_terminalOnly _
  | cons s l ih =>
      intro x y hxy
      rcases hxy with hxy | hxy
      · exact (scale_spec I s).1 x y hxy
      · exact ih x y hxy

theorem listLinks_connect (I : Instance V) (l : List (ScaleData I)) :
    ∀ x y, (listLinks I l).Adj x y → (listStars I l).Reachable x y := by
  induction l with
  | nil => intro x y h; exact h.elim
  | cons s l ih =>
      intro x y hxy
      rcases hxy with hxy | hxy
      · exact ((scale_spec I s).2.1 x y hxy).mono le_sup_left
      · exact (ih x y hxy).mono le_sup_right

theorem listStars_cost (I : Instance V) (l : List (ScaleData I)) :
    GraphCost.cost I.weight (listStars I l) ≤
      (l.map (fun s => GraphCost.cost I.weight (scaleStars I s))).sum := by
  induction l with
  | nil => simp only [listStars, Network.cost_bot, List.map_nil, List.sum_nil, le_refl]
  | cons s l ih =>
      exact (Network.cost_sup_le I.weight I.weight_nonneg _ _).trans
        (by simpa only [List.map_cons, List.sum_cons] using
          add_le_add (le_refl (GraphCost.cost I.weight (scaleStars I s))) ih)

theorem list_charging (I : Instance V) (l : List (ScaleData I))
    (hsep : l.Pairwise Separated) (earlier : SimpleGraph V)
    (hshort : ∀ s ∈ l, earlier ≤ Structural.threshold I (s.a - 2 * s.rho)) :
    (l.map (scaleCharge I)).sum +
        (l.map (fun s => GraphCost.cost I.weight (scaleStars I s))).sum ≤
      integratedGain I earlier (listLinks I l) := by
  induction l generalizing earlier with
  | nil =>
      simpa only [List.map_nil, List.sum_nil, zero_add] using
        integratedGain_nonneg I earlier (listLinks I [])
  | cons s l ih =>
      obtain ⟨hs, hl⟩ := List.pairwise_cons.mp hsep
      have hhead := (scale_spec I s).2.2.2 earlier (hshort s List.mem_cons_self)
      have htshort : ∀ t ∈ l,
          earlier ⊔ scaleLinks I s ≤ Structural.threshold I (t.a - 2 * t.rho) := by
        intro t ht
        exact sup_le (hshort t (List.mem_cons_of_mem _ ht)) (scaleLinks_short I s t (hs t ht))
      have htail := ih hl (earlier ⊔ scaleLinks I s) htshort
      rw [listLinks, integratedGain_sup]
      simp only [List.map_cons, List.sum_cons]
      change scaleCharge I s + _ + (GraphCost.cost I.weight (scaleStars I s) + _) ≤ _
      change scaleCharge I s + _ ≤ _ at hhead
      linarith

theorem separated_sound (I : Instance V) (l : List (ScaleData I))
    (hsep : l.Pairwise Separated) :
    (l.map (fun s => s.a * retainedSaving I s.retained s.a)).sum ≤
      32 * (I.mst - I.optimum) := by
  have hc := list_charging I l hsep ⊥ (fun _ _ => bot_le)
  have hcost := listStars_cost I l
  have hlift := Network.integral_lifting I (listLinks I l) (listStars I l)
    (listLinks_terminalOnly I l) (listLinks_connect I l)
    (Structural.horizon I) (Structural.horizon_pos I).le (Structural.weight_le_horizon I)
  have he : integratedGain I ⊥ (listLinks I l) =
      ∫ t in (0 : ℝ)..Structural.horizon I,
        GraphRank.gain (TerminalMST.below I.weight I.terminals t) (listLinks I l) := by
    simp only [integratedGain, sup_bot_eq, Structural.threshold_eq_below]
  rw [← he] at hlift
  have hcharge : (l.map (scaleCharge I)).sum ≤ I.mst - I.optimum := by linarith
  have hsum : (l.map (fun s => s.a * retainedSaving I s.retained s.a)).sum =
      32 * (l.map (scaleCharge I)).sum := by
    clear hsep hc hcost hlift he hcharge
    induction l with
    | nil => simp
    | cons s l ih =>
        simp only [List.map_cons, List.sum_cons, ih, scaleCharge]
        ring
  rw [hsum]
  exact mul_le_mul_of_nonneg_left hcharge (by norm_num)

end SteinerUpperBound.SavingSoundness
