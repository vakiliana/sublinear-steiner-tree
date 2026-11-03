module

public import SteinerUpperBound.Covers.Geometry.BandSoundnessScale

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry.BandSoundness

open SteinerLowerBound MeasureTheory
open scoped Classical BigOperators Interval
open BandCompleteness

theorem list_sum_mono {A : Type*} (l : List A) (f g : A → ℝ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    exact add_le_add (h x List.mem_cons_self)
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem ordered_band_integrals {A : Type*} (f : ℝ → ℝ)
    (hI : ∀ lo hi, IntervalIntegrable f volume lo hi) (hf : ∀ t, 0 ≤ f t)
    (lo hi : A → ℝ) (l : List A)
    (hsep : l.Pairwise (fun s t => hi s ≤ lo t))
    (hband : ∀ s ∈ l, lo s ≤ hi s)
    (lower upper : ℝ) (hlu : lower ≤ upper)
    (hlower : ∀ s ∈ l, lower ≤ lo s) (hupper : ∀ s ∈ l, hi s ≤ upper) :
    (l.map (fun s => ∫ t in (lo s)..(hi s), f t)).sum ≤
      ∫ t in lower..upper, f t := by
  induction l generalizing lower with
  | nil =>
    simpa using intervalIntegral.integral_nonneg hlu (fun t _ => hf t)
  | cons s l ih =>
    obtain ⟨hs, hl⟩ := List.pairwise_cons.mp hsep
    have htail := ih hl (fun t ht => hband t (List.mem_cons_of_mem _ ht))
      (hi s) (hupper s List.mem_cons_self)
      (fun t ht => hs t ht) (fun t ht => hupper t (List.mem_cons_of_mem _ ht))
    have hgap : 0 ≤ ∫ t in lower..(lo s), f t :=
      intervalIntegral.integral_nonneg (hlower s List.mem_cons_self) (fun t _ => hf t)
    have h₁ := intervalIntegral.integral_add_adjacent_intervals (hI lower (lo s)) (hI (lo s) (hi s))
    have h₂ := intervalIntegral.integral_add_adjacent_intervals (hI lower (hi s)) (hI (hi s) upper)
    simp only [List.map_cons, List.sum_cons]
    linarith

variable {V : Type*} [Fintype V]

def Separated {I : Instance V} (s t : ScaleData I) : Prop := s.a < bandTau * t.a

noncomputable def listLinks (I : Instance V) : List (ScaleData I) → SimpleGraph V
  | [] => ⊥
  | s :: l => scaleLinks I s ⊔ listLinks I l

noncomputable def listNetworks (I : Instance V) : List (ScaleData I) → SimpleGraph V
  | [] => ⊥
  | s :: l => scaleNetworks I s ⊔ listNetworks I l

theorem le_listLinks (I : Instance V) (l : List (ScaleData I))
    {s : ScaleData I} (hs : s ∈ l) : scaleLinks I s ≤ listLinks I l := by
  induction l with
  | nil => simp at hs
  | cons t l ih =>
    rcases List.mem_cons.mp hs with rfl | hs
    · exact le_sup_left
    · exact (ih hs).trans le_sup_right

theorem listLinks_terminalOnly (I : Instance V) (l : List (ScaleData I)) :
    Network.TerminalOnly I.terminals (listLinks I l) := by
  induction l with
  | nil => exact Network.bot_terminalOnly _
  | cons s l ih =>
    intro x y hxy
    rcases hxy with hxy | hxy
    · exact scaleLinks_terminalOnly I s x y hxy
    · exact ih x y hxy

theorem listNetworks_connect (I : Instance V) (l : List (ScaleData I)) :
    ∀ x y, (listLinks I l).Adj x y → (listNetworks I l).Reachable x y := by
  induction l with
  | nil => intro x y h; exact h.elim
  | cons s l ih =>
    intro x y hxy
    rcases hxy with hxy | hxy
    · exact (scaleNetworks_connect I s x y hxy).mono le_sup_left
    · exact (ih x y hxy).mono le_sup_right

theorem listNetworks_cost (I : Instance V) (l : List (ScaleData I)) :
    GraphCost.cost I.weight (listNetworks I l) ≤
      (l.map (fun s => GraphCost.cost I.weight (scaleNetworks I s))).sum := by
  induction l with
  | nil => simp only [listNetworks, Network.cost_bot, List.map_nil, List.sum_nil, le_refl]
  | cons s l ih =>
    exact (Network.cost_sup_le I.weight I.weight_nonneg _ _).trans
      (by simpa only [List.map_cons, List.sum_cons] using
        add_le_add (le_refl (GraphCost.cost I.weight (scaleNetworks I s))) ih)

theorem list_band_charging (I : Instance V) (l : List (ScaleData I))
    (hsep : l.Pairwise Separated) (M : ℝ) (hM : 0 ≤ M)
    (hscales : ∀ s ∈ l, s.a ≤ M) :
    (l.map (scaleScore I)).sum +
        (l.map (fun s => GraphCost.cost I.weight (scaleNetworks I s))).sum ≤
      ∫ t in (0 : ℝ)..M, GraphRank.gain (Structural.threshold I t) (listLinks I l) := by
  let f : ℝ → ℝ := fun t => GraphRank.gain (Structural.threshold I t) (listLinks I l)
  have hI : ∀ lo hi, IntervalIntegrable f volume lo hi := by
    intro lo hi
    change IntervalIntegrable
      (fun t => GraphRank.gain (Structural.threshold I t) (listLinks I l)) volume lo hi
    simpa only [sup_bot_eq] using Structural.gain_intervalIntegrable I ⊥ (listLinks I l) lo hi
  have hf : ∀ t, 0 ≤ f t := fun _ => GraphRank.gain_nonneg _ _
  have hband (s : ScaleData I) : bandTau * s.a ≤ s.a - 2 * s.rho :=
    (band_parameters s.a s.rho s.positive s.rho_nonneg s.rho_small).2.2.1
  have hbandsep : l.Pairwise (fun s t => s.a - 2 * s.rho ≤ bandTau * t.a) := by
    apply List.Pairwise.imp_of_mem (p := hsep)
    intro s t _ _ hst
    change s.a < bandTau * t.a at hst
    linarith [s.rho_nonneg]
  have hpoint (s : ScaleData I) (hs : s ∈ l) :
      scaleScore I s + GraphCost.cost I.weight (scaleNetworks I s) ≤
        ∫ t in (bandTau * s.a)..(s.a - 2 * s.rho), f t := by
    apply (scale_score_cost_le_band I s).trans
    apply intervalIntegral.integral_mono_on (hband s)
      (by
        simpa only [sup_bot_eq] using
          Structural.gain_intervalIntegrable I ⊥ (scaleLinks I s) _ _) (hI _ _)
    intro t _
    exact GraphRank.gain_mono_right (Structural.threshold I t) (le_listLinks I l hs)
  have hsum := list_sum_mono l
    (fun s => scaleScore I s + GraphCost.cost I.weight (scaleNetworks I s))
    (fun s => ∫ t in (bandTau * s.a)..(s.a - 2 * s.rho), f t) hpoint
  have he : (l.map (fun s => scaleScore I s + GraphCost.cost I.weight (scaleNetworks I s))).sum =
      (l.map (scaleScore I)).sum +
        (l.map (fun s => GraphCost.cost I.weight (scaleNetworks I s))).sum := by
    clear hsep hM hscales hI hf hband hbandsep hpoint hsum
    induction l with
    | nil => simp
    | cons s l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [he] at hsum
  exact hsum.trans (ordered_band_integrals f hI hf (fun s => bandTau * s.a)
    (fun s => s.a - 2 * s.rho) l hbandsep (fun s _ => hband s) 0 M hM
    (fun s _ => (band_parameters s.a s.rho s.positive s.rho_nonneg s.rho_small).2.1)
    (fun s hs => by linarith [hscales s hs, s.rho_nonneg]))

/-- Exact soundness for separated actual bands, using one global union network
and disjoint integration intervals, with no marginal telescoping assumption. -/
theorem separated_sound (I : Instance V) (l : List (ScaleData I))
    (hsep : l.Pairwise Separated) :
    (l.map (scaleScore I)).sum ≤ I.mst - I.optimum := by
  classical
  let M := Structural.horizon I + ∑ s ∈ l.toFinset, s.a
  have hsum0 : 0 ≤ ∑ s ∈ l.toFinset, s.a :=
    Finset.sum_nonneg (fun s _ => s.positive.le)
  have hHM : Structural.horizon I ≤ M := by dsimp [M]; linarith
  have hM : 0 ≤ M := (Structural.horizon_pos I).le.trans hHM
  have hscales (s : ScaleData I) (hs : s ∈ l) : s.a ≤ M := by
    have hh := Finset.single_le_sum (fun t (_ : t ∈ l.toFinset) => t.positive.le)
      (List.mem_toFinset.mpr hs)
    dsimp [M]
    linarith [Structural.horizon_pos I]
  have hc := list_band_charging I l hsep M hM hscales
  have hcost := listNetworks_cost I l
  have hlift := Network.integral_lifting I (listLinks I l) (listNetworks I l)
    (listLinks_terminalOnly I l) (listNetworks_connect I l) M hM
    (fun e he => (Structural.weight_le_horizon I e he).trans hHM)
  simp_rw [← Structural.threshold_eq_below] at hlift
  linarith

end SteinerUpperBound.Covers.Geometry.BandSoundness
