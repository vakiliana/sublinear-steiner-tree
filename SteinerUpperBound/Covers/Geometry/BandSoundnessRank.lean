module

public import SteinerUpperBound.Covers.Geometry.Band
public import SteinerUpperBound.SetSystem.Rank
public import SteinerUpperBound.SavingSoundness.Graphs

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry.BandSoundness

open SteinerLowerBound
open scoped Classical BigOperators Interval
open BandCompleteness

variable {V W J : Type*}

theorem completeOn_map (Y : Finset V) (f : V → W) :
    (Network.completeOn Y).map f = Network.completeOn (Y.image f) := by
  classical
  ext x y
  constructor
  · intro h
    obtain ⟨hne, u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj' _ _ x y).mp h
    obtain ⟨_, hu, hv⟩ := (Network.completeOn_adj Y u v).mp huv
    exact (Network.completeOn_adj _ _ _).mpr
      ⟨hne, Finset.mem_image.mpr ⟨u, hu, rfl⟩, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  · intro h
    obtain ⟨hne, hx, hy⟩ := (Network.completeOn_adj _ x y).mp h
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := fun he => hne (congrArg f he)
    exact SimpleGraph.map_adj_apply'
      ((Network.completeOn_adj Y u v).mpr ⟨huv, hu, hv⟩) hne

theorem gain_clique_eq [Fintype V] (G : SimpleGraph V) (Y : Finset V) :
    GraphRank.gain G (Network.completeOn Y) =
      (((Y.image G.connectedComponentMk).card - 1 : ℕ) : ℝ) := by
  classical
  have hsurj : Function.Surjective G.connectedComponentMk :=
    fun c => ⟨GraphRank.representative G c, GraphRank.representative_component G c⟩
  have hfib : ∀ x y, G.Reachable x y ↔ G.connectedComponentMk x = G.connectedComponentMk y :=
    fun _ _ => ⟨SimpleGraph.ConnectedComponent.sound, SimpleGraph.ConnectedComponent.exact⟩
  rw [SetSystem.quotient_gain G (Network.completeOn Y) G.connectedComponentMk hsurj hfib,
    completeOn_map, GraphRank.rank_completeOn]

/-- Only the connectivity relation on the contracted witness matters. -/
theorem gain_clique_antitone_reachable [Fintype V] (G H : SimpleGraph V) (Y : Finset V)
    (hrel : ∀ x ∈ Y, ∀ y ∈ Y, G.Reachable x y → H.Reachable x y) :
    GraphRank.gain H (Network.completeOn Y) ≤ GraphRank.gain G (Network.completeOn Y) := by
  classical
  let f : G.ConnectedComponent → H.ConnectedComponent := fun c =>
    if hc : ∃ x ∈ Y, G.connectedComponentMk x = c then
      H.connectedComponentMk (Classical.choose hc)
    else H.connectedComponentMk (GraphRank.representative G c)
  have hf (x : V) (hx : x ∈ Y) :
      f (G.connectedComponentMk x) = H.connectedComponentMk x := by
    have he : ∃ y ∈ Y, G.connectedComponentMk y = G.connectedComponentMk x := ⟨x, hx, rfl⟩
    dsimp only [f]
    rw [dif_pos he]
    have h := Classical.choose_spec he
    exact SimpleGraph.ConnectedComponent.sound
      (hrel _ h.1 x hx (SimpleGraph.ConnectedComponent.exact h.2))
  have him : (Y.image G.connectedComponentMk).image f = Y.image H.connectedComponentMk := by
    rw [Finset.image_image]
    exact Finset.image_congr (fun x hx => hf x hx)
  have hcard : (Y.image H.connectedComponentMk).card ≤ (Y.image G.connectedComponentMk).card := by
    rw [← him]
    exact Finset.card_image_le
  rw [gain_clique_eq, gain_clique_eq]
  exact_mod_cast Nat.sub_le_sub_right hcard 1

theorem space_zero_off_support [Fintype V] (G : SimpleGraph V) (v : V)
    (hv : v ∉ G.support) {z : V → ℝ} (hz : z ∈ GraphRank.space G) : z v = 0 := by
  classical
  have hker := GraphRank.space_le_total_ker G ({v} : Finset V) (by
    intro x y hxy
    have hx : x ≠ v := by
      intro he
      subst x
      exact hv ⟨y, hxy⟩
    have hy : y ≠ v := by
      intro he
      subst y
      exact hv ⟨x, hxy.symm⟩
    simp [hx, hy])
  have h := hker hz
  change GraphRank.total ({v} : Finset V) z = 0 at h
  simpa [GraphRank.total] using h

theorem rank_sup_disjoint_support [Fintype V] (G H : SimpleGraph V)
    (hd : Disjoint G.support H.support) :
    GraphRank.rank (G ⊔ H) = GraphRank.rank G + GraphRank.rank H := by
  have hs : Disjoint (GraphRank.space G) (GraphRank.space H) := by
    apply disjoint_iff_inf_le.mpr
    intro z hz
    change z = 0
    ext v
    by_cases hv : v ∈ G.support
    · have hvH : v ∉ H.support := fun h => Set.disjoint_left.mp hd hv h
      exact space_zero_off_support H v hvH hz.2
    · exact space_zero_off_support G v hv hz.1
  have he : GraphRank.space G ⊓ GraphRank.space H = ⊥ :=
    le_antisymm (disjoint_iff_inf_le.mp hs) bot_le
  have hr := Submodule.finrank_sup_add_finrank_inf_eq (GraphRank.space G) (GraphRank.space H)
  rw [he] at hr
  simp only [finrank_bot, add_zero] at hr
  unfold GraphRank.rank
  rw [GraphRank.space_sup]
  exact hr

theorem finSup_adj (s : Finset J) (F : J → SimpleGraph V) (x y : V) :
    (s.sup F).Adj x y ↔ ∃ j ∈ s, (F j).Adj x y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp [Finset.sup_insert, ih]

theorem rank_finSup_disjoint [Fintype V] (s : Finset J) (F : J → SimpleGraph V)
    (hd : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (F j).support (F k).support) :
    GraphRank.rank (s.sup F) = ∑ j ∈ s, GraphRank.rank (F j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [GraphRank.rank_bot]
  | @insert j s hj ih =>
    have hds : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Disjoint (F u).support (F v).support :=
      fun u hu v hv huv => hd u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_of_mem hv) huv
    have hdj : Disjoint (F j).support (s.sup F).support := by
      apply Set.disjoint_left.mpr
      rintro x hx ⟨y, hxy⟩
      obtain ⟨k, hk, hxy⟩ := (finSup_adj s F x y).mp hxy
      have hjk : j ≠ k := fun he => hj (he ▸ hk)
      exact Set.disjoint_left.mp
        (hd j (Finset.mem_insert_self _ _) k (Finset.mem_insert_of_mem hk) hjk) hx ⟨y, hxy⟩
    rw [Finset.sup_insert, rank_sup_disjoint_support _ _ hdj, ih hds, Finset.sum_insert hj]

theorem graphUnion_eq_finSup [Fintype J] (F : J → SimpleGraph V) :
    SavingSoundness.graphUnion F = Finset.univ.sup F := by
  ext x y
  rw [SavingSoundness.graphUnion_adj, finSup_adj]
  simp

theorem graphUnion_map (F : J → SimpleGraph V) (f : V → W) :
    (SavingSoundness.graphUnion F).map f = SavingSoundness.graphUnion (fun j => (F j).map f) := by
  ext x y
  constructor
  · intro h
    obtain ⟨hne, u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj' _ _ x y).mp h
    obtain ⟨j, hj⟩ := (SavingSoundness.graphUnion_adj F u v).mp huv
    exact (SavingSoundness.graphUnion_adj _ _ _).mpr
      ⟨j, SimpleGraph.map_adj_apply' hj hne⟩
  · intro h
    obtain ⟨j, hj⟩ := (SavingSoundness.graphUnion_adj _ x y).mp h
    obtain ⟨hne, u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj' _ _ x y).mp hj
    exact SimpleGraph.map_adj_apply'
      ((SavingSoundness.graphUnion_adj _ _ _).mpr ⟨j, huv⟩) hne

theorem mapped_clique_support (Y : Finset V) (f : V → W) :
    ((Network.completeOn Y).map f).support ⊆ (Y.image f : Set W) := by
  rintro x ⟨y, hxy⟩
  rw [completeOn_map] at hxy
  exact ((Network.completeOn_adj _ x y).mp hxy).2.1

/-- Genuine additivity for disjoint quotient cliques. No rank-additivity
certificate or forest witness is assumed. -/
theorem gain_disjoint_cliques [Fintype V] [Fintype J]
    (G : SimpleGraph V) (Y : J → Finset V)
    (hd : Pairwise (fun j k => Disjoint
      ((Y j).image G.connectedComponentMk) ((Y k).image G.connectedComponentMk))) :
    GraphRank.gain G (SavingSoundness.graphUnion (fun j => Network.completeOn (Y j))) =
      ∑ j, GraphRank.gain G (Network.completeOn (Y j)) := by
  classical
  let q := G.connectedComponentMk
  have hsurj : Function.Surjective q :=
    fun c => ⟨GraphRank.representative G c, GraphRank.representative_component G c⟩
  have hfib : ∀ x y, G.Reachable x y ↔ q x = q y :=
    fun _ _ => ⟨SimpleGraph.ConnectedComponent.sound, SimpleGraph.ConnectedComponent.exact⟩
  have hsupport : ∀ j ∈ (Finset.univ : Finset J), ∀ k ∈ (Finset.univ : Finset J),
      j ≠ k → Disjoint ((Network.completeOn (Y j)).map q).support
        ((Network.completeOn (Y k)).map q).support := by
    intro j _ k _ hjk
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Finset.disjoint_left.mp (hd hjk)
      (mapped_clique_support (Y j) q hx) (mapped_clique_support (Y k) q hy)
  rw [SetSystem.quotient_gain G _ q hsurj hfib, graphUnion_map, graphUnion_eq_finSup,
    rank_finSup_disjoint _ _ hsupport, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (SetSystem.quotient_gain G (Network.completeOn (Y j)) q hsurj hfib).symm

variable [Fintype V]

theorem global_gain_ge_shifted (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hρ : 0 ≤ ρ) (a : ℝ)
    {C Y : Finset V} (hC : C ∈ componentsOn I N a) (hY : Y ⊆ C) (t : ℝ) :
    GraphRank.gain (TerminalMST.below I.weight C (t + 2 * ρ)) (Network.completeOn Y) ≤
      globalGain I Y t := by
  apply gain_clique_antitone_reachable
  intro x hx y hy hxy
  rw [below_eq_thresholdOn]
  apply bottleneck_upper I I.terminals N ρ hc hρ a hC (hY hx) (hY hy) t
  rwa [thresholdOn_terminals_eq]

end SteinerUpperBound.Covers.Geometry.BandSoundness
