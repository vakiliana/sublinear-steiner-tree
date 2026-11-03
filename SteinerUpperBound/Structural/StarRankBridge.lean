module

public import SteinerUpperBound.Structural.Statistics
public import SteinerUpperBound.SavingSoundness.PortList
public import SteinerUpperBound.SavingSoundness.SupportRank
public import SteinerUpperBound.SetSystem.Rank

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators
open SavingSoundness

variable {V W R : Type*}

theorem graph_map_sup (G H : SimpleGraph V) (f : V → W) :
    (G ⊔ H).map f = G.map f ⊔ H.map f := by
  ext x y
  simp only [SimpleGraph.map_adj', SimpleGraph.sup_adj]
  aesop

theorem graph_map_bot (f : V → W) : (⊥ : SimpleGraph V).map f = ⊥ := by
  ext x y
  simp only [SimpleGraph.map_adj', SimpleGraph.bot_adj, false_and, and_false,
    exists_false, false_iff]

theorem graph_map_completeOn [DecidableEq W] (Y : Finset V) (f : V → W) :
    (Network.completeOn Y).map f = Network.completeOn (Y.image f) := by
  classical
  ext x y
  rw [SimpleGraph.map_adj', Network.completeOn_adj]
  constructor
  · rintro ⟨hne, a, b, hab, rfl, rfl⟩
    obtain ⟨_, ha, hb⟩ := (Network.completeOn_adj _ _ _).mp hab
    exact ⟨hne, Finset.mem_image.mpr ⟨a, ha, rfl⟩, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
  · rintro ⟨hne, hx, hy⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨hne, a, b, (Network.completeOn_adj _ _ _).mpr
      ⟨fun h => hne (congrArg f h), ha, hb⟩, rfl, rfl⟩

theorem graph_map_portList [DecidableEq W] (f : V → W) (l : List (R × Finset V)) :
    (portGraphList l).map f =
      portGraphList (l.map (fun e => (e.1, e.2.image f))) := by
  induction l with
  | nil => exact graph_map_bot f
  | cons e l ih =>
    simp only [portGraphList_cons, List.map_cons, graph_map_sup, graph_map_completeOn, ih]

theorem portList_terminalOnly (T : Finset V) (l : List (R × Finset V))
    (h : ∀ e ∈ l, e.2 ⊆ T) : Network.TerminalOnly T (portGraphList l) := by
  induction l with
  | nil => exact Network.bot_terminalOnly T
  | cons e l ih =>
    intro x y hxy
    rcases hxy with hxy | hxy
    · obtain ⟨_, hx, hy⟩ := (Network.completeOn_adj _ _ _).mp hxy
      exact ⟨h e (by simp) hx, h e (by simp) hy⟩
    · exact ih (fun e he => h e (List.mem_cons_of_mem _ he)) x y hxy

variable [Fintype V]

noncomputable def componentTerminals (I : Instance V) (G : SimpleGraph V)
    (C : G.ConnectedComponent) : Finset V :=
  C.supp.toFinset ∩ I.terminals

theorem componentTerminals_mk (I : Instance V) (a : ℝ) (x : V) :
    componentTerminals I (threshold I a) ((threshold I a).connectedComponentMk x) =
      component I a x := by
  ext y
  simp only [componentTerminals, Finset.mem_inter, Set.mem_toFinset,
    SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq, mem_component]
  exact ⟨fun h => ⟨h.2, h.1.symm⟩, fun h => ⟨h.2.symm, h.1⟩⟩

theorem threshold_port_gain_eq (I : Instance V) (a : ℝ) (l : List (R × Finset V))
    (hT : ∀ e ∈ l, e.2 ⊆ I.terminals) :
    GraphRank.gain (threshold I a) (portGraphList l) =
      (GraphRank.rank (portGraphList (l.map (fun e => (e.1, e.2.image (component I a))))) : ℝ) := by
  classical
  let G := threshold I a
  let H := portGraphList l
  let f := G.connectedComponentMk
  let q := componentTerminals I G
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hsurj : Function.Surjective f := by
    intro C
    obtain ⟨x, hx⟩ := C.exists_rep
    exact ⟨x, hx⟩
  have hfibers : ∀ x y, G.Reachable x y ↔ f x = f y :=
    fun _ _ => SimpleGraph.ConnectedComponent.eq.symm
  have hHT : Network.TerminalOnly I.terminals H := portList_terminalOnly _ l hT
  have hnonempty : ∀ C ∈ (H.map f).support, (q C).Nonempty := by
    intro C hC
    obtain ⟨D, hCD⟩ := hC
    obtain ⟨_, x, y, hxy, hx, _⟩ := (SimpleGraph.map_adj' f H C D).mp hCD
    refine ⟨x, Finset.mem_inter.mpr ⟨?_, (hHT x y hxy).1⟩⟩
    exact Set.mem_toFinset.mpr ((C.mem_supp_iff x).mpr hx)
  have hinj : Set.InjOn q (H.map f).support := by
    intro C hC D hD he
    obtain ⟨x, hxC⟩ := hnonempty C hC
    have hxD : x ∈ q D := by rw [← he]; exact hxC
    have hCx : G.connectedComponentMk x = C :=
      (C.mem_supp_iff x).mp (Set.mem_toFinset.mp (Finset.mem_inter.mp hxC).1)
    have hDx : G.connectedComponentMk x = D :=
      (D.mem_supp_iff x).mp (Set.mem_toFinset.mp (Finset.mem_inter.mp hxD).1)
    exact hCx.symm.trans hDx
  have hfun : q ∘ f = component I a := by
    funext x
    exact componentTerminals_mk I a x
  have hmap : (H.map f).map q =
      portGraphList (l.map (fun e => (e.1, e.2.image (component I a)))) := by
    rw [SimpleGraph.map_map, hfun]
    exact graph_map_portList _ l
  have hrank := SavingSoundness.rank_map_eq_of_injOn_support (H.map f) q hinj
  rw [hmap] at hrank
  exact (SetSystem.quotient_gain G H f hsurj hfibers).trans
    (congrArg (fun n : ℕ => (n : ℝ)) hrank.symm)

theorem star_events_le_rowSaving (I : Instance V) (a : ℝ) (l : List (V × Finset V))
    (hT : ∀ e ∈ l, e.2 ⊆ I.terminals)
    (hsound : ∀ e ∈ l, e.1 ∈ eligible I a ∧
      e.2.image (component I a) ⊆ components I a ∩ row I a e.1)
    (hrank : 2 * (l.length : ℝ) ≤ GraphRank.gain (threshold I a) (portGraphList l)) :
    (l.length : ℝ) ≤ rowSaving I a := by
  have hh := SavingSoundness.port_rank_saving_list (eligible I a) (row I a) (components I a)
    (l.map (fun e => (e.1, e.2.image (component I a)))) (by
      intro e he
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      have hs := hsound e' he'
      refine ⟨hs.1, ?_⟩
      intro C hC
      have hC' : C ∈ e'.2.image (component I a) := by
        simpa only [Finset.mem_image] using hC
      simpa only [Finset.mem_inter] using hs.2 hC')
  rw [threshold_port_gain_eq I a l hT] at hrank
  simp only [List.length_map] at hh
  change _ ≤ rowSaving I a at hh
  linarith

end SteinerUpperBound.Structural
