module

public import SteinerUpperBound.GraphRank
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace SteinerUpperBound.SetSystem

open scoped Classical BigOperators

variable {V W : Type*}

theorem space_eq_of_reachable [Fintype V] (G H : SimpleGraph V)
    (h : ∀ x y, G.Reachable x y ↔ H.Reachable x y) :
    GraphRank.space G = GraphRank.space H := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x, y, hxy, rfl⟩
    exact GraphRank.reachable_mem H ((h x y).mp hxy.reachable)
  · apply Submodule.span_le.mpr
    rintro z ⟨x, y, hxy, rfl⟩
    exact GraphRank.reachable_mem G ((h x y).mpr hxy.reachable)

theorem rank_eq_of_reachable [Fintype V] (G H : SimpleGraph V)
    (h : ∀ x y, G.Reachable x y ↔ H.Reachable x y) :
    GraphRank.rank G = GraphRank.rank H := by
  unfold GraphRank.rank
  rw [space_eq_of_reachable G H h]

theorem forest_rank_ofEdges [Fintype V] (s : Finset (Sym2 V))
    (hnondiag : ∀ e ∈ s, ¬e.IsDiag) (hforest : (GraphRank.ofEdges s).IsAcyclic) :
    GraphRank.rank (GraphRank.ofEdges s) = s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [GraphRank.ofEdges_empty, GraphRank.rank_bot, Finset.card_empty]
  | @insert e s he ih =>
      have hsmall : (GraphRank.ofEdges s).IsAcyclic :=
        hforest.anti (by rw [GraphRank.ofEdges_insert]; exact le_sup_left)
      have hr := ih (fun a ha => hnondiag a (Finset.mem_insert_of_mem ha)) hsmall
      induction e using Sym2.inductionOn with
      | _ x y =>
          have hxy : x ≠ y := by
            intro h
            apply hnondiag (Sym2.mk x y) (Finset.mem_insert_self _ _)
            simp [h]
          have hnadj : ¬(GraphRank.ofEdges s).Adj x y := by
            intro h
            exact he (((SimpleGraph.fromEdgeSet_adj (s : Set (Sym2 V))).mp h).1)
          have hnreach : ¬(GraphRank.ofEdges s).Reachable x y := by
            intro h
            rw [GraphRank.ofEdges_insert] at hforest
            rcases (SimpleGraph.isAcyclic_sup_fromEdgeSet_iff.mp hforest).2 h with h | h
            · exact hxy h
            · exact hnadj h
          rw [GraphRank.ofEdges_insert]
          change GraphRank.rank (GraphRank.ofEdges s ⊔ SimpleGraph.edge x y) = _
          rw [GraphRank.rank_add_edge (GraphRank.ofEdges s) x y hnreach,
            hr, Finset.card_insert_of_notMem he]

theorem forest_rank [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
    GraphRank.rank G = Nat.card G.edgeSet := by
  classical
  have hr := forest_rank_ofEdges G.edgeFinset
    (fun e he => G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he))
    (by simpa only [GraphRank.ofEdges_edgeFinset] using hG)
  rw [GraphRank.ofEdges_edgeFinset] at hr
  exact hr.trans (SteinerLowerBound.GraphCost.edgeCount_eq_card G).symm

noncomputable def componentEquiv (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V → W) (hsurj : Function.Surjective f)
    (hreach : ∀ x y, G.Reachable x y ↔ H.Reachable (f x) (f y)) :
    G.ConnectedComponent ≃ H.ConnectedComponent := by
  let q : G.ConnectedComponent → H.ConnectedComponent :=
    Quot.lift (fun x => H.connectedComponentMk (f x))
      (fun x y h => SimpleGraph.ConnectedComponent.sound ((hreach x y).mp h))
  apply Equiv.ofBijective q
  constructor
  · intro c d
    refine SimpleGraph.ConnectedComponent.ind₂ (fun x y => ?_) c d
    intro h
    apply SimpleGraph.ConnectedComponent.sound
    exact (hreach x y).mpr (SimpleGraph.ConnectedComponent.exact h)
  · intro c
    refine SimpleGraph.ConnectedComponent.ind (fun y => ?_) c
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨G.connectedComponentMk x, rfl⟩

theorem reachable_map (G : SimpleGraph V) (f : V → W) {x y : V}
    (h : G.Reachable x y) : (G.map f).Reachable (f x) (f y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z hxy p ih =>
      by_cases he : f x = f y
      · simpa only [he] using ih
      · exact (SimpleGraph.map_adj_apply' hxy he).reachable.trans ih

theorem quotient_reachable (G F : SimpleGraph V) (f : V → W)
    (hfibers : ∀ x y, G.Reachable x y ↔ f x = f y) (x y : V) :
    (G ⊔ F).Reachable x y ↔ (F.map f).Reachable (f x) (f y) := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons x y z hxy p ih =>
        rcases hxy with hxy | hxy
        · simpa only [(hfibers x y).mp hxy.reachable] using ih
        · exact (reachable_map F f hxy.reachable).trans ih
  · intro h
    suffices hback : ∀ u v, (F.map f).Reachable u v →
        ∀ x y, f x = u → f y = v → (G ⊔ F).Reachable x y from
      hback (f x) (f y) h x y rfl rfl
    intro u v huv
    obtain ⟨p⟩ := huv
    induction p with
    | nil =>
        intro x y hx hy
        exact ((hfibers x y).mpr (hx.trans hy.symm)).mono le_sup_left
    | @cons u v w huv p ih =>
        intro x y hx hy
        obtain ⟨_, a, b, hab, hfa, hfb⟩ := (SimpleGraph.map_adj' f F u v).mp huv
        have hxa := ((hfibers x a).mpr (hx.trans hfa.symm)).mono
          (show G ≤ G ⊔ F from le_sup_left)
        exact hxa.trans ((hab.reachable.mono (show F ≤ G ⊔ F from le_sup_right)).trans
          (ih b y hfb hy))

theorem quotient_gain [Fintype V] [Fintype W] (G F : SimpleGraph V)
    (f : V → W) (hsurj : Function.Surjective f)
    (hfibers : ∀ x y, G.Reachable x y ↔ f x = f y) :
    GraphRank.gain G F = (GraphRank.rank (F.map f) : ℝ) := by
  have hbase : Nat.card G.ConnectedComponent = Nat.card W := by
    have he := Nat.card_congr (componentEquiv G (⊥ : SimpleGraph W) f hsurj
      (by intro x y; simpa using hfibers x y))
    have hb := GraphRank.rank_add_components (⊥ : SimpleGraph W)
    rw [GraphRank.rank_bot, Nat.zero_add] at hb
    exact he.trans hb
  have hsup : Nat.card (G ⊔ F).ConnectedComponent =
      Nat.card (F.map f).ConnectedComponent :=
    Nat.card_congr (componentEquiv (G ⊔ F) (F.map f) f hsurj
      (quotient_reachable G F f hfibers))
  have hr := GraphRank.rank_add_components (F.map f)
  have hr' : (GraphRank.rank (F.map f) : ℝ) +
      Nat.card (F.map f).ConnectedComponent = Nat.card W := by exact_mod_cast hr
  rw [GraphRank.gain_components, hbase, hsup]
  linarith

end SteinerUpperBound.SetSystem
