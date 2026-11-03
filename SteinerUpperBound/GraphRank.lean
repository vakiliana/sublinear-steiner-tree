module

public import SteinerUpperBound.Model

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerUpperBound.GraphRank

open scoped Classical BigOperators
open Submodule

variable {V : Type*}

noncomputable def delta (x y : V) : V → ℝ :=
  Pi.single x 1 - Pi.single y 1

theorem delta_self (x : V) : delta x x = 0 := by simp [delta]

theorem delta_add (x y z : V) : delta x z = delta x y + delta y z := by
  ext v
  simp only [delta, Pi.sub_apply, Pi.add_apply]
  ring

theorem delta_neg (x y : V) : delta y x = -delta x y := by
  ext v
  simp only [delta, Pi.sub_apply, Pi.neg_apply]
  ring

noncomputable def space (G : SimpleGraph V) : Submodule ℝ (V → ℝ) :=
  Submodule.span ℝ {z | ∃ x y, G.Adj x y ∧ z = delta x y}

theorem edge_mem (G : SimpleGraph V) {x y : V} (hxy : G.Adj x y) :
    delta x y ∈ space G :=
  Submodule.subset_span ⟨x, y, hxy, rfl⟩

theorem reachable_mem (G : SimpleGraph V) {x y : V} (hxy : G.Reachable x y) :
    delta x y ∈ space G := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => simp only [delta_self]; exact (space G).zero_mem
  | @cons x y z hxy p ih =>
      rw [delta_add x y z]
      exact (space G).add_mem (edge_mem G hxy) ih

theorem space_mono {G H : SimpleGraph V} (hGH : G ≤ H) : space G ≤ space H := by
  apply Submodule.span_mono
  rintro z ⟨x, y, hxy, rfl⟩
  exact ⟨x, y, hGH hxy, rfl⟩

theorem space_sup (G H : SimpleGraph V) : space (G ⊔ H) = space G ⊔ space H := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x, y, hxy, rfl⟩
    rcases hxy with hxy | hxy
    · exact Submodule.mem_sup_left (edge_mem G hxy)
    · exact Submodule.mem_sup_right (edge_mem H hxy)
  · exact sup_le (space_mono le_sup_left) (space_mono le_sup_right)

theorem space_bot : space (⊥ : SimpleGraph V) = ⊥ := by
  have he : {z : V → ℝ | ∃ x y, (⊥ : SimpleGraph V).Adj x y ∧ z = delta x y} = ∅ := by
    ext z
    simp
  rw [space, he, Submodule.span_empty]

theorem space_edge (x y : V) :
    space (SimpleGraph.edge x y) = Submodule.span ℝ {delta x y} := by
  have hd : delta x y ∈ space (SimpleGraph.edge x y) := by
    by_cases hxy : x = y
    · subst y
      rw [delta_self]
      exact Submodule.zero_mem _
    · exact edge_mem _ ((SimpleGraph.edge_adj x y x y).mpr ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨a, b, hab, rfl⟩
    rcases (SimpleGraph.edge_adj x y a b).mp hab with ⟨h | h, _⟩
    · rcases h with ⟨rfl, rfl⟩
      exact Submodule.subset_span (Set.mem_singleton _)
    · rcases h with ⟨ha, hb⟩
      rw [ha, hb, delta_neg x y]
      exact (Submodule.span ℝ {delta x y}).neg_mem
        (Submodule.subset_span (Set.mem_singleton _))
  · exact Submodule.span_le.mpr (fun z hz => (Set.mem_singleton_iff.mp hz) ▸ hd)

noncomputable def representative (G : SimpleGraph V) (c : G.ConnectedComponent) : V :=
  Classical.choose c.nonempty_supp

theorem representative_component (G : SimpleGraph V) (c : G.ConnectedComponent) :
    G.connectedComponentMk (representative G c) = c :=
  (c.mem_supp_iff _).mp (Classical.choose_spec c.nonempty_supp)

noncomputable def root (G : SimpleGraph V) (v : V) : V :=
  representative G (G.connectedComponentMk v)

theorem root_reachable (G : SimpleGraph V) (v : V) : G.Reachable v (root G v) :=
  SimpleGraph.ConnectedComponent.eq.mp (representative_component G _).symm

theorem root_idempotent (G : SimpleGraph V) (v : V) : root G (root G v) = root G v := by
  simp only [root, representative_component]

theorem root_eq_of_reachable (G : SimpleGraph V) {x y : V} (hxy : G.Reachable x y) :
    root G x = root G y := by
  simp only [root, SimpleGraph.ConnectedComponent.eq.mpr hxy]

theorem root_ne_nonroot (G : SimpleGraph V) (v : V) (i : {x // root G x ≠ x}) :
    root G v ≠ i.val := by
  intro he
  apply i.property
  rw [← he, root_idempotent]

noncomputable def generator (G : SimpleGraph V) (i : {x // root G x ≠ x}) : V → ℝ :=
  delta i.val (root G i.val)

theorem generator_coordinate (G : SimpleGraph V)
    (i j : {x // root G x ≠ x}) : generator G j i.val = if j = i then 1 else 0 := by
  have hr := root_ne_nonroot G j.val i
  by_cases hji : j = i
  · subst j
    simp [generator, delta, Ne.symm hr]
  · have hv : j.val ≠ i.val := fun h => hji (Subtype.ext h)
    simp [generator, delta, Ne.symm hr, Ne.symm hv, hji]

variable [Fintype V]

noncomputable def total (S : Finset V) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun z := ∑ x ∈ S, z x
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c z := by simp [Finset.mul_sum]

omit [Fintype V] in
theorem total_single (S : Finset V) (x : V) :
    total S (Pi.single x 1) = if x ∈ S then 1 else 0 := by
  simp [total, Pi.single_apply, eq_comm]

omit [Fintype V] in
theorem total_delta (S : Finset V) (x y : V) :
    total S (delta x y) = (if x ∈ S then 1 else 0) - (if y ∈ S then 1 else 0) := by
  rw [delta, map_sub, total_single, total_single]

omit [Fintype V] in
theorem space_le_total_ker (G : SimpleGraph V) (S : Finset V)
    (hS : ∀ x y, G.Adj x y → (x ∈ S ↔ y ∈ S)) : space G ≤ (total S).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨x, y, hxy, rfl⟩
  change total S (delta x y) = 0
  rw [total_delta]
  by_cases hx : x ∈ S
  · have hy := (hS x y hxy).mp hx
    simp [hx, hy]
  · have hy : y ∉ S := fun hy => hx ((hS x y hxy).mpr hy)
    simp [hx, hy]

theorem mem_space_iff (G : SimpleGraph V) (x y : V) :
    delta x y ∈ space G ↔ G.Reachable x y := by
  refine ⟨?_, reachable_mem G⟩
  intro hm
  by_contra hxy
  let S := Finset.univ.filter (fun v => G.Reachable x v)
  have hclosed : ∀ u v, G.Adj u v → (u ∈ S ↔ v ∈ S) := by
    intro u v huv
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.trans huv.reachable, fun h => h.trans huv.symm.reachable⟩
  have hz := space_le_total_ker G S hclosed hm
  change total S (delta x y) = 0 at hz
  have hx : x ∈ S := by simp [S]
  have hy : y ∉ S := by simp [S, hxy]
  simp [total_delta, hx, hy] at hz

theorem generators_independent (G : SimpleGraph V) : LinearIndependent ℝ (generator G) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := congrFun hc i.val
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, generator_coordinate] using h

omit [Fintype V] in
theorem space_generators (G : SimpleGraph V) :
    Submodule.span ℝ (Set.range (generator G)) = space G := by
  have hroot (v : V) :
      delta v (root G v) ∈ Submodule.span ℝ (Set.range (generator G)) := by
    by_cases hv : root G v = v
    · rw [hv, delta_self]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨v, hv⟩, rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    exact reachable_mem G (root_reachable G i.val)
  · apply Submodule.span_le.mpr
    rintro z ⟨x, y, hxy, rfl⟩
    have hr := root_eq_of_reachable G hxy.reachable
    have he : delta x y = delta x (root G x) - delta y (root G y) := by
      rw [hr]
      ext v
      simp only [delta, Pi.sub_apply]
      ring
    rw [he]
    exact Submodule.sub_mem _ (hroot x) (hroot y)

noncomputable def rank (G : SimpleGraph V) : ℕ := Module.finrank ℝ (space G)

omit [Fintype V] in
theorem rank_bot : rank (⊥ : SimpleGraph V) = 0 := by
  unfold rank
  rw [space_bot]
  exact finrank_bot ℝ (V → ℝ)

theorem rank_add_edge (G : SimpleGraph V) (x y : V) (hxy : ¬G.Reachable x y) :
    rank (G ⊔ SimpleGraph.edge x y) = rank G + 1 := by
  unfold rank
  rw [space_sup, space_edge]
  exact Submodule.finrank_sup_span_singleton (fun h => hxy ((mem_space_iff G x y).mp h))

omit [Fintype V] in
theorem rank_add_edge_of_reachable (G : SimpleGraph V) (x y : V) (hxy : G.Reachable x y) :
    rank (G ⊔ SimpleGraph.edge x y) = rank G := by
  unfold rank
  rw [space_sup, space_edge]
  have hs : Submodule.span ℝ {delta x y} ≤ space G :=
    Submodule.span_le.mpr (fun z hz => (Set.mem_singleton_iff.mp hz) ▸ reachable_mem G hxy)
  rw [sup_eq_left.mpr hs]

theorem rank_add_edge_le (G : SimpleGraph V) (x y : V) :
    rank (G ⊔ SimpleGraph.edge x y) ≤ rank G + 1 := by
  by_cases hxy : G.Reachable x y
  · rw [rank_add_edge_of_reachable G x y hxy]
    omega
  · rw [rank_add_edge G x y hxy]

theorem rank_nonroots (G : SimpleGraph V) :
    rank G = Fintype.card {v // root G v ≠ v} := by
  unfold rank
  rw [← space_generators]
  exact finrank_span_eq_card (generators_independent G)

noncomputable def rootsEquiv (G : SimpleGraph V) :
    {v // root G v = v} ≃ G.ConnectedComponent where
  toFun v := G.connectedComponentMk v.val
  invFun c := ⟨representative G c, by simp only [root, representative_component]⟩
  left_inv v := Subtype.ext v.property
  right_inv c := representative_component G c

theorem rank_add_components (G : SimpleGraph V) :
    rank G + Nat.card G.ConnectedComponent = Nat.card V := by
  have hc := Fintype.card_subtype_compl (fun v => root G v = v)
  have hl : Fintype.card {v // root G v = v} ≤ Fintype.card V :=
    Fintype.card_subtype_le _
  have he : Fintype.card {v // root G v = v} = Nat.card G.ConnectedComponent := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (rootsEquiv G)
  have hv : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  rw [← rank_nonroots G] at hc
  omega

theorem rank_mono {G H : SimpleGraph V} (hGH : G ≤ H) : rank G ≤ rank H :=
  Submodule.finrank_mono (space_mono hGH)

noncomputable def gain (G F : SimpleGraph V) : ℝ :=
  (rank (G ⊔ F) : ℝ) - rank G

theorem gain_nonneg (G F : SimpleGraph V) : 0 ≤ gain G F := by
  exact sub_nonneg.mpr (by exact_mod_cast (rank_mono (le_sup_left : G ≤ G ⊔ F)))

theorem gain_antitone {A B : SimpleGraph V} (hAB : A ≤ B) (F : SimpleGraph V) :
    gain B F ≤ gain A F := by
  have hi := Submodule.finrank_mono
    (inf_le_inf (space_mono hAB) (le_refl (space F)))
  have ha := Submodule.finrank_sup_add_finrank_inf_eq (space A) (space F)
  have hb := Submodule.finrank_sup_add_finrank_inf_eq (space B) (space F)
  have har :
      (Module.finrank ℝ ↥(space A ⊔ space F) : ℝ) +
        Module.finrank ℝ ↥(space A ⊓ space F) =
          Module.finrank ℝ (space A) + Module.finrank ℝ (space F) := by exact_mod_cast ha
  have hbr :
      (Module.finrank ℝ ↥(space B ⊔ space F) : ℝ) +
        Module.finrank ℝ ↥(space B ⊓ space F) =
          Module.finrank ℝ (space B) + Module.finrank ℝ (space F) := by exact_mod_cast hb
  have hir :
      (Module.finrank ℝ ↥(space A ⊓ space F) : ℝ) ≤
        Module.finrank ℝ ↥(space B ⊓ space F) := by exact_mod_cast hi
  unfold gain rank
  rw [space_sup, space_sup]
  linarith

theorem gain_components (G F : SimpleGraph V) :
    gain G F = (Nat.card G.ConnectedComponent : ℝ) -
      Nat.card (G ⊔ F).ConnectedComponent := by
  have hG := rank_add_components G
  have hF := rank_add_components (G ⊔ F)
  have hg : (rank G : ℝ) + Nat.card G.ConnectedComponent = Nat.card V := by exact_mod_cast hG
  have hf : (rank (G ⊔ F) : ℝ) + Nat.card (G ⊔ F).ConnectedComponent = Nat.card V := by
    exact_mod_cast hF
  unfold gain
  linarith

noncomputable def ofEdges (s : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (s : Set (Sym2 V))

omit [Fintype V] in
theorem ofEdges_empty : ofEdges (∅ : Finset (Sym2 V)) = ⊥ := by
  simp only [ofEdges, Finset.coe_empty, SimpleGraph.fromEdgeSet_empty]

omit [Fintype V] in
theorem ofEdges_insert (s : Finset (Sym2 V)) (e : Sym2 V) :
    ofEdges (insert e s) = ofEdges s ⊔ SimpleGraph.fromEdgeSet {e} := by
  simp only [ofEdges, Finset.coe_insert, Set.insert_eq, SimpleGraph.fromEdgeSet_union]
  exact sup_comm _ _

theorem ofEdges_edgeFinset (G : SimpleGraph V) : ofEdges G.edgeFinset = G := by
  ext x y
  simp only [ofEdges, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
    SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact ⟨And.left, fun h => ⟨h, h.ne⟩⟩

theorem rank_add_singleton_le (G : SimpleGraph V) (e : Sym2 V) :
    rank (G ⊔ SimpleGraph.fromEdgeSet {e}) ≤ rank G + 1 := by
  induction e using Sym2.inductionOn with
  | _ x y => exact rank_add_edge_le G x y

theorem rank_add_edges_le (G : SimpleGraph V) (s : Finset (Sym2 V)) :
    rank (G ⊔ ofEdges s) ≤ rank G + s.card := by
  induction s using Finset.induction_on with
  | empty => simp only [ofEdges_empty, sup_bot_eq, Finset.card_empty, Nat.add_zero, le_refl]
  | @insert e s he ih =>
      rw [ofEdges_insert, ← sup_assoc, Finset.card_insert_of_notMem he]
      exact (rank_add_singleton_le (G ⊔ ofEdges s) e).trans (by omega)

theorem rank_le_card_edges (G : SimpleGraph V) : rank G ≤ Nat.card G.edgeSet := by
  have h := rank_add_edges_le (⊥ : SimpleGraph V) G.edgeFinset
  rw [ofEdges_edgeFinset, bot_sup_eq, rank_bot, Nat.zero_add] at h
  exact h.trans_eq (SteinerLowerBound.GraphCost.edgeCount_eq_card G).symm

theorem rank_sup_le (G H : SimpleGraph V) :
    rank (G ⊔ H) ≤ rank G + Nat.card H.edgeSet := by
  have h := rank_add_edges_le G H.edgeFinset
  rw [ofEdges_edgeFinset] at h
  exact h.trans_eq (by rw [← SteinerLowerBound.GraphCost.edgeCount_eq_card H])

noncomputable def cliqueGenerator (T : Finset V) (r : V) (i : {v // v ∈ T ∧ v ≠ r}) : V → ℝ :=
  delta i.val r

theorem cliqueGenerators_independent (T : Finset V) (r : V) :
    LinearIndependent ℝ (cliqueGenerator T r) := by
  have hentry (i j : {v // v ∈ T ∧ v ≠ r}) :
      cliqueGenerator T r j i.val = if j = i then 1 else 0 := by
    by_cases hji : j = i
    · subst j
      simp [cliqueGenerator, delta, i.property.2]
    · have hv : j.val ≠ i.val := fun h => hji (Subtype.ext h)
      simp [cliqueGenerator, delta, Ne.symm hv, i.property.2, hji]
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := congrFun hc i.val
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hentry] using h

omit [Fintype V] in
theorem space_completeOn (T : Finset V) (r : V) (hr : r ∈ T) :
    space (Network.completeOn T) = Submodule.span ℝ (Set.range (cliqueGenerator T r)) := by
  have hroot (v : V) (hv : v ∈ T) :
      delta v r ∈ Submodule.span ℝ (Set.range (cliqueGenerator T r)) := by
    by_cases hvr : v = r
    · rw [hvr, delta_self]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨v, hv, hvr⟩, rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x, y, hxy, rfl⟩
    obtain ⟨_, hx, hy⟩ := (Network.completeOn_adj T x y).mp hxy
    have he : delta x y = delta x r - delta y r := by
      ext v
      simp only [delta, Pi.sub_apply]
      ring
    rw [he]
    exact Submodule.sub_mem _ (hroot x hx) (hroot y hy)
  · apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    exact edge_mem _ ((Network.completeOn_adj T i.val r).mpr ⟨i.property.2, i.property.1, hr⟩)

theorem rank_completeOn (T : Finset V) : rank (Network.completeOn T) = T.card - 1 := by
  by_cases hT : T.Nonempty
  · obtain ⟨r, hr⟩ := hT
    unfold rank
    rw [space_completeOn T r hr, finrank_span_eq_card (cliqueGenerators_independent T r)]
    let e : {v // v ∈ T ∧ v ≠ r} ≃ ↥(T.erase r) :=
      Equiv.subtypeEquivRight (by intro v; simp only [Finset.mem_erase]; exact and_comm)
    calc
      _ = Fintype.card ↥(T.erase r) := Fintype.card_congr e
      _ = (T.erase r).card := Fintype.card_coe _
      _ = T.card - 1 := Finset.card_erase_of_mem hr
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    subst T
    have hg : Network.completeOn (∅ : Finset V) = ⊥ := by
      ext x y
      simp [Network.completeOn_adj]
    rw [hg, rank_bot]
    simp

omit [Fintype V] in
theorem space_of_feasible (T : Finset V) (G : SimpleGraph V)
    (hG : Network.Feasible T G) (hT : Network.TerminalOnly T G) :
    space G = space (Network.completeOn T) := by
  have hle : G ≤ Network.completeOn T := by
    intro x y hxy
    obtain ⟨hx, hy⟩ := hT x y hxy
    exact (Network.completeOn_adj T x y).mpr ⟨hxy.ne, hx, hy⟩
  apply le_antisymm (space_mono hle)
  apply Submodule.span_le.mpr
  rintro z ⟨x, y, hxy, rfl⟩
  obtain ⟨_, hx, hy⟩ := (Network.completeOn_adj T x y).mp hxy
  exact reachable_mem G (hG x hx y hy)

theorem rank_of_feasible (T : Finset V) (G : SimpleGraph V)
    (hG : Network.Feasible T G) (hT : Network.TerminalOnly T G) :
    rank G = T.card - 1 := by
  unfold rank
  rw [space_of_feasible T G hG hT]
  exact rank_completeOn T

theorem gain_le_rank (G F : SimpleGraph V) : gain G F ≤ rank F := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (space G) (space F)
  have hr :
      (Module.finrank ℝ ↥(space G ⊔ space F) : ℝ) +
        Module.finrank ℝ ↥(space G ⊓ space F) =
          Module.finrank ℝ (space G) + Module.finrank ℝ (space F) := by exact_mod_cast h
  have hi : (0 : ℝ) ≤ Module.finrank ℝ ↥(space G ⊓ space F) := Nat.cast_nonneg _
  unfold gain rank
  rw [space_sup]
  linarith

theorem gain_mono_right (G : SimpleGraph V) {F H : SimpleGraph V} (hFH : F ≤ H) :
    gain G F ≤ gain G H := by
  have h := rank_mono (sup_le_sup (le_refl G) hFH)
  unfold gain
  exact sub_le_sub_right (by exact_mod_cast h) _

end SteinerUpperBound.GraphRank
