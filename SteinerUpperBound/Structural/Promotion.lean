module

public import SteinerUpperBound.Structural.CherryElimination

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

noncomputable abbrev retained (S : TreeGeometry.TreeSolution I)
    (removed z : ↥S.vertices) (hz : z ≠ removed) : ↥(S.vertices.erase (removed : V)) :=
  ⟨z.val, Finset.mem_erase.mpr ⟨Subtype.val_injective.ne hz, z.property⟩⟩

@[simp] theorem retained_val (S : TreeGeometry.TreeSolution I)
    (removed z : ↥S.vertices) (hz : z ≠ removed) :
    (retained S removed z hz : V) = (z : V) := rfl

namespace Cherry

variable {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}

noncomputable abbrev promote (C : Cherry S v) : TreeGeometry.TreeSolution I :=
  suppress C.promoted C.center v C.primary C.center_nonterminal
    ((C.promoted_center_adj v).mpr (Or.inl rfl))
    ((C.promoted_center_adj C.primary).mpr (Or.inr rfl)) C.primary_ne_attachment.symm
    (fun z hz => (C.promoted_center_adj z).mp hz)

theorem promote_preserves_terminals (C : Cherry S v) :
    terminalGraph S ≤ terminalGraph C.promote :=
  (exchange_preserves_terminals S C.center C.secondary C.primary C.secondary C.secondary_arm
    (sibling_cut_reachable S C.center C.secondary C.primary C.secondary_arm C.primary_arm C.ports_ne.symm)
    (SimpleGraph.Reachable.refl _) C.center_nonterminal).trans
      (suppress_preserves_terminals C.promoted C.center v C.primary C.center_nonterminal
        ((C.promoted_center_adj v).mpr (Or.inl rfl))
        ((C.promoted_center_adj C.primary).mpr (Or.inr rfl)) C.primary_ne_attachment.symm
        (fun z hz => (C.promoted_center_adj z).mp hz))

theorem promote_cost_le (C : Cherry S v) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) :
    GraphCost.cost (fun e => w (e.map Subtype.val)) C.promote.graph ≤
      GraphCost.cost (fun e => w (e.map Subtype.val)) S.graph -
        w s((C.center : V), (C.secondary : V)) - w s((C.center : V), (v : V)) -
        w s((C.center : V), (C.primary : V)) +
        w s((C.primary : V), (C.secondary : V)) + w s((C.primary : V), (v : V)) := by
  have h1 := exchangeEdge_cost_le S.graph (fun e => w (e.map Subtype.val)) (fun e => hw _)
    (a := C.primary) (b := C.secondary) C.secondary_arm
  change GraphCost.cost (fun e => w (e.map Subtype.val)) C.promoted.graph ≤ _ at h1
  have h2 := suppress_cost_le C.promoted C.center v C.primary C.center_nonterminal
    ((C.promoted_center_adj v).mpr (Or.inl rfl))
    ((C.promoted_center_adj C.primary).mpr (Or.inr rfl)) C.primary_ne_attachment.symm
    (fun z hz => (C.promoted_center_adj z).mp hz) w hw
  change GraphCost.cost (fun e => w (e.map Subtype.val)) C.promote.graph ≤ _ at h2
  simp only [Sym2.map_mk] at h1
  linarith

theorem promote_potential (C : Cherry S v) :
    potential C.promote ≤ potential S + (2 - chi) * I.distance C.center C.secondary := by
  have hh := C.promote_cost_le (potentialWeight I) (potentialWeight_nonneg I)
  simp only [potentialWeight_mk, potentialDistance, C.center_nonterminal, C.primary_terminal,
    C.secondary_terminal, C.attachment_nonterminal, false_and, and_false, and_self, ↓reduceIte] at hh
  have h1 := I.distance_triangle (C.primary : V) C.center C.secondary
  rw [I.distance_comm (C.primary : V) C.center] at h1
  have h2 := I.distance_triangle (C.primary : V) C.center v
  rw [I.distance_comm (C.primary : V) C.center] at h2
  have hs := C.ordered
  change GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) C.promote.graph ≤
    GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) S.graph +
      (2 - chi) * I.distance C.center C.secondary
  have hchi : 0 ≤ chi := by norm_num [chi, e0]
  change GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) C.promote.graph ≤ _ at hh
  nlinarith [mul_le_mul_of_nonneg_left h2 hchi]

theorem promote_nonterminalCost (C : Cherry S v) :
    nonterminalCost C.promote ≤ nonterminalCost S - I.distance v C.center := by
  have hh := C.promote_cost_le (nonterminalWeight I) (nonterminalWeight_nonneg I)
  simpa [nonterminalCost, nonterminalWeight_mk, nonterminalDistance,
    C.center_nonterminal, C.attachment_nonterminal, C.primary_terminal, C.secondary_terminal,
    I.distance_comm C.center v] using hh

theorem promote_steinerEdges (C : Cherry S v) :
    (steinerEdges C.promote).card < (steinerEdges S).card := by
  have hxy : (C.primary : V) ≠ (C.secondary : V) := fun h => C.ports_ne (Subtype.ext h)
  have hh := C.promote_cost_le (steinerCountWeight I) (steinerCountWeight_nonneg I)
  have hnewT : steinerCountWeight I s((C.primary : V), (C.secondary : V)) = 0 := by
    simp [steinerCountWeight, SimpleGraph.mem_edgeSet, Network.completeOn_adj, hxy,
      C.primary_terminal, C.secondary_terminal]
  have hnewS : steinerCountWeight I s((C.primary : V), (v : V)) = 1 := by
    rw [Sym2.eq_swap]
    exact steinerCountWeight_incident I C.attachment_nonterminal _
  simp only [steinerCountWeight_incident I C.center_nonterminal, hnewT, hnewS, add_zero] at hh
  change GraphCost.cost (fun e => steinerCountWeight I (e.map Subtype.val)) C.promote.graph ≤
    GraphCost.cost (fun e => steinerCountWeight I (e.map Subtype.val)) S.graph - 1 - 1 - 1 + 1 at hh
  rw [steinerCountWeight_cost C.promote, steinerCountWeight_cost S] at hh
  have hN : (steinerEdges C.promote).card + 2 ≤ (steinerEdges S).card := by
    exact_mod_cast (show ((steinerEdges C.promote).card : ℝ) + 2 ≤ (steinerEdges S).card by linarith)
  omega

theorem promote_adj_survives (C : Cherry S v) (a b : ↥S.vertices)
    (ha : a ≠ C.center) (hb : b ≠ C.center) (hab : S.graph.Adj a b) :
    C.promote.graph.Adj (retained S C.center a ha) (retained S C.center b hb) := by
  have hnot (x : ↥S.vertices) : s(a, b) ≠ s(C.center, x) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨_, h⟩
    · exact ha h
    · exact hb h
  change ((S.graph.deleteEdges {s(C.center, C.secondary)} ⊔ SimpleGraph.edge C.primary C.secondary).deleteEdges
    {s(C.center, v)} ⊔ SimpleGraph.edge C.primary v).Adj a b
  apply Or.inl
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨Or.inl (SimpleGraph.deleteEdges_adj.mpr ⟨hab, ?_⟩), ?_⟩
  · simpa only [Set.mem_singleton_iff] using hnot C.secondary
  · simpa only [Set.mem_singleton_iff] using hnot v

theorem promote_adj_reflects (C : Cherry S v) (z : ↥S.vertices)
    (hzT : (z : V) ∉ I.terminals) (hzv : z ≠ v) (hzc : z ≠ C.center)
    (w : ↥C.promote.vertices)
    (h : C.promote.graph.Adj (retained S C.center z hzc) w) :
    S.graph.Adj z (eraseEmbedding S C.center w) := by
  have hzp : z ≠ C.primary := fun he => hzT (he ▸ C.primary_terminal)
  have hzq : z ≠ C.secondary := fun he => hzT (he ▸ C.secondary_terminal)
  change ((S.graph.deleteEdges {s(C.center, C.secondary)} ⊔ SimpleGraph.edge C.primary C.secondary).deleteEdges
    {s(C.center, v)} ⊔ SimpleGraph.edge C.primary v).Adj z (eraseEmbedding S C.center w) at h
  rcases h with h | h
  · have hh := (SimpleGraph.deleteEdges_adj.mp h).1
    rcases hh with hh | hh
    · exact (SimpleGraph.deleteEdges_adj.mp hh).1
    · rcases (SimpleGraph.edge_adj C.primary C.secondary _ _).mp hh with ⟨h | h, _⟩
      · exact False.elim (hzp h.1)
      · exact False.elim (hzq h.1)
  · rcases (SimpleGraph.edge_adj C.primary v _ _).mp h with ⟨h | h, _⟩
    · exact False.elim (hzp h.1)
    · exact False.elim (hzv h.1)

noncomputable abbrev transport {w : ↥S.vertices} (C : Cherry S v) (D : Cherry S w)
    (hw : w ≠ C.center) (hdv : D.center ≠ v) (hdc : D.center ≠ C.center) :
    Cherry C.promote (retained S C.center w hw) where
  center := retained S C.center D.center hdc
  primary := retained S C.center D.primary (fun h => C.center_nonterminal (h ▸ D.primary_terminal))
  secondary := retained S C.center D.secondary (fun h => C.center_nonterminal (h ▸ D.secondary_terminal))
  attachment_nonterminal := D.attachment_nonterminal
  center_nonterminal := D.center_nonterminal
  primary_terminal := D.primary_terminal
  secondary_terminal := D.secondary_terminal
  ports_ne := fun h => D.ports_ne
    (Subtype.ext (congrArg (fun z : ↥C.promote.vertices => (z : V)) h))
  trunk := C.promote_adj_survives w D.center hw hdc D.trunk
  primary_arm := C.promote_adj_survives D.center D.primary hdc _ D.primary_arm
  secondary_arm := C.promote_adj_survives D.center D.secondary hdc _ D.secondary_arm
  neighbors := by
    intro z hz
    have hold := C.promote_adj_reflects D.center D.center_nonterminal hdv hdc z hz
    rcases D.neighbors (eraseEmbedding S C.center z) hold with h | h | h
    · exact Or.inl (Subtype.ext (by
        simpa only [eraseEmbedding_val, retained_val] using
          congrArg (fun x : ↥S.vertices => (x : V)) h))
    · exact Or.inr (Or.inl (Subtype.ext (by
        simpa only [eraseEmbedding_val, retained_val] using
          congrArg (fun x : ↥S.vertices => (x : V)) h)))
    · exact Or.inr (Or.inr (Subtype.ext (by
        simpa only [eraseEmbedding_val, retained_val] using
          congrArg (fun x : ↥S.vertices => (x : V)) h)))
  ordered := D.ordered

theorem small_charge (C : Cherry S v) (hred : Reduced S)
    (hsmall : I.distance C.center C.primary <
      alpha0 * (I.distance v C.center + I.distance C.center C.primary)) :
    I.distance C.center C.secondary <
      (alpha0 / ((1 - alpha0) * (chi - 1))) * I.distance v C.center := by
  have hh := C.longer_arm_bound hred
  norm_num [alpha0, chi, e0] at hh hsmall ⊢
  linarith

theorem small_promotion_paid (C : Cherry S v) (hred : Reduced S)
    (hsmall : I.distance C.center C.primary <
      alpha0 * (I.distance v C.center + I.distance C.center C.primary)) :
    I.distance C.center C.secondary ≤
      (alpha0 / ((1 - alpha0) * (chi - 1))) *
        (nonterminalCost S - nonterminalCost C.promote) := by
  have hc := C.small_charge hred hsmall
  have hn := C.promote_nonterminalCost
  have hp : 0 ≤ alpha0 / ((1 - alpha0) * (chi - 1)) := by norm_num [alpha0, chi, e0]
  exact hc.le.trans (mul_le_mul_of_nonneg_left (by linarith) hp)

end Cherry

end SteinerUpperBound.Structural.Tree
