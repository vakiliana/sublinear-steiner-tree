module

public import SteinerUpperBound.PortGraph.Program

@[expose] public section

namespace SteinerUpperBound.PortGraph

open scoped Classical BigOperators
open Covers.Geometry Matching

variable {n k b B : ℕ} {Q : Type}

abbrev AllPart (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k) :=
  ↥(parts I bits cfg)

noncomputable def residualParts (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ) : Finset (AllPart I bits cfg) :=
  Finset.univ.filter (fun C => C.val ∈ smallParts I bits cfg B)

noncomputable def originalRows (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (v : Fin n) : Finset (AllPart I bits cfg) :=
  Finset.univ.filter (fun C => C.val ∈ rows I bits cfg v)

noncomputable def originalLists (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b : ℕ) (C : AllPart I bits cfg) : Finset (Fin n) :=
  lists I bits cfg b C.val

def inclusion (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ) : Vertex I bits cfg B ↪ AllPart I bits cfg where
  toFun C := ⟨C.val, vertex_part I bits cfg B C⟩
  inj' := by
    intro C D h
    apply Subtype.ext
    exact congrArg (fun E : AllPart I bits cfg => E.val) h

def mapGraph {V W E : Type*} (G : Matching.Graph V E) (j : V ↪ W) : Matching.Graph W E where
  left e := j (G.left e)
  right e := j (G.right e)
  loopless e h := G.loopless e (j.injective h)

/-- This lift is for saving statistics only. Its copy carrier and ranks are
unchanged; runtime matching still uses the smaller `Vertex` universe. -/
noncomputable def liftedGraph (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ) :
    Matching.Graph (AllPart I bits cfg) (Copy I bits cfg b B) :=
  mapGraph (graph I bits cfg b B) (inclusion I bits cfg B)

theorem inclusion_mem (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ) (C : Vertex I bits cfg B) :
    inclusion I bits cfg B C ∈ residualParts I bits cfg B := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.property⟩

theorem originalRows_image (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (v : Fin n) :
    (originalRows I bits cfg v).image Subtype.val = rows I bits cfg v := by
  classical
  ext C
  constructor
  · intro h
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hD).2
  · intro hC
    let C' : AllPart I bits cfg := ⟨C, (rowOn_subset_componentsOn I _ _ _ v) hC⟩
    exact Finset.mem_image.mpr ⟨C', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩, rfl⟩

theorem originalRows_card (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (v : Fin n) :
    (originalRows I bits cfg v).card = (rows I bits cfg v).card := by
  classical
  have h := Finset.card_image_of_injective (originalRows I bits cfg v) Subtype.val_injective
  rw [originalRows_image] at h
  exact h.symm

theorem originalLists_ordered (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b : ℕ) (C : AllPart I bits cfg) :
    originalLists I bits cfg b C =
      SetSystem.firstIncident (List.finRange n) (originalRows I bits cfg) b C := by
  classical
  have hl :
      incidentList (List.finRange n) (rows I bits cfg) b C.val =
        incidentList (List.finRange n) (originalRows I bits cfg) b C := by
    unfold incidentList
    apply congrArg (List.take b)
    apply List.filter_congr
    intro v _
    apply bool_ext
    simp only [decide_eq_true_eq, originalRows, Finset.mem_filter, Finset.mem_univ, true_and]
  ext v
  simp only [originalLists, lists, SetSystem.firstIncident, List.mem_toFinset]
  exact Iff.of_eq (congrArg (fun l : List (Fin n) => v ∈ l) hl)

noncomputable def incidenceCap (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ) :
    SetSystem.IncidenceCap Finset.univ (originalRows I bits cfg) (residualParts I bits cfg B) b where
  lists := originalLists I bits cfg b
  sound C hC v hv := by
    classical
    exact ⟨Finset.mem_univ _, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, lists_sound I bits cfg b C.val hv⟩⟩
  card_le C _ := lists_card_le I bits cfg b C.val
  complete C hC hlt v hv hrow := by
    classical
    have hCs : C.val ∈ smallParts I bits cfg B := (Finset.mem_filter.mp hC).2
    have hCv : C.val ∈ rows I bits cfg v := (Finset.mem_filter.mp hrow).2
    exact (SetSystem.orderedCap (List.finRange n) (List.nodup_finRange n)
      (rows I bits cfg) (smallParts I bits cfg B) b).complete C.val hCs hlt v
        (by simp) hCv

theorem lifted_realizes (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) :
    SetSystem.Realizes (liftedGraph I bits cfg b B)
      (SetSystem.mutualGraph (residualParts I bits cfg B) (eligible I bits cfg)
        (incidenceCap I bits cfg b B).lists) := by
  classical
  intro C D
  constructor
  · rintro ⟨hC, hD, hne, v, hv, hvC, hvD⟩
    let C' : Vertex I bits cfg B := ⟨C.val, (Finset.mem_filter.mp hC).2⟩
    let D' : Vertex I bits cfg B := ⟨D.val, (Finset.mem_filter.mp hD).2⟩
    have hh : (underlying I bits cfg b B).Adj C' D' :=
      ⟨C'.property, D'.property, fun he => hne (Subtype.ext he), v, hv, hvC, hvD⟩
    obtain ⟨e, he⟩ := (graph_realizes I bits cfg b B hT C' D').mp hh
    have hC' : inclusion I bits cfg B C' = C := Subtype.ext rfl
    have hD' : inclusion I bits cfg B D' = D := Subtype.ext rfl
    refine ⟨e, ?_⟩
    rcases he with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact Or.inl ⟨(congrArg (inclusion I bits cfg B) hl).trans hC',
        (congrArg (inclusion I bits cfg B) hr).trans hD'⟩
    · exact Or.inr ⟨(congrArg (inclusion I bits cfg B) hl).trans hD',
        (congrArg (inclusion I bits cfg B) hr).trans hC'⟩
  · rintro ⟨e, he | he⟩
    · obtain ⟨rfl, rfl⟩ := he
      exact ⟨inclusion_mem I bits cfg B _, inclusion_mem I bits cfg B _,
        (liftedGraph I bits cfg b B).loopless e, e.val.1, e.property.eligible,
        e.property.left_list, e.property.right_list⟩
    · obtain ⟨rfl, rfl⟩ := he
      exact ⟨inclusion_mem I bits cfg B _, inclusion_mem I bits cfg B _,
        ((liftedGraph I bits cfg b B).loopless e).symm, e.val.1, e.property.eligible,
        e.property.right_list, e.property.left_list⟩

theorem map_incident {V W E : Type*} (G : Matching.Graph V E) (j : V ↪ W) (e : E) (v : V) :
    (mapGraph G j).Incident e (j v) ↔ G.Incident e v := by
  simp only [Graph.Incident, mapGraph, j.injective.eq_iff]

theorem map_touch {V W E : Type*} (G : Matching.Graph V E) (j : V ↪ W) (e f : E) :
    (mapGraph G j).Touch e f ↔ G.Touch e f := by
  constructor
  · rintro ⟨v, he, hf⟩
    rcases he with hl | hr
    · rw [← hl] at hf
      exact ⟨G.left e, G.incident_left e, (map_incident G j f _).mp hf⟩
    · rw [← hr] at hf
      exact ⟨G.right e, G.incident_right e, (map_incident G j f _).mp hf⟩
  · rintro ⟨v, he, hf⟩
    exact ⟨j v, (map_incident G j e v).mpr he, (map_incident G j f v).mpr hf⟩

theorem map_admissible {V W E : Type*} [Fintype E] (G : Matching.Graph V E) (j : V ↪ W)
    (M : Finset E) (e : E) :
    (mapGraph G j).Admissible M e ↔ G.Admissible M e := by
  rw [Graph.admissible_iff_no_touch, Graph.admissible_iff_no_touch]
  simp only [map_touch]

theorem map_greedyPrefix {V W E : Type*} [Fintype E] (G : Matching.Graph V E) (j : V ↪ W)
    (rank : Matching.Rank E) (t : ℕ) :
    (mapGraph G j).greedyPrefix rank t = G.greedyPrefix rank t := by
  classical
  induction t with
  | zero => rfl
  | succ t ih =>
    cases he : rank.edgeAt t with
    | none => simp only [Graph.greedyPrefix, he, ih]
    | some e =>
      have ha :
          (mapGraph G j).Admissible ((mapGraph G j).greedyPrefix rank t) e ↔
            G.Admissible (G.greedyPrefix rank t) e := by
        rw [ih]
        exact map_admissible G j _ e
      rw [Graph.greedyPrefix, Graph.greedyPrefix, he]
      dsimp only
      by_cases h : G.Admissible (G.greedyPrefix rank t) e
      · rw [ite_eq_left (ha.mpr h), ite_eq_left h, ih]
      · rw [ite_eq_right (fun h' => h (ha.mp h')), ite_eq_right h, ih]

theorem lifted_greedy (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ) (rank : Matching.Rank (Copy I bits cfg b B)) :
    (liftedGraph I bits cfg b B).greedy rank = (graph I bits cfg b B).greedy rank :=
  map_greedyPrefix (graph I bits cfg b B) (inclusion I bits cfg B) rank _

theorem lifted_incident (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ) (e : Copy I bits cfg b B)
    (C : Vertex I bits cfg B) :
    (liftedGraph I bits cfg b B).Incident e (inclusion I bits cfg B C) ↔
      (graph I bits cfg b B).Incident e C :=
  map_incident _ _ e C

theorem lifted_matched (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ) (rank : Matching.Rank (Copy I bits cfg b B))
    (C : Vertex I bits cfg B) :
    (∃ e ∈ (liftedGraph I bits cfg b B).greedy rank,
      (liftedGraph I bits cfg b B).Incident e (inclusion I bits cfg B C)) ↔
    ∃ e ∈ (graph I bits cfg b B).greedy rank, (graph I bits cfg b B).Incident e C := by
  rw [lifted_greedy]
  simp only [lifted_incident]

theorem original_ineligible (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (v : Fin n) (hv : v ∉ eligible I bits cfg) :
    (originalRows I bits cfg v).card ≤ 2 := by
  have hcard : (rows I bits cfg v).card < 3 := by
    by_contra hn
    exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_not_gt hn⟩)
  rw [originalRows_card]
  omega

theorem inter_card_le_right {V : Type*} (A B : Finset V) : (A ∩ B).card ≤ B.card := by
  classical
  exact Finset.card_le_card Finset.inter_subset_right

theorem greedy_saving_bounds (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hb : 1 ≤ b)
    (rank : Matching.Rank (Copy I bits cfg b B)) :
    SetSystem.saving (eligible I bits cfg) (originalRows I bits cfg) (residualParts I bits cfg B) / 2 -
        n / (b : ℝ) ≤ (((graph I bits cfg b B).greedy rank).card : ℝ) ∧
      (((graph I bits cfg b B).greedy rank).card : ℝ) ≤
        SetSystem.saving (eligible I bits cfg) (originalRows I bits cfg) (residualParts I bits cfg B) := by
  have h := SetSystem.mutualCap_greedy_half (Finset.univ : Finset (Fin n)) (eligible I bits cfg)
    (originalRows I bits cfg) (fun _ _ => Finset.mem_univ _) (residualParts I bits cfg B) b hb
    (incidenceCap I bits cfg b B) (fun v _ hv => (inter_card_le_right _ _).trans
      (original_ineligible I bits cfg v hv))
    (liftedGraph I bits cfg b B) (lifted_realizes I bits cfg b B hT) rank
  rw [lifted_greedy] at h
  simpa only [Finset.card_univ, Fintype.card_fin] using h

theorem expected_greedy_saving_bounds (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hb : 1 ≤ b)
    (μ : SteinerLowerBound.Law (Matching.Rank (Copy I bits cfg b B))) :
    SetSystem.saving (eligible I bits cfg) (originalRows I bits cfg) (residualParts I bits cfg B) / 2 -
        n / (b : ℝ) ≤ μ.expect (fun rank => (((graph I bits cfg b B).greedy rank).card : ℝ)) ∧
      μ.expect (fun rank => (((graph I bits cfg b B).greedy rank).card : ℝ)) ≤
        SetSystem.saving (eligible I bits cfg) (originalRows I bits cfg) (residualParts I bits cfg B) := by
  have h := greedy_saving_bounds I bits cfg b B hT hb
  constructor
  · simpa only [SteinerLowerBound.Law.expect_const] using μ.expect_mono (fun rank => (h rank).1)
  · simpa only [SteinerLowerBound.Law.expect_const] using μ.expect_mono (fun rank => (h rank).2)

end SteinerUpperBound.PortGraph
