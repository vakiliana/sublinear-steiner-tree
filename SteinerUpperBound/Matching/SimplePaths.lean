module

public import SteinerUpperBound.Matching.Paths

@[expose] public section

namespace SteinerUpperBound.Matching

open scoped Classical BigOperators

variable {V E : Type*} [Fintype E]

namespace Graph

variable (G : Graph V E) (ρ : Rank E)

theorem validStack_pairwise {ds : List (Directed E)} (h : G.ValidStack ρ ds) :
    ds.Pairwise (fun a b => ρ.index a.1 < ρ.index b.1) := by
  let R : Directed E → Directed E → Prop := fun a b => ρ.index a.1 < ρ.index b.1
  let : IsTrans (Directed E) R := ⟨fun _ _ _ hab hbc => hab.trans hbc⟩
  exact List.isChain_iff_pairwise.mp (h.2.imp fun _ _ hs => hs.1)

theorem validStack_tail {d : Directed E} {ds : List (Directed E)}
    (h : G.ValidStack ρ (d :: ds)) : G.ValidStack ρ ds :=
  ⟨fun a ha => h.1 a (List.mem_cons_of_mem _ ha), h.2.tail⟩

theorem validStack_copies_nodup {ds : List (Directed E)} (h : G.ValidStack ρ ds) :
    (ds.map Prod.fst).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact (G.validStack_pairwise ρ h).imp (fun hlt heq => by simp [heq] at hlt)

theorem validStack_head_not_tail {d : Directed E} {ds : List (Directed E)}
    (h : G.ValidStack ρ (d :: ds)) :
    G.head d ∉ (d :: ds).map G.tail := by
  intro hm
  obtain ⟨a, ha, heq⟩ := List.mem_map.mp hm
  rcases List.mem_cons.mp ha with had | ha
  · subst a
    exact G.head_ne_tail d heq.symm
  · have hr := (List.pairwise_cons.mp (G.validStack_pairwise ρ h)).1 a ha
    have hfa := h.1 a (by simp [ha])
    have hfd := h.1 d (by simp)
    have hhead : G.Free (G.greedyPrefix ρ (ρ.index d.1)) (G.head d) := by
      rw [← heq]
      exact G.free_mono (G.greedyPrefix_mono ρ hr.le) hfa
    have had := (G.accepted_at_free_tail ρ d hfd).mpr hhead
    have hmem := (G.mem_greedyPrefix ρ (ρ.index a.1) d.1).mpr ⟨hr, had⟩
    exact hfa d.1 hmem (by rw [heq]; exact G.head_incident d)

def stackVertices : List (Directed E) → List V
  | [] => []
  | d :: ds => G.head d :: (d :: ds).map G.tail

theorem validStack_vertices_nodup {ds : List (Directed E)} (h : G.ValidStack ρ ds) :
    (G.stackVertices ds).Nodup := by
  induction ds with
  | nil => simp [stackVertices]
  | cons d ds ih =>
    have hn := G.validStack_head_not_tail ρ h
    refine List.nodup_cons.mpr ⟨hn, ?_⟩
    cases ds with
    | nil => simp
    | cons a ds =>
      have hstep := (List.isChain_cons_cons.mp h.2).1
      have hh := ih (G.validStack_tail ρ h)
      simpa only [stackVertices, List.map_cons, hstep.2] using hh

theorem validStack_length_lt [Fintype V] {d : Directed E} {ds : List (Directed E)}
    (h : G.ValidStack ρ (d :: ds)) : (d :: ds).length < Fintype.card V := by
  have hl := (G.validStack_vertices_nodup ρ h).length_le_card
  simp only [stackVertices, List.length_cons, List.length_map] at hl
  simp only [List.length_cons]
  omega

theorem vertexOracle_stack_length_lt [Fintype V] (v : V) (c : Invocation E)
    (hc : c ∈ (G.vertexOracle ρ v).calls) :
    (c.state :: c.ancestors).length < Fintype.card V :=
  G.validStack_length_lt ρ (G.vertexOracle_validStack ρ v c hc)

end Graph

end SteinerUpperBound.Matching
