module

public import SteinerUpperBound.Matching.Requests

@[expose] public section

/-! Focused regression proofs for empty lists, labeled parallel copies, and cache hits. -/

namespace SteinerUpperBound.Matching.Checks

open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical

theorem isolated_vertex {V E : Type*} [Fintype E] (G : Graph V E) (ρ : Rank E)
    (v : V) (hv : ∀ e, ¬ G.Incident e v) :
    (G.vertexOracle ρ v).value = none ∧ (G.vertexOracle ρ v).calls = [] := by
  have hc : G.candidates ρ (Fintype.card E) v = [] := by
    cases he : G.candidates ρ (Fintype.card E) v with
    | nil => rfl
    | cons e xs =>
      have hm : e ∈ G.candidates ρ (Fintype.card E) v := by rw [he]; simp
      exact (hv e ((G.mem_candidates ρ _ v e).mp hm).2).elim
  simp [Graph.vertexOracle, hc, Run.scan]

theorem empty_copy_type {V : Type*} (G : Graph V (Fin 0)) (ρ : Rank (Fin 0)) (v : V) :
    (G.vertexOracle ρ v).value = none ∧ (G.vertexOracle ρ v).calls = [] :=
  isolated_vertex G ρ v (fun e => Fin.elim0 e)

def parallel (p : ℕ) : Graph Bool (Fin p) where
  left _ := false
  right _ := true
  loopless _ := by decide

/-- Parallel identifiers are not collapsed: the returned copy is the rank-zero ID. -/
theorem parallel_minimum_id (p : ℕ) (hp : 0 < p) (ρ : Rank (Fin p)) (v : Bool) :
    ((parallel p).vertexOracle ρ v).value = some (ρ.edge ⟨0, by simpa using hp⟩) := by
  let e := ρ.edge ⟨0, by simpa using hp⟩
  have ha : (parallel p).Accepted ρ e := by
    simp [e, Graph.Accepted, Graph.Admissible, Graph.Free]
  apply ((parallel p).vertexOracle_eq_some_iff ρ v e).mpr
  refine ⟨((parallel p).mem_greedy ρ e).mpr ha, ?_⟩
  cases v <;> simp [Graph.Incident, parallel]

theorem cache_hit_is_logged {V E : Type*} [Fintype E] (G : Graph V E) (ρ : Rank E)
    (d : Directed E) (ancestors : List (Directed E)) (μ : Memo E) (b : Bool)
    (hb : μ d = some b) :
    (G.runEO ρ d ancestors μ).value = b ∧
      (G.runEO ρ d ancestors μ).calls = [⟨d, ancestors, true⟩] ∧
      requests (G.runEO ρ d ancestors μ).calls d = 1 := by
  rw [Graph.runEO, hb]
  simp [requests]

end SteinerUpperBound.Matching.Checks
