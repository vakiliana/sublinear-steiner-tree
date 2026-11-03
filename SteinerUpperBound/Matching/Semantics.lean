module

public import SteinerUpperBound.Matching.Greedy

@[expose] public section

namespace SteinerUpperBound.Matching

open scoped Classical BigOperators

variable {V E : Type*} [Fintype E]

namespace Graph

variable (G : Graph V E) (ρ : Rank E)

noncomputable def candidates (k : ℕ) (v : V) : List E :=
  (ρ.edgesBelow k).filter fun e => G.Incident e v

@[simp] theorem mem_candidates (k : ℕ) (v : V) (e : E) :
    e ∈ G.candidates ρ k v ↔ ρ.index e < k ∧ G.Incident e v := by
  simp [candidates]

theorem candidates_nodup (k : ℕ) (v : V) : (G.candidates ρ k v).Nodup :=
  (ρ.edgesBelow_nodup k).filter _

theorem candidates_pairwise (k : ℕ) (v : V) :
    (G.candidates ρ k v).Pairwise (fun e f => ρ.index e < ρ.index f) :=
  (ρ.edgesBelow_pairwise k).filter _

@[simp] theorem candidates_zero (v : V) : G.candidates ρ 0 v = [] := rfl

theorem candidates_succ (k : ℕ) (hk : k < Fintype.card E) (v : V) :
    G.candidates ρ (k + 1) v =
      G.candidates ρ k v ++
        if G.Incident (ρ.edge ⟨k, hk⟩) v then [ρ.edge ⟨k, hk⟩] else [] := by
  by_cases hi : G.Incident (ρ.edge ⟨k, hk⟩) v <;>
    simp [candidates, ρ.edgesBelow_succ k hk, hi]

theorem candidates_succ_of_ge (k : ℕ) (hk : Fintype.card E ≤ k) (v : V) :
    G.candidates ρ (k + 1) v = G.candidates ρ k v := by
  simp [candidates, ρ.edgesBelow_succ_of_ge k hk]

/-- Specification for a directed answer, meaningful even for states never queried. -/
noncomputable def freeBefore (d : Directed E) : Bool :=
  decide (G.Free (G.greedyPrefix ρ (ρ.index d.1)) (G.head d))

/-- The first positive directed answer in the indicated initial segment. -/
noncomputable def localFirst (k : ℕ) (v : V) : Option E :=
  (G.candidates ρ k v).find? fun e => G.freeBefore ρ (G.away v e)

/-- Read the sequential matching, without running a local oracle. -/
noncomputable def greedyMate (k : ℕ) (v : V) : Option E :=
  (G.candidates ρ k v).find? fun e => decide (e ∈ G.greedy ρ)

theorem greedyMate_eq_none (k : ℕ) (v : V) :
    G.greedyMate ρ k v = none ↔ G.Free (G.greedyPrefix ρ k) v := by
  rw [greedyMate, List.find?_eq_none]
  simp only [Bool.not_eq_true, decide_eq_false_iff_not, G.mem_candidates]
  constructor
  · intro h e he hi
    obtain ⟨hr, ha⟩ := (G.mem_greedyPrefix ρ k e).mp he
    exact h e ⟨hr, hi⟩ ((G.mem_greedy ρ e).mpr ha)
  · intro h e ⟨hr, hi⟩ he
    exact h e ((G.mem_greedyPrefix ρ k e).mpr
      ⟨hr, (G.mem_greedy ρ e).mp he⟩) hi

theorem greedyMate_eq_some {k : ℕ} {v : V} {e : E}
    (h : G.greedyMate ρ k v = some e) :
    e ∈ G.greedy ρ ∧ ρ.index e < k ∧ G.Incident e v := by
  have hm := List.mem_of_find?_eq_some h
  have ha := List.find?_some h
  exact ⟨of_decide_eq_true ha, (G.mem_candidates ρ k v e).mp hm⟩

theorem localFirst_eq_greedyMate (k : ℕ) (v : V) :
    G.localFirst ρ k v = G.greedyMate ρ k v := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < Fintype.card E
    · unfold localFirst greedyMate at ih ⊢
      rw [G.candidates_succ ρ k hk v, List.find?_append, List.find?_append, ih]
      cases hm : G.greedyMate ρ k v with
      | some e =>
        have hm' : (G.candidates ρ k v).find? (fun e => decide (e ∈ G.greedy ρ)) =
            some e := hm
        rw [hm']
        rfl
      | none =>
        have hm' : (G.candidates ρ k v).find? (fun e => decide (e ∈ G.greedy ρ)) =
            none := hm
        rw [hm']
        have hv := (G.greedyMate_eq_none ρ k v).mp hm
        by_cases hi : G.Incident (ρ.edge ⟨k, hk⟩) v
        · simp only [hi, ↓reduceIte]
          have ht : G.Free (G.greedyPrefix ρ (ρ.index (ρ.edge ⟨k, hk⟩)))
              (G.tail (G.away v (ρ.edge ⟨k, hk⟩))) := by
            simpa [G.tail_away hi] using hv
          have he : G.freeBefore ρ (G.away v (ρ.edge ⟨k, hk⟩)) =
              decide (ρ.edge ⟨k, hk⟩ ∈ G.greedy ρ) := by
            simp only [freeBefore, away_edge, G.mem_greedy]
            exact congrArg (fun p : Prop => decide p)
              (propext (G.accepted_at_free_tail ρ (G.away v (ρ.edge ⟨k, hk⟩)) ht).symm)
          simp only [List.find?_cons, List.find?_nil, he]
        · simp only [hi, ↓reduceIte]
          rfl
    · unfold localFirst greedyMate at ih ⊢
      rw [G.candidates_succ_of_ge ρ k (Nat.le_of_not_gt hk) v]
      exact ih

theorem localFirst_eq_none (k : ℕ) (v : V) :
    G.localFirst ρ k v = none ↔ G.Free (G.greedyPrefix ρ k) v := by
  rw [G.localFirst_eq_greedyMate ρ, G.greedyMate_eq_none]

theorem localFirst_eq_some {k : ℕ} {v : V} {e : E}
    (h : G.localFirst ρ k v = some e) :
    e ∈ G.greedy ρ ∧ ρ.index e < k ∧ G.Incident e v := by
  rw [G.localFirst_eq_greedyMate ρ] at h
  exact G.greedyMate_eq_some ρ h

end Graph

end SteinerUpperBound.Matching
