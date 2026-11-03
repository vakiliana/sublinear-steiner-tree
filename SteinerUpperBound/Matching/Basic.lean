module

public import SteinerLowerBound.FiniteProbability

@[expose] public section

/-!
# Labeled loopless multigraphs and orders of their copies

`E` is a type of copy identifiers, not a set of unordered endpoint pairs.
In particular, none of the definitions identify parallel copies.
-/

namespace SteinerUpperBound.Matching

open scoped Classical BigOperators

structure Graph (V E : Type*) where
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e

namespace Graph

variable {V E : Type*} (G : Graph V E)

def Incident (e : E) (v : V) : Prop := G.left e = v ∨ G.right e = v

@[simp] theorem incident_left (e : E) : G.Incident e (G.left e) := Or.inl rfl

@[simp] theorem incident_right (e : E) : G.Incident e (G.right e) := Or.inr rfl

def Touch (e f : E) : Prop := ∃ v, G.Incident e v ∧ G.Incident f v

theorem touch_symm {e f : E} (h : G.Touch e f) : G.Touch f e := by
  obtain ⟨v, he, hf⟩ := h
  exact ⟨v, hf, he⟩

def IsMatching (M : Finset E) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, G.Touch e f → e = f

def IsMaximalMatching (M : Finset E) : Prop :=
  G.IsMatching M ∧ ∀ e, ∃ f ∈ M, G.Touch e f

def Free (M : Finset E) (v : V) : Prop := ∀ e ∈ M, ¬ G.Incident e v

theorem free_mono {M M' : Finset E} (h : M ⊆ M') {v : V}
    (hv : G.Free M' v) : G.Free M v := fun e he => hv e (h he)

noncomputable def degree [Fintype E] (v : V) : ℕ :=
  (Finset.univ.filter fun e => G.Incident e v).card

/-- The Boolean selects the head: `false` is the left endpoint. -/
abbrev Directed (E : Type*) := E × Bool

def head (d : Directed E) : V :=
  match d.2 with
  | false => G.left d.1
  | true => G.right d.1

def tail (d : Directed E) : V :=
  match d.2 with
  | false => G.right d.1
  | true => G.left d.1

@[simp] theorem head_incident (d : Directed E) : G.Incident d.1 (G.head d) := by
  cases d with | mk e b => cases b <;> simp [head]

@[simp] theorem tail_incident (d : Directed E) : G.Incident d.1 (G.tail d) := by
  cases d with | mk e b => cases b <;> simp [tail]

theorem head_ne_tail (d : Directed E) : G.head d ≠ G.tail d := by
  cases d with
  | mk e b =>
    cases b
    · exact G.loopless e
    · exact (G.loopless e).symm

/-- Orient an incident copy away from the vertex whose list is being scanned. -/
noncomputable def away (v : V) (e : E) : Directed E :=
  (e, decide (G.left e = v))

@[simp] theorem away_edge (v : V) (e : E) : (G.away v e).1 = e := rfl

theorem tail_away {v : V} {e : E} (h : G.Incident e v) :
    G.tail (G.away v e) = v := by
  rcases h with h | h
  · simp [away, tail, h]
  · have hl : G.left e ≠ v := by simpa [← h] using G.loopless e
    simp [away, tail, h, hl]

theorem away_head {v : V} {e : E} (h : G.Incident e v) :
    G.Incident e (G.head (G.away v e)) ∧ G.head (G.away v e) ≠ v := by
  exact ⟨G.head_incident (G.away v e),
    by simpa [G.tail_away h] using G.head_ne_tail (G.away v e)⟩

theorem directed_eq_of_tail {d d' : Directed E} (he : d.1 = d'.1)
    (ht : G.tail d = G.tail d') : d = d' := by
  cases d with
  | mk e b =>
    cases d' with
    | mk e' b' =>
      simp only [Prod.mk.injEq] at he ⊢
      subst e'
      cases b <;> cases b' <;> simp_all [tail, G.loopless, Ne.symm]

theorem directed_eq_of_head {d d' : Directed E} (he : d.1 = d'.1)
    (hh : G.head d = G.head d') : d = d' := by
  cases d with
  | mk e b =>
    cases d' with
    | mk e' b' =>
      simp only [Prod.mk.injEq] at he ⊢
      subst e'
      cases b <;> cases b' <;> simp_all [head, G.loopless, Ne.symm]

theorem away_tail (d : Directed E) : G.away (G.tail d) d.1 = d :=
  G.directed_eq_of_tail rfl (G.tail_away (G.tail_incident d))

theorem incident_iff_endpoints (e : E) (v : V) :
    G.Incident e v ↔ G.left e = v ∨ G.right e = v := Iff.rfl

end Graph

variable {V E : Type*} [Fintype E]

/-- A bijective rank assignment, including the unique empty assignment. -/
abbrev Rank (E : Type*) [Fintype E] := E ≃ Fin (Fintype.card E)

namespace Rank

def index (ρ : Rank E) (e : E) : ℕ := (ρ e).val

@[simp] theorem index_lt (ρ : Rank E) (e : E) : ρ.index e < Fintype.card E :=
  (ρ e).isLt

theorem index_injective (ρ : Rank E) : Function.Injective ρ.index :=
  fun _ _ h => ρ.injective (Fin.ext h)

def edge (ρ : Rank E) (k : Fin (Fintype.card E)) : E := ρ.symm k

@[simp] theorem index_at (ρ : Rank E) (k : Fin (Fintype.card E)) :
    ρ.index (ρ.edge k) = k.val := by simp [index, edge]

@[simp] theorem at_index (ρ : Rank E) (e : E) : ρ.edge (ρ e) = e := ρ.symm_apply_apply e

def edgeAt (ρ : Rank E) (k : ℕ) : Option E :=
  if h : k < Fintype.card E then some (ρ.edge ⟨k, h⟩) else none

theorem edgeAt_eq_some (ρ : Rank E) (k : ℕ) (hk : k < Fintype.card E) :
    ρ.edgeAt k = some (ρ.edge ⟨k, hk⟩) := by simp [edgeAt, hk]

theorem edgeAt_eq_none (ρ : Rank E) (k : ℕ) (hk : Fintype.card E ≤ k) :
    ρ.edgeAt k = none := by simp [edgeAt, Nat.not_lt.mpr hk]

theorem edgeAt_eq_some_iff (ρ : Rank E) (k : ℕ) (e : E) :
    ρ.edgeAt k = some e ↔ ρ.index e = k := by
  by_cases hk : k < Fintype.card E
  · rw [ρ.edgeAt_eq_some k hk, Option.some.injEq]
    constructor
    · intro h
      rw [← h, ρ.index_at]
    · intro h
      exact ρ.index_injective (by simpa using h.symm)
  · rw [ρ.edgeAt_eq_none k (Nat.le_of_not_gt hk)]
    constructor
    · simp
    · intro h
      exact (hk (h ▸ ρ.index_lt e)).elim

/-- Increasing enumeration of the copies of rank strictly below `k`. -/
def edgesBelow (ρ : Rank E) (k : ℕ) : List E :=
  (List.range k).filterMap ρ.edgeAt

@[simp] theorem edgesBelow_zero (ρ : Rank E) : ρ.edgesBelow 0 = [] := rfl

@[simp] theorem mem_edgesBelow (ρ : Rank E) (k : ℕ) (e : E) :
    e ∈ ρ.edgesBelow k ↔ ρ.index e < k := by
  simp only [edgesBelow, List.mem_filterMap, List.mem_range, ρ.edgeAt_eq_some_iff]
  constructor
  · rintro ⟨i, hi, he⟩
    omega
  · intro h
    exact ⟨ρ.index e, h, rfl⟩

theorem edgesBelow_succ (ρ : Rank E) (k : ℕ) (hk : k < Fintype.card E) :
    ρ.edgesBelow (k + 1) = ρ.edgesBelow k ++ [ρ.edge ⟨k, hk⟩] := by
  simp [edgesBelow, List.range_succ, ρ.edgeAt_eq_some k hk]

theorem edgesBelow_succ_of_ge (ρ : Rank E) (k : ℕ) (hk : Fintype.card E ≤ k) :
    ρ.edgesBelow (k + 1) = ρ.edgesBelow k := by
  simp [edgesBelow, List.range_succ, ρ.edgeAt_eq_none k hk]

theorem edgesBelow_nodup (ρ : Rank E) (k : ℕ) : (ρ.edgesBelow k).Nodup := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k < Fintype.card E
    · rw [ρ.edgesBelow_succ k hk, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      have hb' : b = ρ.edge ⟨k, hk⟩ := by simpa using hb
      subst b
      have ha' := (ρ.mem_edgesBelow k a).mp ha
      intro h
      simp [h] at ha'
    · rw [ρ.edgesBelow_succ_of_ge k (Nat.le_of_not_gt hk)]
      exact ih

theorem edgesBelow_pairwise (ρ : Rank E) (k : ℕ) :
    (ρ.edgesBelow k).Pairwise (fun e f => ρ.index e < ρ.index f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k < Fintype.card E
    · rw [ρ.edgesBelow_succ k hk, List.pairwise_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      have hb' : b = ρ.edge ⟨k, hk⟩ := by simpa using hb
      subst b
      simpa using (ρ.mem_edgesBelow k a).mp ha
    · rw [ρ.edgesBelow_succ_of_ge k (Nat.le_of_not_gt hk)]
      exact ih

noncomputable instance : Nonempty (Rank E) := ⟨Fintype.equivFin E⟩

noncomputable def uniform : SteinerLowerBound.Law (Rank E) :=
  SteinerLowerBound.Law.uniform _

end Rank

end SteinerUpperBound.Matching
