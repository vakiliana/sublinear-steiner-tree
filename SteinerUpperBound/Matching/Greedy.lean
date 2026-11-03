module

public import SteinerUpperBound.Matching.Basic

@[expose] public section

namespace SteinerUpperBound.Matching

open scoped Classical BigOperators

variable {V E : Type*} [Fintype E]

namespace Graph

variable (G : Graph V E) (ρ : Rank E)

def Admissible (M : Finset E) (e : E) : Prop :=
  G.Free M (G.left e) ∧ G.Free M (G.right e)

/-- The sequential algorithm after inspecting the first `k` ranks. -/
noncomputable def greedyPrefix (G : Graph V E) (ρ : Rank E) : ℕ → Finset E
  | 0 => ∅
  | k + 1 =>
    match ρ.edgeAt k with
    | none => greedyPrefix G ρ k
    | some e =>
      if G.Admissible (greedyPrefix G ρ k) e then
        insert e (greedyPrefix G ρ k)
      else greedyPrefix G ρ k

@[simp] theorem greedyPrefix_zero : G.greedyPrefix ρ 0 = ∅ := rfl

theorem greedyPrefix_succ (k : ℕ) (hk : k < Fintype.card E) :
    G.greedyPrefix ρ (k + 1) =
      if G.Admissible (G.greedyPrefix ρ k) (ρ.edge ⟨k, hk⟩) then
        insert (ρ.edge ⟨k, hk⟩) (G.greedyPrefix ρ k)
      else G.greedyPrefix ρ k := by
  rw [greedyPrefix, ρ.edgeAt_eq_some k hk]

theorem greedyPrefix_succ_of_ge (k : ℕ) (hk : Fintype.card E ≤ k) :
    G.greedyPrefix ρ (k + 1) = G.greedyPrefix ρ k := by
  rw [greedyPrefix, ρ.edgeAt_eq_none k hk]

theorem greedyPrefix_subset_succ (k : ℕ) :
    G.greedyPrefix ρ k ⊆ G.greedyPrefix ρ (k + 1) := by
  classical
  by_cases hk : k < Fintype.card E
  · rw [G.greedyPrefix_succ ρ k hk]
    split_ifs
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _
  · rw [G.greedyPrefix_succ_of_ge ρ k (Nat.le_of_not_gt hk)]

theorem greedyPrefix_mono : Monotone (G.greedyPrefix ρ) :=
  monotone_nat_of_le_succ (G.greedyPrefix_subset_succ ρ)

/-- The acceptance decision when the copy's own rank is inspected. -/
def Accepted (e : E) : Prop :=
  G.Admissible (G.greedyPrefix ρ (ρ.index e)) e

theorem mem_greedyPrefix (k : ℕ) (e : E) :
    e ∈ G.greedyPrefix ρ k ↔ ρ.index e < k ∧ G.Accepted ρ e := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k < Fintype.card E
    · rw [G.greedyPrefix_succ ρ k hk]
      by_cases he : e = ρ.edge ⟨k, hk⟩
      · subst e
        have hi := ρ.index_at ⟨k, hk⟩
        simp only [Accepted, hi, Nat.lt_succ_self, true_and]
        split_ifs with ha
        · simp [ha]
        · simp [ih, hi, ha]
      · have hi : ρ.index e ≠ k := by
          intro h
          exact he (ρ.index_injective (by simpa using h))
        have hlt : ρ.index e < k + 1 ↔ ρ.index e < k := by omega
        split_ifs <;> simp [he, ih, hlt]
    · rw [G.greedyPrefix_succ_of_ge ρ k (Nat.le_of_not_gt hk), ih]
      have he := ρ.index_lt e
      have hlt : ρ.index e < k := by omega
      simp [hlt, Nat.lt_succ_of_lt hlt]

theorem accepted_iff_free (e : E) :
    G.Accepted ρ e ↔
      G.Free (G.greedyPrefix ρ (ρ.index e)) (G.left e) ∧
      G.Free (G.greedyPrefix ρ (ρ.index e)) (G.right e) := Iff.rfl

/-- The actual random-greedy output for the specified rank assignment. -/
noncomputable def greedy : Finset E := G.greedyPrefix ρ (Fintype.card E)

@[simp] theorem mem_greedy (e : E) : e ∈ G.greedy ρ ↔ G.Accepted ρ e := by
  simp [greedy, G.mem_greedyPrefix, ρ.index_lt e]

theorem free_prefix_iff (k : ℕ) (v : V) :
    G.Free (G.greedyPrefix ρ k) v ↔
      ∀ e ∈ G.greedy ρ, ρ.index e < k → ¬ G.Incident e v := by
  simp only [Free, G.mem_greedyPrefix, G.mem_greedy]
  constructor
  · intro h e he hk
    exact h e ⟨hk, he⟩
  · intro h e ⟨hk, he⟩
    exact h e he hk

omit [Fintype E] in
theorem admissible_iff_no_touch (M : Finset E) (e : E) :
    G.Admissible M e ↔ ∀ f ∈ M, ¬ G.Touch f e := by
  constructor
  · rintro ⟨hl, hr⟩ f hf ⟨v, hfv, hev⟩
    rcases hev with h | h
    · subst v
      exact hl f hf hfv
    · subst v
      exact hr f hf hfv
  · intro h
    constructor
    · intro f hf hfv
      exact h f hf ⟨_, hfv, G.incident_left e⟩
    · intro f hf hfv
      exact h f hf ⟨_, hfv, G.incident_right e⟩

theorem greedy_isMatching : G.IsMatching (G.greedy ρ) := by
  intro e he f hf htouch
  by_contra hne
  have hrne : ρ.index e ≠ ρ.index f := fun h => hne (ρ.index_injective h)
  rcases lt_or_gt_of_ne hrne with hlt | hgt
  · have he' : e ∈ G.greedyPrefix ρ (ρ.index f) :=
      (G.mem_greedyPrefix ρ _ _).mpr ⟨hlt, (G.mem_greedy ρ e).mp he⟩
    exact ((G.admissible_iff_no_touch _ f).mp ((G.mem_greedy ρ f).mp hf)) e he' htouch
  · have hf' : f ∈ G.greedyPrefix ρ (ρ.index e) :=
      (G.mem_greedyPrefix ρ _ _).mpr ⟨hgt, (G.mem_greedy ρ f).mp hf⟩
    exact ((G.admissible_iff_no_touch _ e).mp ((G.mem_greedy ρ e).mp he)) f hf'
      (G.touch_symm htouch)

theorem rejected_blocker (e : E) (he : e ∉ G.greedy ρ) :
    ∃ f ∈ G.greedy ρ, ρ.index f < ρ.index e ∧ G.Touch f e := by
  have hna : ¬ G.Admissible (G.greedyPrefix ρ (ρ.index e)) e := by
    simpa only [G.mem_greedy, Accepted] using he
  rw [G.admissible_iff_no_touch] at hna
  push Not at hna
  obtain ⟨f, hf, ht⟩ := hna
  obtain ⟨hr, ha⟩ := (G.mem_greedyPrefix ρ _ f).mp hf
  exact ⟨f, (G.mem_greedy ρ f).mpr ha, hr, ht⟩

theorem greedy_isMaximalMatching : G.IsMaximalMatching (G.greedy ρ) := by
  refine ⟨G.greedy_isMatching ρ, ?_⟩
  intro e
  by_cases he : e ∈ G.greedy ρ
  · exact ⟨e, he, G.left e, G.incident_left e, G.incident_left e⟩
  · obtain ⟨f, hf, _, ht⟩ := G.rejected_blocker ρ e he
    exact ⟨f, hf, G.touch_symm ht⟩

theorem accepted_at_free_tail (d : Directed E)
    (ht : G.Free (G.greedyPrefix ρ (ρ.index d.1)) (G.tail d)) :
    G.Accepted ρ d.1 ↔
      G.Free (G.greedyPrefix ρ (ρ.index d.1)) (G.head d) := by
  cases d with
  | mk e b =>
    cases b
    · simpa only [tail, head, Bool.false_eq_true, ↓reduceIte, Accepted, Admissible]
        using and_iff_left ht
    · simpa only [tail, head, ↓reduceIte, Accepted, Admissible]
        using and_iff_right ht

theorem accepted_free_head (d : Directed E) (h : G.Accepted ρ d.1) :
    G.Free (G.greedyPrefix ρ (ρ.index d.1)) (G.head d) := by
  cases d with | mk e b => cases b <;> first | exact h.1 | exact h.2

theorem accepted_free_tail (d : Directed E) (h : G.Accepted ρ d.1) :
    G.Free (G.greedyPrefix ρ (ρ.index d.1)) (G.tail d) := by
  cases d with | mk e b => cases b <;> first | exact h.1 | exact h.2

end Graph

end SteinerUpperBound.Matching
