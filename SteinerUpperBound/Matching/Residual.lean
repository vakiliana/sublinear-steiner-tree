module

public import SteinerUpperBound.Matching.Oracle

@[expose] public section

namespace SteinerUpperBound.Matching

open scoped Classical BigOperators

variable {V E : Type*} [Fintype E]

namespace Rank

def swapRanks (ρ : Rank E) (i j : Fin (Fintype.card E)) : Rank E :=
  ρ.trans (Equiv.swap i j)

@[simp] theorem swapRanks_apply (ρ : Rank E) (i j : Fin (Fintype.card E)) (e : E) :
    ρ.swapRanks i j e = Equiv.swap i j (ρ e) := rfl

@[simp] theorem swapRanks_edge (ρ : Rank E) (i j k : Fin (Fintype.card E)) :
    (ρ.swapRanks i j).edge k = ρ.edge (Equiv.swap i j k) := rfl

@[simp] theorem swapRanks_twice (ρ : Rank E) (i j : Fin (Fintype.card E)) :
    (ρ.swapRanks i j).swapRanks i j = ρ := by
  ext e
  simp [swapRanks]

def swapEquiv (i j : Fin (Fintype.card E)) : Rank E ≃ Rank E where
  toFun ρ := ρ.swapRanks i j
  invFun ρ := ρ.swapRanks i j
  left_inv ρ := ρ.swapRanks_twice i j
  right_inv ρ := ρ.swapRanks_twice i j

end Rank

namespace Graph

variable (G : Graph V E)

theorem greedyPrefix_congr {ρ σ : Rank E} (k : ℕ)
    (h : ∀ i < k, ρ.edgeAt i = σ.edgeAt i) :
    G.greedyPrefix ρ k = G.greedyPrefix σ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp := ih (fun i hi => h i (by omega))
    rw [greedyPrefix, greedyPrefix, hp, h k (by omega)]

theorem greedyPrefix_swap {ρ : Rank E} (k : ℕ)
    (i j : Fin (Fintype.card E)) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    G.greedyPrefix (ρ.swapRanks i j) k = G.greedyPrefix ρ k := by
  apply G.greedyPrefix_congr
  intro a ha
  have hap : a < Fintype.card E := lt_of_lt_of_le ha (hi.trans (Nat.le_of_lt i.isLt))
  rw [(ρ.swapRanks i j).edgeAt_eq_some a hap, ρ.edgeAt_eq_some a hap,
    Rank.swapRanks_edge]
  congr 2
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have hh := congrArg Fin.val h
    change a = i.val at hh
    omega
  · intro h
    have hh := congrArg Fin.val h
    change a = j.val at hh
    omega

variable (ρ : Rank E)

/-- Copies remaining after deleting the endpoints matched by the first `k` ranks. -/
noncomputable def residual (k : ℕ) : Finset E :=
  Finset.univ.filter fun e => G.Admissible (G.greedyPrefix ρ k) e

@[simp] theorem mem_residual (k : ℕ) (e : E) :
    e ∈ G.residual ρ k ↔ G.Admissible (G.greedyPrefix ρ k) e := by
  simp [residual]

theorem residual_antitone : Antitone (G.residual ρ) := by
  intro i j hij e he
  obtain ⟨hl, hr⟩ := (G.mem_residual ρ j e).mp he
  exact (G.mem_residual ρ i e).mpr
    ⟨G.free_mono (G.greedyPrefix_mono ρ hij) hl,
      G.free_mono (G.greedyPrefix_mono ρ hij) hr⟩

theorem residual_rank (k : ℕ) {e : E} (he : e ∈ G.residual ρ k) : k ≤ ρ.index e := by
  by_contra hk
  have hlt : ρ.index e < k := by omega
  have ha := (G.mem_residual ρ k e).mp he
  have he' : G.Accepted ρ e := by
    exact ⟨G.free_mono (G.greedyPrefix_mono ρ (Nat.le_of_lt hlt)) ha.1,
      G.free_mono (G.greedyPrefix_mono ρ (Nat.le_of_lt hlt)) ha.2⟩
  have hm := (G.mem_greedyPrefix ρ k e).mpr ⟨hlt, he'⟩
  exact ha.1 e hm (G.incident_left e)

theorem residual_swap (k : ℕ) (i j : Fin (Fintype.card E))
    (hi : k ≤ i.val) (hj : k ≤ j.val) :
    G.residual (ρ.swapRanks i j) k = G.residual ρ k := by
  simp only [residual, G.greedyPrefix_swap k i j hi hj]

/-- Closed neighborhood in the residual line graph, counting labeled copies. -/
noncomputable def residualNeighbors (k : ℕ) (e : E) : Finset E :=
  (G.residual ρ k).filter (G.Touch e)

@[simp] theorem mem_residualNeighbors (k : ℕ) (e f : E) :
    f ∈ G.residualNeighbors ρ k e ↔ f ∈ G.residual ρ k ∧ G.Touch e f := by
  simp [residualNeighbors]

theorem residualNeighbors_antitone (e : E) : Antitone (fun k => G.residualNeighbors ρ k e) := by
  intro i j hij f hf
  obtain ⟨hf, ht⟩ := (G.mem_residualNeighbors ρ j e f).mp hf
  exact (G.mem_residualNeighbors ρ i e f).mpr ⟨G.residual_antitone ρ hij hf, ht⟩

theorem residualNeighbors_swap (k : ℕ) (i j : Fin (Fintype.card E))
    (hi : k ≤ i.val) (hj : k ≤ j.val) (e : E) :
    G.residualNeighbors (ρ.swapRanks i j) k e = G.residualNeighbors ρ k e := by
  simp only [residualNeighbors, G.residual_swap ρ k i j hi hj]

theorem residual_killed (k : ℕ) (hk : k < Fintype.card E) (e : E)
    (hf : ρ.edge ⟨k, hk⟩ ∈ G.residualNeighbors ρ k e) :
    e ∉ G.residual ρ (k + 1) := by
  classical
  obtain ⟨hf, v, hev, hfv⟩ := (G.mem_residualNeighbors ρ k e _).mp hf
  have hfa := (G.mem_residual ρ k _).mp hf
  have hfm : ρ.edge ⟨k, hk⟩ ∈ G.greedyPrefix ρ (k + 1) := by
    rw [G.greedyPrefix_succ ρ k hk]
    simp [hfa]
  intro he
  obtain ⟨hl, hr⟩ := (G.mem_residual ρ (k + 1) e).mp he
  rcases hev with h | h
  · subst v
    exact hl _ hfm hfv
  · subst v
    exact hr _ hfm hfv

theorem residualNeighbors_card_le (k : ℕ) (e : E) :
    (G.residualNeighbors ρ k e).card ≤ Fintype.card E - k := by
  classical
  let S : Finset (Fin (Fintype.card E)) := Finset.univ.filter fun i => k ≤ i.val
  have hsub : (G.residualNeighbors ρ k e).image ρ ⊆ S := by
    intro i hi
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      G.residual_rank ρ k ((G.mem_residualNeighbors ρ k e f).mp hf).1⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ ρ.injective] at hcard
  have hs : S.card = Fintype.card E - k := by
    by_cases hk : k < Fintype.card E
    · have heq : S = Finset.Ici (⟨k, hk⟩ : Fin (Fintype.card E)) := by
        ext i
        simp [S, Fin.le_def]
      rw [heq, Fin.card_Ici]
    · have heq : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hki : k ≤ i.val := (Finset.mem_filter.mp hi).2
        omega
      simp [heq, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hk)]
  exact hs ▸ hcard

end Graph

end SteinerUpperBound.Matching
