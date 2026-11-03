module

public import SteinerUpperBound.SavingScores.Clip
public import SteinerUpperBound.SetSystem.OrderedMatching

@[expose] public section

namespace SteinerUpperBound.SavingScores

open scoped Classical BigOperators

variable {X A R : Type*}

noncomputable def orderedGraph (order : List R) (E : Finset R)
    (rows : R → Finset A) (U : Finset A) (b : ℕ) :=
  SetSystem.mutualCopies U E (SetSystem.firstIncident order rows b)

noncomputable def orderedMean [Fintype X] [Nonempty X]
    (part : X → A) (hsurj : Function.Surjective part)
    (order : List R) (E : Finset R) (rows : R → Finset A)
    (covered U : Finset A) (b : ℕ) : ℝ :=
  scoreMean part hsurj covered U (orderedGraph order E rows U b)

theorem orderedMean_eq [Fintype X] [Fintype A] [Nonempty X]
    (part : X → A) (hsurj : Function.Surjective part)
    (order : List R) (E : Finset R) (rows : R → Finset A)
    (covered U : Finset A) (b : ℕ) (hdisj : Disjoint covered U) :
    orderedMean part hsurj order E rows covered U b =
      ((covered.card : ℝ) + expectedMatching (orderedGraph order E rows U b)) / (Nat.card X : ℝ) := by
  apply scoreMean_eq part hsurj covered U hdisj
  intro e
  have hh := (SetSystem.mutualCopies_realizes U E
    (SetSystem.firstIncident order rows b)).copy_adj e
  exact ⟨hh.1, hh.2.1⟩

theorem ordered_expectedMatching_half (order : List R) (horder : order.Nodup)
    (E : Finset R) (rows : R → Finset A) (hE : E ⊆ order.toFinset)
    (U : Finset A) (b : ℕ) (hb : 1 ≤ b)
    (hineligible : ∀ r ∈ order.toFinset, r ∉ E → (U ∩ rows r).card ≤ 2) :
    SetSystem.saving E rows U / 2 - (order.toFinset.card : ℝ) / b ≤
        expectedMatching (orderedGraph order E rows U b) ∧
      expectedMatching (orderedGraph order E rows U b) ≤ SetSystem.saving E rows U :=
  SetSystem.orderedMutual_expected_half order horder E rows hE U b hb hineligible
    (Matching.Rank.uniform (E := SetSystem.MutualCopy U E
      (SetSystem.firstIncident order rows b)))

theorem ordered_Z_contract [Fintype X] [Fintype A] [Nonempty X]
    (part : X → A) (hsurj : Function.Surjective part)
    (order : List R) (horder : order.Nodup)
    (E : Finset R) (rows : R → Finset A) (hE : E ⊆ order.toFinset)
    (large covered U : Finset A) (S : Finset R) (s : ℕ)
    (hparts : (Finset.univ : Finset A) ⊆ large ∪ covered ∪ U)
    (hdisj : Disjoint covered U) (hcover : covered ⊆ S.biUnion rows)
    (hS : S ⊆ order.toFinset) (hs : S.card ≤ s)
    (hineligible : ∀ r ∈ order.toFinset, r ∉ E → (rows r).card ≤ 2)
    (b : ℕ) (hb : 1 ≤ b)
    (gminus empirical xi : ℝ) (hxi₀ : 0 ≤ xi) (hxi₁ : xi ≤ 1)
    (hcal : (1 - xi) * (Nat.card X : ℝ) ≤ gminus) (hcal₁ : gminus ≤ Nat.card X)
    (he : |empirical - orderedMean part hsurj order E rows covered U b| ≤ xi) :
    0 ≤ Z gminus empirical xi s ∧ Z gminus empirical xi s ≤ fullSaving E rows ∧
      fullSaving E rows / 2 - (large.card : ℝ) / 2 - (order.toFinset.card : ℝ) / b -
          2 * s - 3 * xi * Nat.card X ≤ Z gminus empirical xi s :=
  capped_Z_contract part hsurj order.toFinset E rows hE large covered U S s
    hparts hdisj hcover hS hs hineligible b hb
    (SetSystem.orderedCap order horder rows U b)
    (orderedGraph order E rows U b)
    (SetSystem.mutualCopies_realizes U E (SetSystem.firstIncident order rows b))
    gminus empirical xi hxi₀ hxi₁ hcal hcal₁ he

end SteinerUpperBound.SavingScores
