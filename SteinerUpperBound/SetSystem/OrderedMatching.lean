module

public import SteinerUpperBound.SetSystem.CappedMatching

@[expose] public section

namespace SteinerUpperBound.SetSystem

open scoped Classical BigOperators

variable {R U : Type*}

/-- Row and endpoint labels are retained, including parallel copies from different rows. -/
def MutualCopy (A : Finset U) (E : Finset R) (L : U → Finset R) :=
  {p : ↥E × (↥A × ↥A) //
    p.2.1.val ≠ p.2.2.val ∧ p.1.val ∈ L p.2.1.val ∧ p.1.val ∈ L p.2.2.val}

noncomputable instance (A : Finset U) (E : Finset R) (L : U → Finset R) :
    Fintype (MutualCopy A E L) := by
  classical
  unfold MutualCopy
  infer_instance

def mutualCopies (A : Finset U) (E : Finset R) (L : U → Finset R) :
    Matching.Graph U (MutualCopy A E L) where
  left d := d.val.2.1.val
  right d := d.val.2.2.val
  loopless d := d.property.1

theorem mutualCopies_realizes (A : Finset U) (E : Finset R) (L : U → Finset R) :
    Realizes (mutualCopies A E L) (mutualGraph A E L) := by
  intro x y
  constructor
  · rintro ⟨hx, hy, hxy, r, hr, hrl, hrr⟩
    let d : MutualCopy A E L :=
      ⟨(⟨r, hr⟩, (⟨x, hx⟩, ⟨y, hy⟩)), hxy, hrl, hrr⟩
    exact ⟨d, Or.inl ⟨rfl, rfl⟩⟩
  · rintro ⟨d, hd | hd⟩
    · obtain ⟨rfl, rfl⟩ := hd
      exact ⟨d.val.2.1.property, d.val.2.2.property, d.property.1,
        d.val.1.val, d.val.1.property, d.property.2⟩
    · obtain ⟨rfl, rfl⟩ := hd
      exact ⟨d.val.2.2.property, d.val.2.1.property, d.property.1.symm,
        d.val.1.val, d.val.1.property, d.property.2.2, d.property.2.1⟩

theorem orderedMutual_greedy_half (order : List R) (horder : order.Nodup)
    (E : Finset R) (rows : R → Finset U) (hE : E ⊆ order.toFinset)
    (A : Finset U) (b : ℕ) (hb : 1 ≤ b)
    (hineligible : ∀ r ∈ order.toFinset, r ∉ E → (A ∩ rows r).card ≤ 2)
    (rank : Matching.Rank (MutualCopy A E (firstIncident order rows b))) :
    saving E rows A / 2 - order.toFinset.card / b ≤
      (((mutualCopies A E (firstIncident order rows b)).greedy rank).card : ℝ) ∧
      (((mutualCopies A E (firstIncident order rows b)).greedy rank).card : ℝ) ≤
        saving E rows A :=
  mutualCap_greedy_half order.toFinset E rows hE A b hb
    (orderedCap order horder rows A b) hineligible
    (mutualCopies A E (firstIncident order rows b))
    (mutualCopies_realizes A E (firstIncident order rows b)) rank

theorem orderedMutual_expected_half (order : List R) (horder : order.Nodup)
    (E : Finset R) (rows : R → Finset U) (hE : E ⊆ order.toFinset)
    (A : Finset U) (b : ℕ) (hb : 1 ≤ b)
    (hineligible : ∀ r ∈ order.toFinset, r ∉ E → (A ∩ rows r).card ≤ 2)
    (μ : SteinerLowerBound.Law
      (Matching.Rank (MutualCopy A E (firstIncident order rows b)))) :
    saving E rows A / 2 - order.toFinset.card / b ≤
      μ.expect (fun rank => ((mutualCopies A E (firstIncident order rows b)).greedy rank).card) ∧
      μ.expect (fun rank => ((mutualCopies A E (firstIncident order rows b)).greedy rank).card) ≤
        saving E rows A :=
  mutualCap_expected_greedy_half order.toFinset E rows hE A b hb
    (orderedCap order horder rows A b) hineligible
    (mutualCopies A E (firstIncident order rows b))
    (mutualCopies_realizes A E (firstIncident order rows b)) μ

end SteinerUpperBound.SetSystem
