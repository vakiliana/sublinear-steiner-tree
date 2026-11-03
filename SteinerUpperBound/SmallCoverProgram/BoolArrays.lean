module

public import SteinerUpperBound.SmallCoverProgram.Rows

@[expose] public section

namespace SteinerUpperBound.SmallCoverProgram

open QueryProgram
open scoped Classical

variable {M Q : Type*} {g : ℕ}

def bits (v : Vector Bool g) : Finset (Fin g) :=
  Finset.univ.filter (fun i => v.get i = true)

theorem mem_bits (v : Vector Bool g) (i : Fin g) : i ∈ bits v ↔ v.get i = true := by
  simp [bits]

def countStep (row claimed : Vector Bool g) (c : ℕ × ℕ) (i : Fin g) : ℕ × ℕ :=
  if row.get i then (c.1 + 1, c.2 + if claimed.get i then 0 else 1) else c

def counts (row claimed : Vector Bool g) : Code M Q (ℕ × ℕ) :=
  Code.foldList (fun c i => .tick 7 (.pure (countStep row claimed c i))) (List.finRange g) (0, 0)

def countsRun (row claimed : Vector Bool g) : Outcome (ℕ × ℕ) :=
  Code.folded (fun c i => ⟨countStep row claimed c i, 8, 0, 0, 0⟩) (List.finRange g) (0, 0)

theorem counts_evaluates (m : M → ℝ) (b : Q → Bool) (row claimed : Vector Bool g) :
    Code.Evaluates m b (counts row claimed) (countsRun row claimed) := by
  apply Code.foldList_evaluates
  intro c i
  exact Code.Evaluates.tick m b _ _ (Code.evaluates_pure m b _) 7

theorem countFold (row claimed : Vector Bool g) (l : List (Fin g)) (c : ℕ × ℕ) :
    l.foldl (countStep row claimed) c =
      (c.1 + (l.filter row.get).length,
        c.2 + (l.filter (fun i => row.get i && !claimed.get i)).length) := by
  induction l generalizing c with
  | nil => simp
  | cons i l ih =>
      rw [List.foldl_cons, ih]
      cases hr : row.get i <;> cases hc : claimed.get i <;>
        simp [countStep, hr, hc, Nat.add_assoc, Nat.add_comm]

theorem filter_finRange_card (p : Fin g → Bool) :
    ((List.finRange g).filter p).length = (Finset.univ.filter (fun i => p i = true)).card := by
  have hn := (List.nodup_finRange g).filter p
  have hh := List.toFinset_card_of_nodup hn
  have he : ((List.finRange g).filter p).toFinset = Finset.univ.filter (fun i => p i = true) := by
    ext i
    simp
  rw [he] at hh
  exact hh.symm

theorem countsRun_value (row claimed : Vector Bool g) :
    (countsRun row claimed).value = ((bits row).card, (bits row \ bits claimed).card) := by
  rw [countsRun, folded_value]
  change (List.finRange g).foldl (countStep row claimed) (0, 0) = _
  rw [countFold]
  simp only [Nat.zero_add, filter_finRange_card]
  congr 1
  apply congrArg Finset.card
  ext i
  simp [bits]

def claim (row claimed : Vector Bool g) : Code M Q (Vector Bool g) :=
  tabulate (fun i => .tick 3 (.pure (claimed.get i || row.get i))) claimed

def claimRun (row claimed : Vector Bool g) : Outcome (Vector Bool g) :=
  tabulated (fun i => ⟨claimed.get i || row.get i, 4, 0, 0, 0⟩) claimed

theorem claim_evaluates (m : M → ℝ) (b : Q → Bool) (row claimed : Vector Bool g) :
    Code.Evaluates m b (claim row claimed) (claimRun row claimed) := by
  apply tabulate_evaluates
  intro i
  exact Code.Evaluates.tick m b _ _ (Code.evaluates_pure m b _) 3

theorem claimRun_get (row claimed : Vector Bool g) (i : Fin g) :
    (claimRun row claimed).value.get i = (claimed.get i || row.get i) :=
  tabulated_get _ _ i

theorem claimRun_bits (row claimed : Vector Bool g) :
    bits (claimRun row claimed).value = bits claimed ∪ bits row := by
  ext i
  simp only [mem_bits, claimRun_get, Finset.mem_union, Bool.or_eq_true]

theorem countsRun_work (row claimed : Vector Bool g) : (countsRun row claimed).work ≤ 9 * g := by
  have hh := Code.folded_work (fun c i => (⟨countStep row claimed c i, 8, 0, 0, 0⟩ : Outcome (ℕ × ℕ)))
    8 (fun _ _ => le_rfl) (List.finRange g) (0, 0)
  simpa [countsRun] using hh

theorem claimRun_work (row claimed : Vector Bool g) : (claimRun row claimed).work ≤ 6 * g := by
  simpa only [claimRun] using
    tabulated_work (fun i => (⟨claimed.get i || row.get i, 4, 0, 0, 0⟩ : Outcome Bool))
      claimed 4 (fun _ => le_rfl)

theorem countsRun_resources (row claimed : Vector Bool g) :
    (countsRun row claimed).metricQueries = 0 ∧ (countsRun row claimed).retentionQueries = 0 ∧
      (countsRun row claimed).positiveReplies = 0 := by
  let step := fun c i => (⟨countStep row claimed c i, 8, 0, 0, 0⟩ : Outcome (ℕ × ℕ))
  have hm := Code.folded_metric_queries step 0 (fun _ _ => le_rfl) (List.finRange g) (0, 0)
  have hr := folded_retention_zero step (fun _ _ => rfl) (List.finRange g) (0, 0)
  have hp := folded_positive_zero step (fun _ _ => rfl) (List.finRange g) (0, 0)
  simpa only [countsRun] using
    (And.intro (by simpa only [Nat.zero_mul, Nat.le_zero] using hm) (And.intro hr hp))

theorem claimRun_resources (row claimed : Vector Bool g) :
    (claimRun row claimed).metricQueries = 0 ∧ (claimRun row claimed).retentionQueries = 0 ∧
      (claimRun row claimed).positiveReplies = 0 := by
  let step := fun i => (⟨claimed.get i || row.get i, 4, 0, 0, 0⟩ : Outcome Bool)
  have hm := tabulated_metricQueries step claimed 0 (fun _ => le_rfl)
  have hr := tabulated_retention_zero step claimed (fun _ => rfl)
  have hp := tabulated_positive_zero step claimed (fun _ => rfl)
  simpa only [claimRun] using
    (And.intro (by simpa only [Nat.zero_mul, Nat.le_zero] using hm) (And.intro hr hp))

end SteinerUpperBound.SmallCoverProgram
