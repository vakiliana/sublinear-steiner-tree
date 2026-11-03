module

public import SteinerUpperBound.BandEvaluation.Lookup

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

open QueryProgram SmallCoverProgram
open scoped Classical

variable {M Q : Type*} {n m : ℕ}

noncomputable def rawMST (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    Code M Q ℝ := (rawMatrix C d L).bind FiniteMST.program

noncomputable def rawMSTRun (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    Outcome ℝ :=
  (rawMatrixRun C d L).combine (FiniteMST.run (rawMatrixRun C d L).value)

theorem rawMST_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    Code.Evaluates oracle bits (rawMST C d L) (rawMSTRun C d L) :=
  Code.Evaluates.bind _ _ _ _ _ _ (rawMatrix_evaluates _ _ _ _ _) (FiniteMST.program_evaluates _ _ _)

theorem labels_asVector (L : List (Fin n)) : FiniteMST.labels (asVector L).get = L.toFinset := by
  ext x
  simp only [FiniteMST.mem_labels, List.mem_toFinset, List.mem_iff_get, asVector_get]

theorem rawMSTRun_correct (I : Instance (Fin n)) (C : Vector (Fin n) m)
    (d : MetricTable n m) (hd : ∀ i v, distanceAt d i v = I.distance (C.get i) v)
    (L : List (Fin n)) (hL : L.Nodup)
    (hobs : ∀ x ∈ L, ∀ y ∈ L, x = y ∨ x ∈ retained C ∨ y ∈ retained C) :
    (rawMSTRun C d L).value = TerminalMST.value I.weight L.toFinset := by
  have hnonneg : ∀ i v, 0 ≤ distanceAt d i v := by
    intro i v
    rw [hd]
    exact I.distance_nonneg _ _
  have hh := FiniteMST.on_labels_correct (rawMatrixRun C d L).value
    (rawMatrixRun_nonneg C d hnonneg L) I.weight I.weight_nonneg
    (asVector L).get (asVector_injective L hL)
    (fun i j _ => rawMatrixRun_correct I C d hd L hobs i j)
  simpa only [rawMSTRun, Outcome.combine, labels_asVector] using hh

theorem finite_work_poly {k : ℕ} (a : FiniteMST.Matrix k) :
    (FiniteMST.run a).work ≤ 1024 * (k + 1) ^ 7 := by
  have hl : 1 + Nat.log2 (k + 1) ≤ 2 * (k + 1) := by
    have hh := Nat.log2_le_self (k + 1)
    omega
  calc
    _ ≤ 512 * (k + 1) ^ 6 * (1 + Nat.log2 (k + 1)) := FiniteMST.run_work a
    _ ≤ 512 * (k + 1) ^ 6 * (2 * (k + 1)) := Nat.mul_le_mul_left _ hl
    _ = _ := by ring

theorem rawMSTRun_work_small (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n))
    (hL : L.length ≤ 5) : (rawMSTRun C d L).work ≤ 1000000000 * (m + 1) := by
  have hm := rawMatrixRun_work C d L
  have hk := finite_work_poly (rawMatrixRun C d L).value
  have hk2 : L.length ^ 2 ≤ 25 := by nlinarith
  have hmul := Nat.mul_le_mul_left (16 * m + 12) hk2
  have hp : (L.length + 1) ^ 7 ≤ 6 ^ 7 := by gcongr; omega
  have hpow := Nat.mul_le_mul_left 1024 hp
  norm_num at hpow
  dsimp only [rawMSTRun, Outcome.combine]
  nlinarith

theorem rawMSTRun_resources (C : Vector (Fin n) m) (d : MetricTable n m) (L : List (Fin n)) :
    (rawMSTRun C d L).metricQueries = 0 ∧ (rawMSTRun C d L).retentionQueries = 0 ∧
      (rawMSTRun C d L).positiveReplies = 0 := by
  have hm := rawMatrixRun_resources C d L
  have hk := FiniteMST.run_resources (rawMatrixRun C d L).value
  simp only [rawMSTRun, Outcome.combine, hm, hk, Nat.zero_add, and_self]

end SteinerUpperBound.BandEvaluation
