module

public import SteinerUpperBound.LargeCoverProgram.Cache
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical

variable {Q : Type*} {n k : ℕ}

def smallWork (n k : ℕ) (p : Parameters) : ℕ :=
  16 * (k + 2) + 128 * (n * smallLimit p +
    smallLimit p ^ 3 * (1 + Nat.log2 (smallLimit p + 1)))

/-- The size guard makes ordinary small-branch work PUBLICLY bounded even on
bad calibration. Disclosures are bounded by the actual retained size. -/
theorem small_resources (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ)
    (gm gp : ℚ) (c : Cache Q) (hc : Cache.Correct bits c) (hnd : terminals.toList.Nodup) :
    ∀ o, Runs w bits (small p terminals key a gm gp c) o →
      o.work ≤ smallWork n k p ∧
      o.positiveReplies ≤ (ComponentExplore.retained bits key terminals.toList.toFinset).card := by
  intro o ho
  have he := deterministic_run_eq w bits _ (small_deterministic p terminals key a gm gp c)
    _ (small_evaluates w bits p terminals key a gm gp c) o ho
  subst o
  let r := LocalAccess.revealResult bits key terminals.toList c
  have hr := LocalAccess.reveal_correct bits key terminals.toList c hc
  have hn : r.value.points.Nodup := by
    change (LocalAccess.revealResult bits key terminals.toList c).value.points.Nodup
    rw [hr.1]
    exact hnd.filter _
  have hlen : r.value.points.length ≤ k + 1 := by
    change (LocalAccess.revealResult bits key terminals.toList c).value.points.length ≤ k + 1
    rw [hr.1]
    exact (List.length_filter_le _ _).trans_eq (by simp)
  have hcard : r.value.points.length =
      (ComponentExplore.retained bits key terminals.toList.toFinset).card := by
    rw [← List.toFinset_card_of_nodup hn, reveal_set bits key terminals c hc]
  have hrw := LocalAccess.reveal_work bits key terminals.toList c
  have hrp := LocalAccess.reveal_positive bits key terminals.toList c
  have hl := length_result r.value.points
  have hgreedy := SmallCoverProgram.run_resources w r.value.points a
  have hrw' : r.work ≤ 7 * (k + 1) + 1 := by simpa only [Vector.length_toList] using hrw
  have hrp' : r.positiveReplies ≤
      (ComponentExplore.retained bits key terminals.toList.toFinset).card := by
    exact hrp.trans hcard.le
  by_cases hs : (lengthResult r.value.points).value ≤ smallLimit p
  · have hs' : r.value.points.length ≤ smallLimit p := by simpa only [hl.1] using hs
    have hw := SmallCoverProgram.run_work w r.value.points hn a
    have hlog : Nat.log2 (r.value.points.length + 1) ≤ Nat.log2 (smallLimit p + 1) := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact Nat.log_mono_right (Nat.add_le_add_right hs' 1)
    have hupper : n * r.value.points.length +
        r.value.points.length ^ 3 * (1 + Nat.log2 (r.value.points.length + 1)) ≤
          n * smallLimit p + smallLimit p ^ 3 * (1 + Nat.log2 (smallLimit p + 1)) := by gcongr
    have hwork := hw.trans (Nat.mul_le_mul_left 128 hupper)
    simp only [smallResult, show (LocalAccess.revealResult bits key terminals.toList c) = r from rfl,
      hs, ite_true, Outcome.combine, Outcome.add, Outcome.pure, hl.2.1, hl.2.2.2.2,
      hgreedy.2, Nat.add_zero, Nat.zero_add]
    constructor
    · dsimp [smallWork]
      omega
    · exact hrp'
  · simp only [smallResult, show (LocalAccess.revealResult bits key terminals.toList c) = r from rfl,
      hs, ite_false, Outcome.combine, Outcome.add, Outcome.pure, hl.2.1, hl.2.2.2.2,
      Nat.add_zero, Nat.zero_add]
    constructor
    · dsimp [smallWork]
      omega
    · exact hrp'

end SteinerUpperBound.LargeCoverProgram
