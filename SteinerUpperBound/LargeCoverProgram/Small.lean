module

public import SteinerUpperBound.LargeCoverProgram.Basic

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

variable {Q : Type*} {n k : ℕ}

noncomputable def smallResult (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ)
    (gminus gplus : ℚ) (cache : Cache Q) : Outcome (Answer Q n) :=
  let revealed := LocalAccess.revealResult bits key terminals.toList cache
  let len := lengthResult revealed.value.points
  let tail : Outcome (Answer Q n) :=
    if len.value ≤ smallLimit p then
      let greedy := SmallCoverProgram.run w revealed.value.points a
      greedy.combine ((Outcome.pure ⟨some greedy.value, revealed.value.cache, true,
        gminus, gplus, ⟨[], 0⟩, none, none⟩).add 8 0 0 0)
    else Outcome.pure (abort revealed.value.cache gminus gplus true)
  revealed.combine (len.combine (tail.add 4 0 0 0))

theorem small_evaluates (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ)
    (gminus gplus : ℚ) (cache : Cache Q) :
    Code.Evaluates w bits (small p terminals key a gminus gplus cache)
      (smallResult w bits p terminals key a gminus gplus cache) := by
  intro F
  simp only [small, Code.evaluate_bind]
  rw [LocalAccess.reveal_evaluates w bits, length_evaluates w bits]
  by_cases hs : (lengthResult (LocalAccess.revealResult bits key terminals.toList cache).value.points).value ≤ smallLimit p
  · simp only [Code.evaluate, hs, ite_true]
    rw [Code.evaluate_bind, SmallCoverProgram.program_evaluates w bits]
    simp only [smallResult, hs, ite_true, Code.evaluate, Outcome.add, Outcome.combine,
      Outcome.pure, Nat.add_zero, Nat.zero_add, Nat.add_assoc]
    congr 1
    congr 1
    omega
  · simp only [smallResult, hs, ite_false, Code.evaluate, Outcome.add, Outcome.combine,
      Outcome.pure, Nat.add_zero, Nat.zero_add, Nat.add_assoc]

theorem reveal_set (bits : Q → Bool) (key : Fin n → Q)
    (terminals : Vector (Fin n) (k + 1)) (cache : Cache Q) (hc : Cache.Correct bits cache) :
    (LocalAccess.revealResult bits key terminals.toList cache).value.points.toFinset =
      ComponentExplore.retained bits key terminals.toList.toFinset := by
  rw [(LocalAccess.reveal_correct bits key terminals.toList cache hc).1]
  ext x
  simp [ComponentExplore.retained]

theorem small_guard (bits : Q → Bool) (p : Parameters) (key : Fin n → Q)
    (terminals : Vector (Fin n) (k + 1)) (cache : Cache Q) (hc : Cache.Correct bits cache)
    (hnd : terminals.toList.Nodup) (gplus : ℚ)
    (hcal : ((ComponentExplore.retained bits key terminals.toList.toFinset).card : ℝ) ≤ gplus)
    (hbranch : gplus ≤ 100 * (p.t : ℚ) / p.eps) :
    (LocalAccess.revealResult bits key terminals.toList cache).value.points.length ≤ smallLimit p := by
  have hr := (LocalAccess.reveal_correct bits key terminals.toList cache hc).1
  have hn : (LocalAccess.revealResult bits key terminals.toList cache).value.points.Nodup := by
    rw [hr]
    exact hnd.filter _
  have hcard : (LocalAccess.revealResult bits key terminals.toList cache).value.points.length =
      (ComponentExplore.retained bits key terminals.toList.toFinset).card := by
    rw [← List.toFinset_card_of_nodup hn, reveal_set bits key terminals cache hc]
  have hb : (gplus : ℝ) ≤ ((100 * (p.t : ℚ) / p.eps : ℚ) : ℝ) := by exact_mod_cast hbranch
  have hceil : ((100 * (p.t : ℚ) / p.eps : ℚ) : ℝ) ≤ smallLimit p := by
    have hq : (100 * (p.t : ℚ) / p.eps) ≤ (smallLimit p : ℚ) := Nat.le_ceil _
    exact_mod_cast hq
  rw [hcard]
  exact_mod_cast (hcal.trans hb).trans hceil

theorem small_contract (I : Instance (Fin n)) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ)
    (gminus gplus : ℚ) (cache : Cache Q) (hc : Cache.Correct bits cache)
    (hnd : terminals.toList.Nodup)
    (hcal : ((ComponentExplore.retained bits key terminals.toList.toFinset).card : ℝ) ≤ gplus)
    (hbranch : gplus ≤ 100 * (p.t : ℚ) / p.eps) :
    let N := ComponentExplore.retained bits key terminals.toList.toFinset
    let o := smallResult I.weight bits p terminals key a gminus gplus cache
    Cache.Correct bits o.value.cache ∧
      (∃ Z, o.value.value = some Z ∧ 0 ≤ Z ∧
        Z ≤ Covers.Geometry.savingOn I N a (5 * a / 8) ∧
        Covers.Geometry.savingOn I N a (5 * a / 8) / 2 ≤ Z) ∧
      o.positiveReplies ≤ N.card := by
  dsimp only
  let revealed := LocalAccess.revealResult bits key terminals.toList cache
  have hr := LocalAccess.reveal_correct bits key terminals.toList cache hc
  have hn : revealed.value.points.Nodup := by rw [show revealed.value.points = _ from hr.1]; exact hnd.filter _
  have hs := small_guard bits p key terminals cache hc hnd gplus hcal hbranch
  have hg := SmallCoverProgram.program_guarantee I revealed.value.points hn a
  have hz := (SmallCoverProgram.run_resources I.weight revealed.value.points a).2
  have he := reveal_set bits key terminals cache hc
  have he' : revealed.value.points.toFinset =
      ComponentExplore.retained bits key terminals.toList.toFinset := he
  rw [he'] at hg
  have hl := length_result revealed.value.points
  have hp := LocalAccess.reveal_positive bits key terminals.toList cache
  have hcard : revealed.value.points.length =
      (ComponentExplore.retained bits key terminals.toList.toFinset).card := by
    rw [← List.toFinset_card_of_nodup hn]
    exact congrArg Finset.card he
  have hs' : (lengthResult (LocalAccess.revealResult bits key terminals.toList cache).value.points).value ≤ smallLimit p := by
    rw [(length_result _).1]
    exact hs
  simp only [smallResult, hs', ite_true, Outcome.combine, Outcome.add, Outcome.pure]
  refine ⟨hr.2, ⟨_, rfl, hg.1, ?_, ?_⟩, ?_⟩
  · exact hg.2.1
  · exact hg.2.2
  · dsimp [revealed] at hp hcard
    dsimp [revealed] at hl hz
    simp only [hl.2.2.2.2, hz, Nat.add_zero, Nat.zero_add]
    exact hp.trans hcard.le

end SteinerUpperBound.LargeCoverProgram
