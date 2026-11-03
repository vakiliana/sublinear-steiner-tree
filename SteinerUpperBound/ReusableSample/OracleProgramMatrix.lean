module

public import SteinerUpperBound.ReusableSample.OracleProgramArithmetic

@[expose] public section

namespace SteinerUpperBound.ReusableSample.OracleProgram

open SteinerLowerBound
open SteinerUpperBound.QueryProgram
open scoped BigOperators Classical

variable {V M Q : Type*}

/-- Every entry is constructed in the continuation of its own metric query.
The query order depends only on the supplied center and sample arrays. -/
noncomputable def readRow (center : V) (r : ℝ) :
    {Ns : ℕ} → (Fin Ns → V) → Code (Sym2 V) Q (Fin Ns → Bool)
  | 0, _ => .tick 0 (.pure Fin.elim0)
  | _ + 1, X => .tick 3 (.metric (Sym2.mk center (X 0)) (fun d =>
      .tick 1 ((readRow center r (fun i => X i.succ)).bind fun tail =>
        .tick 0 (.pure (Fin.cons (decide (d ≤ r)) tail)))))

noncomputable def readMatrix (r : ℝ) {Ns : ℕ} (X : Fin Ns → V) :
    {n : ℕ} → (Fin n → V) → Code (Sym2 V) Q (Fin n → Fin Ns → Bool)
  | 0, _ => .tick 0 (.pure Fin.elim0)
  | _ + 1, centers => .tick 2 ((readRow (centers 0) r X).bind fun row =>
      (readMatrix r X (fun j => centers j.succ)).bind fun tail =>
        .tick 0 (.pure (Fin.cons row tail)))

/-- Specification only; the oracle `m` is not an argument of executable code. -/
noncomputable def observedMatrix {n Ns : ℕ} (m : Sym2 V → ℝ)
    (centers : Fin n → V) (X : Fin Ns → V) (r : ℝ) : Fin n → Fin Ns → Bool :=
  fun j i => decide (m (Sym2.mk (centers j) (X i)) ≤ r)

theorem readRow_good (m : Sym2 V → ℝ) (b : Q → Bool) (center : V) (r : ℝ)
    {Ns : ℕ} (X : Fin Ns → V) :
    Sure m b (readRow center r X)
      (Good (· = fun i => decide (m (Sym2.mk center (X i)) ≤ r)) (8 * Ns + 1) Ns) := by
  induction Ns with
  | zero =>
      apply good_mono m b _ (good_tick m b _ _ 0 0 0 (good_pure m b Fin.elim0))
      · omega
      · intro v hv; subst v; funext j; exact Fin.elim0 j
  | succ Ns ih =>
      let row : Fin Ns → Bool := fun i => decide (m (Sym2.mk center (X i.succ)) ≤ r)
      have he : (Fin.cons (decide (m (Sym2.mk center (X 0)) ≤ r)) row) =
          fun i => decide (m (Sym2.mk center (X i)) ≤ r) := by
        funext i
        refine Fin.cases rfl (fun _ => rfl) i
      have hk : Sure m b
          (.tick 0 (.pure (Fin.cons (decide (m (Sym2.mk center (X 0)) ≤ r)) row)))
          (Good (· = fun i => decide (m (Sym2.mk center (X i)) ≤ r)) 1 0) := by
        rw [he]
        exact good_tick m b _ _ 0 0 0 (good_pure m b _)
      have hs := good_bind_value m b (readRow center r (fun i => X i.succ))
        (fun tail => .tick 0 (.pure (Fin.cons (decide (m (Sym2.mk center (X 0)) ≤ r)) tail)))
        row (· = fun i => decide (m (Sym2.mk center (X i)) ≤ r))
        (8 * Ns + 1) Ns 1 0 (ih _) hk
      let next : ℝ → Code (Sym2 V) Q (Fin (Ns + 1) → Bool) := fun d =>
        .tick 1 ((readRow center r (fun i => X i.succ)).bind fun tail =>
          .tick 0 (.pure (Fin.cons (decide (d ≤ r)) tail)))
      have hm := good_metric m b (Sym2.mk center (X 0)) next
        (· = fun i => decide (m (Sym2.mk center (X i)) ≤ r)) _ _
        (good_tick m b _ _ _ _ 1 hs)
      rw [show 1 + (Ns + 0) = Ns + 1 by omega] at hm
      exact good_mono m b _ (good_tick m b _ _ _ _ 3 hm) (by omega) (fun _ h => h)

theorem readMatrix_good (m : Sym2 V → ℝ) (b : Q → Bool) (r : ℝ)
    {Ns n : ℕ} (X : Fin Ns → V) (centers : Fin n → V) :
    Sure m b (readMatrix r X centers)
      (Good (· = observedMatrix m centers X r) (n * (8 * Ns + 5) + 1) (n * Ns)) := by
  induction n with
  | zero =>
      simp only [readMatrix, Nat.zero_mul, Nat.zero_add]
      apply good_mono m b _ (good_tick m b _ _ 0 0 0 (good_pure m b Fin.elim0))
      · omega
      · intro v hv; subst v; funext j; exact Fin.elim0 j
  | succ n ih =>
      let row : Fin Ns → Bool := fun i => decide (m (Sym2.mk (centers 0) (X i)) ≤ r)
      let tail := observedMatrix m (fun j => centers j.succ) X r
      have he : (Fin.cons row tail) = observedMatrix m centers X r := by
        funext j
        refine Fin.cases rfl (fun _ => rfl) j
      let k : (Fin n → Fin Ns → Bool) → Code (Sym2 V) Q (Fin (n + 1) → Fin Ns → Bool) :=
        fun B => .tick 0 (.pure (Fin.cons row B))
      have hk : Sure m b (k tail) (Good (· = observedMatrix m centers X r) 1 0) := by
        dsimp [k]
        rw [he]
        exact good_tick m b _ _ 0 0 0 (good_pure m b _)
      have hs := good_bind_value m b (readMatrix r X (fun j => centers j.succ))
        k tail (· = observedMatrix m centers X r) (n * (8 * Ns + 5) + 1) (n * Ns) 1 0
        (ih _) hk
      have hr := good_bind_value m b (readRow (centers 0) r X)
        (fun row => (readMatrix r X (fun j => centers j.succ)).bind fun B =>
          .tick 0 (.pure (Fin.cons row B)))
        row (· = observedMatrix m centers X r) (8 * Ns + 1) Ns
        (n * (8 * Ns + 5) + 1 + 1) (n * Ns + 0) (readRow_good m b _ _ _) hs
      have hh := good_tick m b _ _ _ _ 2 hr
      rw [show Ns + (n * Ns + 0) = (n + 1) * Ns by ring] at hh
      apply good_mono m b _ hh
      · nlinarith
      · exact fun _ h => h

noncomputable def flagSet {Ns : ℕ} (live : Fin Ns → Bool) : Finset (Fin Ns) :=
  Finset.univ.filter fun i => live i = true

theorem count_eq_card {Ns : ℕ} (live row : Fin Ns → Bool) :
    count live row = (matrixHits (flagSet live) row).card := by
  rw [matrixHits, flagSet, Finset.filter_filter, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Bool.and_eq_true]

theorem count_le {Ns : ℕ} (live row : Fin Ns → Bool) : count live row ≤ Ns := by
  rw [count_eq_card]
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

theorem flagSet_deleted {Ns : ℕ} (live row : Fin Ns → Bool) :
    flagSet (deleted live row) = flagSet live \ matrixHits (flagSet live) row := by
  ext i
  cases hl : live i <;> cases hr : row i <;> simp [flagSet, deleted, matrixHits, hl, hr]

theorem flagSet_true (Ns : ℕ) : flagSet (fun _ : Fin Ns => true) = Finset.univ := by
  ext i
  simp [flagSet]

def perRow (Ns : ℕ) : ℕ := 16 * Ns + 8 * Nat.log2 (Ns + 1) + 64

/-- All record scans, scalar arithmetic, probability evaluation, bitmap choices,
and output construction are charged where performed. The original threshold
parameter `t` is fixed even as the remaining quota decreases. -/
noncomputable def loop (Lbar Ns t : ℕ) :
    {n : ℕ} → (Fin n → Fin Ns → Bool) → ℕ → (Fin Ns → Bool) →
      Code M Q (Fin n → Bool)
  | 0, _, _, _ => .tick 0 (.pure Fin.elim0)
  | n + 1, B, quota, live => .tick 1
      (if quota = 0 then fill (n + 1) false
      else (scan live (B 0)).bind fun v =>
        (probability Lbar Ns t v.1).bind fun p =>
          .tick 7 (.coin (coinRate p) (fun a =>
            .tick 7 ((loop Lbar Ns t (fun j => B j.succ)
              (if a then quota - 1 else quota) (if a then v.2 else live)).bind fun tail =>
                .tick 0 (.pure (Tree.prepend a tail))))))

theorem loop_good (m : M → ℝ) (b : Q → Bool) (Lbar Ns t : ℕ)
    {n : ℕ} (B : Fin n → Fin Ns → Bool) (quota : ℕ) (live : Fin Ns → Bool) :
    Sure m b (loop Lbar Ns t B quota live)
      (Good (fun T => acceptances T ≤ quota) (n * perRow Ns + 3) 0) := by
  induction n generalizing quota live with
  | zero =>
      apply good_mono m b _ (good_tick m b _ _ 0 0 0 (good_pure m b Fin.elim0))
      · omega
      · intro T hT; subst T; simp [acceptances]
  | succ n ih =>
      by_cases hq : quota = 0
      · rw [loop, ite_eq_left hq]
        apply good_mono m b _ (good_tick m b _ _ _ _ 1 (fill_good m b (n + 1) false))
        · dsimp [perRow]
          nlinarith
        · intro T hT; subst T; simp [acceptances]
      · let c := count live (B 0)
        let D := deleted live (B 0)
        let choose : ℚ → Code M Q (Fin (n + 1) → Bool) := fun p =>
          .tick 7 (.coin (coinRate p) (fun a =>
            .tick 7 ((loop Lbar Ns t (fun j => B j.succ)
              (if a then quota - 1 else quota) (if a then D else live)).bind fun tail =>
                .tick 0 (.pure (Tree.prepend a tail)))))
        have hchoose (p : ℚ) : Sure m b (choose p)
            (Good (fun T => acceptances T ≤ quota) (n * perRow Ns + 22) 0) := by
          apply good_mono m b _ (good_tick m b _ _ _ _ 7 (good_coin m b (coinRate p) _
            (fun T => acceptances T ≤ quota) (n * perRow Ns + 12) 0 (fun a => ?_)))
          · omega
          · exact fun _ h => h
          have hk (tail : Fin n → Bool)
              (htail : acceptances tail ≤ if a then quota - 1 else quota) :
              Sure m b (.tick 0 (.pure (Tree.prepend a tail)))
                (Good (fun T => acceptances T ≤ quota) 1 0) := by
            apply good_mono m b _ (good_tick m b _ _ 0 0 0 (good_pure m b _))
            · omega
            · intro T hT
              subst T
              rw [acceptances_succ]
              simp only [Tree.prepend, Fin.cons_zero, Fin.cons_succ]
              change (if a then 1 else 0) + acceptances tail ≤ quota
              cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] at htail ⊢ <;> omega
          have hh := good_bind m b
            (loop Lbar Ns t (fun j => B j.succ)
              (if a then quota - 1 else quota) (if a then D else live))
            (fun tail => .tick 0 (.pure (Tree.prepend a tail)))
            (fun tail => acceptances tail ≤ if a then quota - 1 else quota)
            (fun T => acceptances T ≤ quota) (n * perRow Ns + 3) 0 1 0
            (ih _ _ _) hk
          exact good_mono m b _ (good_tick m b _ _ _ _ 7 hh) (by omega) (fun _ h => h)
        let after : (ℕ × (Fin Ns → Bool)) → Code M Q (Fin (n + 1) → Bool) := fun v =>
          (probability Lbar Ns t v.1).bind fun p =>
            .tick 7 (.coin (coinRate p) (fun a =>
              .tick 7 ((loop Lbar Ns t (fun j => B j.succ)
                (if a then quota - 1 else quota) (if a then v.2 else live)).bind fun tail =>
                  .tick 0 (.pure (Tree.prepend a tail)))))
        have ha : Sure m b (after (c, D))
            (Good (fun T => acceptances T ≤ quota)
              (8 * Nat.log2 (Ns + 1) + 34 + (n * perRow Ns + 22)) 0) :=
          good_bind_value m b (probability Lbar Ns t c) choose
            (fastProbability Lbar Ns t c) _ (8 * Nat.log2 (Ns + 1) + 34) 0
            (n * perRow Ns + 22) 0
            (probability_good m b Lbar Ns t c (count_le live (B 0))) (hchoose _)
        have hs := good_bind_value m b (scan live (B 0)) after (c, D)
          (fun T => acceptances T ≤ quota) (16 * Ns + 1) 0
          (8 * Nat.log2 (Ns + 1) + 34 + (n * perRow Ns + 22)) 0
          (scan_good m b live (B 0)) ha
        rw [loop, ite_eq_right hq]
        exact good_mono m b _ (good_tick m b _ _ _ _ 1 hs)
          (by dsimp [perRow]; nlinarith) (fun _ h => h)

end SteinerUpperBound.ReusableSample.OracleProgram
