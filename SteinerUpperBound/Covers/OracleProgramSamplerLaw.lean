module

public import SteinerUpperBound.Covers.OracleProgramSamplerResources

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram.Sampler

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators
open FiniteSampling

variable {M Q R : Type*} {k : ℕ}

structure Observation (k s : ℕ) where
  labels : Option (Fin s → Fin (k + 1))
  times : Fin s → ℕ
  successful : Bool
  proposals : ℕ
  remaining : ℕ

namespace Observation

def ofRecords {s : ℕ} (r : Records Q k s) : Observation k s :=
  ⟨r.labels, r.times, r.successful, r.store.proposals, r.store.remaining⟩

def failure (s B P : ℕ) : Observation k s := ⟨none, fun _ => 0, false, P, B⟩

def prepend {s : ℕ} (root : Fin (k + 1)) (label : Option (Fin (k + 1))) (used : ℕ)
    (r : Observation k s) : Observation k (s + 1) :=
  ⟨r.labels.map (fun v => Fin.cons (label.getD root) v), Fin.cons used r.times,
    label.isSome && r.successful, r.proposals, r.remaining⟩

end Observation

def replayRow {A : Type*} (b : Fin (k + 1) → Bool) :
    (C : ℕ) → ℕ → ℕ → ℕ → (Fin C → Fin (k + 1)) →
      (Option (Fin (k + 1)) → ℕ → ℕ → ℕ → A) → (ℕ → ℕ → A) → A
  | 0, used, B, P, _, next, _ => next none used B P
  | _ + 1, _, 0, P, _, _, abort => abort 0 P
  | C + 1, used, B + 1, P, w, next, abort =>
      if b (w 0) then next (some (w 0)) (used + 1) B (P + 1)
      else replayRow b C (used + 1) B (P + 1) (Fin.tail w) next abort

def replayPool (b : Fin (k + 1) → Bool) (root : Fin (k + 1)) (C : ℕ) :
    (s : ℕ) → ℕ → ℕ → (Fin s → Fin C → Fin (k + 1)) → Observation k s
  | 0, B, P, _ => ⟨some Fin.elim0, Fin.elim0, true, P, B⟩
  | s + 1, B, P, rows => replayRow b C 0 B P (rows 0)
      (fun label used B' P' => Observation.prepend root label used
        (replayPool b root C s B' P' (Fin.tail rows)))
      (Observation.failure (k := k) (s + 1))

theorem replayRow_expect {A : Type*} [Fintype A] (μ : Law A)
    (b : Fin (k + 1) → Bool) (C used B P : ℕ) (w : Fin C → Fin (k + 1))
    (next : A → Option (Fin (k + 1)) → ℕ → ℕ → ℕ → ℝ)
    (abort : A → ℕ → ℕ → ℝ) :
    μ.expect (fun a => replayRow b C used B P w (next a) (abort a)) =
      replayRow b C used B P w
        (fun label used B P => μ.expect (fun a => next a label used B P))
        (fun B P => μ.expect (fun a => abort a B P)) := by
  induction C generalizing used B P with
  | zero => rfl
  | succ C ih =>
    cases B with
    | zero => rfl
    | succ B =>
      cases hb : b (w 0) with
      | true => simp only [replayRow, hb, ite_true]
      | false => simpa only [replayRow, hb, Bool.false_eq_true, ite_false] using
          (ih (used + 1) B (P + 1) (Fin.tail w))

theorem replayRow_map {A T : Type*} (f : A → T) (b : Fin (k + 1) → Bool)
    (C used B P : ℕ) (w : Fin C → Fin (k + 1))
    (next : Option (Fin (k + 1)) → ℕ → ℕ → ℕ → A) (abort : ℕ → ℕ → A) :
    f (replayRow b C used B P w next abort) =
      replayRow b C used B P w
        (fun label used B P => f (next label used B P)) (fun B P => f (abort B P)) := by
  induction C generalizing used B P with
  | zero => rfl
  | succ C ih =>
    cases B with
    | zero => rfl
    | succ B =>
      cases hb : b (w 0) with
      | true => simp only [replayRow, hb, ite_true]
      | false => simpa only [replayRow, hb, Bool.false_eq_true, ite_false] using
          (ih (used + 1) B (P + 1) (Fin.tail w))

theorem row_evaluate (m : M → ℝ) (b : Q → Bool) (query : Fin (k + 1) → Q)
    (C used : ℕ) (u : Store Q) (hc : Cache.Correct b u.cache)
    (next : Option (Fin (k + 1)) → ℕ → Store Q → Code M Q R)
    (abort : Store Q → Code M Q R) (F : R → ℝ)
    (K : Option (Fin (k + 1)) → ℕ → ℕ → ℕ → ℝ) (A : ℕ → ℕ → ℝ)
    (hn : ∀ label used t, Cache.Correct b t.cache →
      (next label used t).evaluate m b (fun o => F o.value) =
        K label used t.remaining t.proposals)
    (ha : ∀ t, Cache.Correct b t.cache →
      (abort t).evaluate m b (fun o => F o.value) = A t.remaining t.proposals) :
    (row query C used u next abort).evaluate m b (fun o => F o.value) =
      (tape (Law.uniform (Fin (k + 1))) C).expect (fun w =>
        replayRow (fun y => b (query y)) C used u.remaining u.proposals w K A) := by
  induction C generalizing used u with
  | zero =>
    simp only [row, Code.evaluate, Outcome.add, replayRow]
    rw [hn none used u hc, Law.expect_const]
  | succ C ih =>
    cases hB : u.remaining with
    | zero =>
      simp only [row, hB, ite_true, Code.evaluate, Outcome.add, replayRow]
      rw [ha u hc, Law.expect_const]
      simp only [hB]
    | succ B =>
      have hu : u.remaining ≠ 0 := by rw [hB]; omega
      simp only [row, hu, ite_false, Code.evaluate, Outcome.add]
      rw [expect_tape_succ]
      apply congrArg (Law.uniform (Fin (k + 1))).expect
      funext y
      rw [member_value]
      have hcDraw : Cache.Correct b u.draw.cache := hc
      have hres := member_correct b (query y) u.draw hcDraw
      let t := u.draw.replaceCache (Cache.resolved b (query y) u.draw.cache).value.2
      have htB : t.remaining = B := by dsimp [t, Store.replaceCache, Store.draw]; rw [hB]; omega
      have htP : t.proposals = u.proposals + 1 := rfl
      rw [hres.1]
      cases hy : b (query y) with
      | true =>
        simp only [hy, ite_true]
        rw [hn (some y) (used + 1) t hres.2]
        simp only [replayRow, hB, Fin.cons_zero, hy, ite_true, Law.expect_const, htB, htP]
      | false =>
        simp only [hy, Bool.false_eq_true, ite_false]
        rw [ih (used + 1) t hres.2]
        apply congrArg (tape (Law.uniform (Fin (k + 1))) C).expect
        funext w
        simp only [replayRow, hB, Fin.cons_zero, Fin.tail_cons, hy, Bool.false_eq_true,
          ite_false, htB, htP]

/-- Exact law of every observation, including the actual proposal counter and
the recorded row stopping times. All long row tapes are analysis-only. -/
theorem pool_evaluate_replay (m : M → ℝ) (b : Q → Bool) (query : Fin (k + 1) → Q)
    (root : Fin (k + 1)) (C s : ℕ) (u : Store Q) (hc : Cache.Correct b u.cache)
    (F : Observation k s → ℝ) :
    (pool query root C s u).evaluate m b (fun o => F (Observation.ofRecords o.value)) =
      (Rejection.poolLaw C s).expect
        (fun rows => F (replayPool (fun y => b (query y)) root C s u.remaining u.proposals rows)) := by
  induction s generalizing u with
  | zero =>
    simp only [pool, Code.evaluate, Outcome.add, Outcome.pure, Observation.ofRecords,
      replayPool, Law.expect_const]
  | succ s ih =>
    rw [pool]
    rw [row_evaluate m b query C 0 u hc _ _ (fun r => F (Observation.ofRecords r))
      (fun label used B P => (Rejection.poolLaw C s).expect (fun rows =>
        F (Observation.prepend root label used (replayPool (fun y => b (query y)) root C s B P rows))))
      (fun B P => F (Observation.failure (k := k) (s + 1) B P))]
    · simp only [Rejection.poolLaw]
      rw [expect_tape_succ]
      apply congrArg (tape (Law.uniform (Fin (k + 1))) C).expect
      funext w
      simp only [replayPool, Fin.cons_zero, Fin.tail_cons]
      simp_rw [replayRow_map]
      rw [replayRow_expect]
      simp only [Law.expect_const]
    · intro label used t ht
      simp only [Code.evaluate, Outcome.add, Code.evaluate_map, Outcome.map]
      exact ih t ht (fun obs => F (Observation.prepend root label used obs))
    · intro t _
      rfl

theorem replayRow_complete {A : Type*} (b : Fin (k + 1) → Bool)
    (C used B P : ℕ) (w : Fin C → Fin (k + 1))
    (next : Option (Fin (k + 1)) → ℕ → ℕ → ℕ → A) (abort : ℕ → ℕ → A)
    (h : Rejection.waiting b C w ≤ B) :
    replayRow b C used B P w next abort =
      next (Rejection.first b C w) (used + Rejection.waiting b C w)
        (B - Rejection.waiting b C w) (P + Rejection.waiting b C w) := by
  induction C generalizing used B P with
  | zero => simp [replayRow, Rejection.first, Rejection.waiting]
  | succ C ih =>
    cases B with
    | zero =>
      cases hb : b (w 0) <;> simp [Rejection.waiting, hb] at h
    | succ B =>
      cases hb : b (w 0) with
      | true => simp [replayRow, Rejection.first, Rejection.waiting, hb]
      | false =>
        have ht : Rejection.waiting b C (Fin.tail w) ≤ B := by
          simp only [Rejection.waiting, hb, Bool.false_eq_true, ite_false] at h
          omega
        rw [replayRow, if_neg (by simp [hb]), ih (used + 1) B (P + 1) (Fin.tail w) ht]
        simp only [Rejection.first, Rejection.waiting, hb, Bool.false_eq_true, ite_false]
        congr 1 <;> omega

theorem replayRow_abort {A : Type*} (b : Fin (k + 1) → Bool)
    (C used B P : ℕ) (w : Fin C → Fin (k + 1))
    (next : Option (Fin (k + 1)) → ℕ → ℕ → ℕ → A) (abort : ℕ → ℕ → A)
    (h : B < Rejection.waiting b C w) :
    replayRow b C used B P w next abort = abort 0 (P + B) := by
  induction C generalizing used B P with
  | zero => simp [Rejection.waiting] at h
  | succ C ih =>
    cases B with
    | zero => simp [replayRow]
    | succ B =>
      cases hb : b (w 0) with
      | true => simp [Rejection.waiting, hb] at h
      | false =>
        have ht : B < Rejection.waiting b C (Fin.tail w) := by
          simp only [Rejection.waiting, hb, Bool.false_eq_true, ite_false] at h
          omega
        rw [replayRow, if_neg (by simp [hb]), ih (used + 1) B (P + 1) (Fin.tail w) ht]
        congr 1
        omega

end SteinerUpperBound.Covers.OracleProgram.Sampler
