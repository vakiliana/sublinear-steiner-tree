module

public import SteinerUpperBound.Covers.OracleProgramLaw

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {M Q R S : Type*}

theorem runs_map_inv (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (f : R → S) (o : Outcome S) (hr : Runs m b (p.map f) o) :
    ∃ a : Outcome R, Runs m b p a ∧ o = a.map f := by
  induction p generalizing o with
  | pure r =>
    cases hr
    exact ⟨.pure r, Runs.pure r, rfl⟩
  | metric q next ih =>
    cases hr with
    | metric hr =>
      obtain ⟨a, ha, rfl⟩ := ih (m q) _ hr
      exact ⟨a.add 1 1 0 0, Runs.metric ha, rfl⟩
  | retained q next ih =>
    cases hr with
    | retained hr =>
      obtain ⟨a, ha, rfl⟩ := ih (b q) _ hr
      exact ⟨a.add 1 0 1 (if b q then 1 else 0), Runs.retained ha, rfl⟩
  | uniform n next ih =>
    cases hr with
    | uniform a hr =>
      obtain ⟨o, ho, rfl⟩ := ih a _ hr
      exact ⟨o.add 1 0 0 0, Runs.uniform a ho, rfl⟩
  | coin rate next ih =>
    cases hr with
    | coin a hr =>
      obtain ⟨o, ho, rfl⟩ := ih a _ hr
      exact ⟨o.add 2 0 0 0, Runs.coin a ho, rfl⟩
  | tick n next ih =>
    cases hr with
    | tick hr =>
      obtain ⟨a, ha, rfl⟩ := ih _ hr
      exact ⟨a.add (n + 1) 0 0 0, Runs.tick ha, rfl⟩

namespace Sampler

structure Store (Q : Type*) where
  cache : Q → Option Bool
  remaining : ℕ
  proposals : ℕ

namespace Store

def initial (cache : Q → Option Bool) (B : ℕ) : Store Q := ⟨cache, B, 0⟩

def draw (s : Store Q) : Store Q :=
  { s with remaining := s.remaining - 1, proposals := s.proposals + 1 }

def replaceCache (s : Store Q) (cache : Q → Option Bool) : Store Q :=
  { s with cache := cache }

end Store

structure Records (Q : Type*) (k s : ℕ) where
  labels : Option (Fin s → Fin (k + 1))
  times : Fin s → ℕ
  successful : Bool
  store : Store Q

namespace Records

def failure {k : ℕ} (s : ℕ) (u : Store Q) : Records Q k s :=
  ⟨none, fun _ => 0, false, u⟩

def prepend {k s : ℕ} (root : Fin (k + 1)) (label : Option (Fin (k + 1))) (used : ℕ)
    (r : Records Q k s) : Records Q k (s + 1) :=
  ⟨r.labels.map (fun v => Fin.cons (label.getD root) v), Fin.cons used r.times,
    label.isSome && r.successful, r.store⟩

end Records

/-- Frontend caching uses the checked primitive resolver. Every proposal still
consumes its proposal clock even when its retention bit was already cached. -/
noncomputable def member (q : Q) (u : Store Q)
    (next : Bool → Store Q → Code M Q R) : Code M Q R :=
  (Cache.resolve q u.cache).bind
    (fun reply => next reply.1 (u.replaceCache reply.2))

noncomputable def row {k : ℕ} (query : Fin (k + 1) → Q) :
    ℕ → ℕ → Store Q →
      (Option (Fin (k + 1)) → ℕ → Store Q → Code M Q R) →
      (Store Q → Code M Q R) → Code M Q R
  | 0, used, u, next, _ => .tick 1 (next none used u)
  | C + 1, used, u, next, abort =>
      .tick 3 (if u.remaining = 0 then abort u else
        .uniform k (fun y => .tick 3 (member (query y) u.draw (fun v t =>
          if v then next (some y) (used + 1) t
          else row query C (used + 1) t next abort))))

noncomputable def pool {k : ℕ} (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C : ℕ) :
    (s : ℕ) → Store Q → Code M Q (Records Q k s)
  | 0, u => .tick 1 (.pure ⟨some Fin.elim0, Fin.elim0, true, u⟩)
  | s + 1, u => row query C 0 u
      (fun label used t => .tick 3 ((pool query root C s t).map (Records.prepend root label used)))
      (fun t => .pure (Records.failure (s + 1) t))

noncomputable def program {k : ℕ} (query : Fin (k + 1) → Q) (root : Fin (k + 1))
    (C s B : ℕ) (cache : Q → Option Bool) : Code M Q (Records Q k s) :=
  pool query root C s (Store.initial cache B)

theorem member_value (m : M → ℝ) (b : Q → Bool) (q : Q) (u : Store Q)
    (next : Bool → Store Q → Code M Q R) (F : R → ℝ) :
    (member q u next).evaluate m b (fun o => F o.value) =
      (next (Cache.resolved b q u.cache).value.1
        (u.replaceCache (Cache.resolved b q u.cache).value.2)).evaluate m b (fun o => F o.value) := by
  rw [member, Code.evaluate_bind]
  exact Cache.resolve_evaluates m b q u.cache _

theorem member_correct (b : Q → Bool) (q : Q) (u : Store Q) (hc : Cache.Correct b u.cache) :
    (Cache.resolved b q u.cache).value.1 = b q ∧
      Cache.Correct b (u.replaceCache (Cache.resolved b q u.cache).value.2).cache :=
  Cache.resolved_correct b q u.cache hc

end Sampler

end SteinerUpperBound.Covers.OracleProgram
