module

public import SteinerLowerBound.FiniteProbability

@[expose] public section

namespace SteinerLowerBound

inductive DecisionTree (Q A R : Type*)
  | leaf : R → DecisionTree Q A R
  | query : Q → (A → DecisionTree Q A R) → DecisionTree Q A R

namespace DecisionTree

variable {Q A R : Type*}

def output (oracle : Q → A) : DecisionTree Q A R → R
  | .leaf r => r
  | .query q next => (next (oracle q)).output oracle

def transcript (oracle : Q → A) : DecisionTree Q A R → List (Q × A)
  | .leaf _ => []
  | .query q next => (q, oracle q) :: (next (oracle q)).transcript oracle

def queries (oracle : Q → A) (t : DecisionTree Q A R) : ℕ :=
  (t.transcript oracle).length

def truncate : ℕ → DecisionTree Q A R → DecisionTree Q A (Option R)
  | _, .leaf r => .leaf (some r)
  | 0, .query _ _ => .leaf none
  | n + 1, .query q next => .query q (fun a => (next a).truncate n)

theorem truncate_queries (oracle : Q → A) (t : DecisionTree Q A R) (n : ℕ) :
    (t.truncate n).queries oracle ≤ n := by
  induction n generalizing t with
  | zero => cases t <;> simp [truncate, queries, transcript]
  | succ n ih =>
      cases t with
      | leaf r => simp [truncate, queries, transcript]
      | query q next =>
          simpa [truncate, queries, transcript] using ih (next (oracle q))

theorem truncate_output (oracle : Q → A) (t : DecisionTree Q A R) (n : ℕ)
    (h : t.queries oracle ≤ n) :
    (t.truncate n).output oracle = some (t.output oracle) := by
  induction n generalizing t with
  | zero =>
      cases t with
      | leaf r => rfl
      | query q next => simp [queries, transcript] at h
  | succ n ih =>
      cases t with
      | leaf r => rfl
      | query q next =>
          simp only [truncate, output]
          apply ih
          simpa [queries, transcript] using h

theorem truncate_none_iff (oracle : Q → A) (t : DecisionTree Q A R) (n : ℕ) :
    (t.truncate n).output oracle = none ↔ n < t.queries oracle := by
  induction n generalizing t with
  | zero => cases t <;> simp [truncate, output, queries, transcript]
  | succ n ih =>
      cases t with
      | leaf r => simp [truncate, output, queries, transcript]
      | query q next =>
          simpa [truncate, output, queries, transcript] using ih (next (oracle q))

def map {R' : Type*} (f : R → R') : DecisionTree Q A R → DecisionTree Q A R'
  | .leaf r => .leaf (f r)
  | .query q next => .query q (fun a => (next a).map f)

theorem output_map {R' : Type*} (f : R → R') (oracle : Q → A) (t : DecisionTree Q A R) :
    (t.map f).output oracle = f (t.output oracle) := by
  induction t with
  | leaf => rfl
  | query q next ih => exact ih (oracle q)

theorem queries_map {R' : Type*} (f : R → R') (oracle : Q → A) (t : DecisionTree Q A R) :
    (t.map f).queries oracle = t.queries oracle := by
  induction t with
  | leaf => rfl
  | query q next ih => simpa [map, queries, transcript] using ih (oracle q)

def truncateWith (fallback : R) (n : ℕ) (t : DecisionTree Q A R) : DecisionTree Q A R :=
  (t.truncate n).map (fun r => r.getD fallback)

theorem truncateWith_queries (fallback : R) (oracle : Q → A) (t : DecisionTree Q A R) (n : ℕ) :
    (t.truncateWith fallback n).queries oracle ≤ n := by
  simpa only [truncateWith, queries_map] using t.truncate_queries oracle n

theorem truncateWith_output (fallback : R) (oracle : Q → A) (t : DecisionTree Q A R)
    (n : ℕ) (h : t.queries oracle ≤ n) :
    (t.truncateWith fallback n).output oracle = t.output oracle := by
  rw [truncateWith, output_map, truncate_output oracle t n h, Option.getD_some]

end DecisionTree

end SteinerLowerBound
