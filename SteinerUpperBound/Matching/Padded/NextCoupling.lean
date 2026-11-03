module

public import SteinerUpperBound.Matching.Padded.Prefix
public import SteinerUpperBound.Matching.Padded.Oracle

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Cache

open SteinerLowerBound
open scoped Classical

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ)

noncomputable def idealExtend (height : ℕ) (v : V) (s : Cache S Q)
    (ranks : E → Fin Q) : Cache S Q :=
  if Buckets.bound (s.level v + 1) ≤ Q then Posterior.ideal S Q height s v ranks else s

theorem idealExtend_joint [Fintype E] (hQ : 0 < Q) (height : ℕ) (v : V) (s : Cache S Q)
    (f : Cache S Q → (E → Fin Q) → ℝ) :
    (completion S Q hQ s).expect (fun ranks => f (idealExtend S Q height v s ranks) ranks) =
      (extend S Q hQ height v s).expect (fun t => (completion S Q hQ t).expect (f t)) := by
  by_cases hb : Buckets.bound (s.level v + 1) ≤ Q
  · simpa only [idealExtend, hb, ↓reduceIte] using
      Posterior.extension_joint S Q hQ height s v hb f
  · simp only [idealExtend, extend, hb, ↓reduceIte, Program.expect_ret]

noncomputable def idealNextLoop (S : Slots G) (Q height : ℕ) (v : V) (cursor : ℕ) :
    ℕ → Cache S Q → (E → Fin Q) → Option (Entry S Q) × Cache S Q
  | 0, s, _ => (none, s)
  | fuel + 1, s, ranks =>
    match available S Q v cursor s with
    | some x => (some x, s)
    | none =>
      if boundary S Q s v < Q then
        idealNextLoop S Q height v cursor fuel (idealExtend S Q height v s ranks) ranks
      else (none, s)

theorem nextLoop_joint [Fintype E] (hQ : 0 < Q) (height : ℕ) (v : V) (cursor fuel : ℕ)
    (s : Cache S Q) (f : (Option (Entry S Q) × Cache S Q) → (E → Fin Q) → ℝ) :
    (completion S Q hQ s).expect
      (fun ranks => f (idealNextLoop S Q height v cursor fuel s ranks) ranks) =
      (nextLoop S Q hQ height v cursor fuel s).expect
        (fun answer => (completion S Q hQ answer.2).expect (f answer)) := by
  induction fuel generalizing s with
  | zero => simp only [nextLoop, idealNextLoop, Program.expect_ret]
  | succ fuel ih =>
    simp only [nextLoop, idealNextLoop, Program.expect_tick]
    cases ha : available S Q v cursor s with
    | some x => simp only [ha, Program.expect_ret]
    | none =>
      simp only [ha]
      by_cases hb : boundary S Q s v < Q
      · simp only [hb, ↓reduceIte, Program.expect_bind]
        simp_rw [← ih]
        exact idealExtend_joint S Q hQ height v s
          (fun t ranks => f (idealNextLoop S Q height v cursor fuel t ranks) ranks)
      · simp only [hb, ↓reduceIte, Program.expect_ret]

noncomputable def idealNext (height maxLevel : ℕ) (v : V) (cursor : ℕ) (s : Cache S Q)
    (ranks : E → Fin Q) : Option (Entry S Q) × Cache S Q :=
  let t := { s with requests := Function.update s.requests v (s.requests v + 1) }
  if s.prepared v then idealNextLoop S Q height v cursor (maxLevel + 1) t ranks
  else idealNextLoop S Q height v cursor (maxLevel + 1)
    { t with prepared := Function.update t.prepared v true } ranks

theorem next_joint [Fintype E] (hQ : 0 < Q) (height maxLevel : ℕ) (v : V) (cursor : ℕ)
    (s : Cache S Q) (f : (Option (Entry S Q) × Cache S Q) → (E → Fin Q) → ℝ) :
    (completion S Q hQ s).expect
      (fun ranks => f (idealNext S Q height maxLevel v cursor s ranks) ranks) =
      (next S Q hQ height maxLevel v cursor s).expect
        (fun answer => (completion S Q hQ answer.2).expect (f answer)) := by
  unfold next idealNext
  cases hp : s.prepared v with
  | true =>
    simp only [hp, ↓reduceIte]
    exact nextLoop_joint S Q hQ height v cursor (maxLevel + 1)
      { s with requests := Function.update s.requests v (s.requests v + 1) } f
  | false =>
    simp only [hp, Bool.false_eq_true, ↓reduceIte, Program.expect_tick]
    exact nextLoop_joint S Q hQ height v cursor (maxLevel + 1)
      { s with requests := Function.update s.requests v (s.requests v + 1),
               prepared := Function.update s.prepared v true } f

end SteinerUpperBound.Matching.Padded.Cache
