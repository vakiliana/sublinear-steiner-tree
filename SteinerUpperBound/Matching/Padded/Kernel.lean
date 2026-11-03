module

public import SteinerUpperBound.Matching.Padded.PlanTree

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Kernel

open SteinerLowerBound
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ) (hQ : 0 < Q)

noncomputable def prior (s : Cache S Q) (e : E) : Law (Fin Q) :=
  match s.assigned e with
  | some r => Law.pure r
  | none => Range.law Q hQ (Cache.lower S Q s e) Q

noncomputable def observationLaw (s : Cache S Q) (v : V) (e : E) : Law (Option (Fin Q)) :=
  if e ∈ Plan.keys S Q s v then
    Observation.law Q hQ (Cache.boundary S Q s v) (Buckets.bound (s.level v + 1))
  else Law.pure none

noncomputable def observe (s : Cache S Q) (v : V) (e : E) (r : Fin Q) : Option (Fin Q) :=
  if e ∈ Plan.keys S Q s v ∧ r.val < Buckets.bound (s.level v + 1) then some r else none

noncomputable def posterior (s : Cache S Q) (v : V) (obs : E → Option (Fin Q)) (e : E) :
    Law (Fin Q) :=
  if e ∈ Plan.keys S Q s v then Observation.posterior Q hQ (Buckets.bound (s.level v + 1)) (obs e)
  else prior S Q hQ s e

theorem coordinate_joint (s : Cache S Q) (v : V)
    (hb : Buckets.bound (s.level v + 1) ≤ Q) (e : E) :
    (prior S Q hQ s e).map (fun r => (observe S Q s v e r, r)) =
      (observationLaw S Q hQ s v e).bind
        (fun tag => (posterior S Q hQ s v (fun _ => tag) e).map (fun r => (tag, r))) := by
  classical
  by_cases he : e ∈ Plan.keys S Q s v
  · have hp := Plan.key_properties S Q s v e he
    have ha : Cache.boundary S Q s v < Buckets.bound (s.level v + 1) :=
      Buckets.bound_strictMono (show s.level v < s.level v + 1 by omega)
    simpa only [prior, hp.1, hp.2.2, observe, observationLaw, posterior, he, true_and,
      ↓reduceIte] using Observation.joint_law Q hQ (Cache.boundary S Q s v)
        (Buckets.bound (s.level v + 1)) ha hb
  · apply FiniteLaw.eq_of_expect
    intro f
    simp only [observe, observationLaw, posterior, he, false_and, ↓reduceIte,
      Law.expect_map, Law.expect_bind, Law.expect_pure]

theorem joint [Fintype E] (s : Cache S Q) (v : V)
    (hb : Buckets.bound (s.level v + 1) ≤ Q) :
    (Cache.completion S Q hQ s).map
      (fun ranks => ((fun e => observe S Q s v e (ranks e)), ranks)) =
      (Law.pi (observationLaw S Q hQ s v)).bind
        (fun obs => (Law.pi (posterior S Q hQ s v obs)).map (fun ranks => (obs, ranks))) :=
  FiniteLaw.pi_joint (prior S Q hQ s) (observe S Q s v) (observationLaw S Q hQ s v)
    (fun e tag => posterior S Q hQ s v (fun _ => tag) e)
    (coordinate_joint S Q hQ s v hb)

theorem commit_levels (s : Cache S Q) (xs : List (Entry S Q)) :
    (Cache.commit S Q s xs).level = s.level := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    change (Cache.commit S Q (Cache.assign S Q s x.source x.reverse x.edge x.rank) xs).level = _
    rw [ih, Cache.assign_levels]

noncomputable def final (sortHeight : ℕ) (s : Cache S Q) (v : V)
    (obs : E → Option (Fin Q)) : Cache S Q :=
  (Cache.finish S Q sortHeight v s
    (Plan.observations (Plan.items S Q s v) obs).reverse).value

theorem final_assigned (sortHeight : ℕ) (s : Cache S Q) (v : V)
    (obs : E → Option (Fin Q)) (e : E) :
    (final S Q sortHeight s v obs).assigned e =
      if e ∈ Plan.keys S Q s v then obs e else s.assigned e := by
  classical
  change (Cache.commit S Q s
    (Plan.observations (Plan.items S Q s v) obs).reverse).assigned e = _
  rw [Plan.commit_assigned]
  by_cases he : e ∈ Plan.keys S Q s v
  · have hn := (Plan.key_properties S Q s v e he).1
    have hm : e ∈ (Plan.items S Q s v).map Plan.Item.edge := List.mem_toFinset.mp he
    simp only [he, ↓reduceIte]
    cases ho : obs e with
    | none => rw [Plan.assignedMap_none _ _ _ e ho, hn]
    | some r => exact Plan.assignedMap_some _ _ _ e r ho hm
  · have hm : e ∉ (Plan.items S Q s v).map Plan.Item.edge := by simpa [Plan.keys] using he
    simp only [he, ↓reduceIte]
    exact Plan.assignedMap_absent _ _ _ e hm

theorem final_boundary (sortHeight : ℕ) (s : Cache S Q) (v u : V)
    (obs : E → Option (Fin Q)) :
    Cache.boundary S Q (final S Q sortHeight s v obs) u =
      if u = v then Buckets.bound (s.level v + 1) else Cache.boundary S Q s u := by
  classical
  unfold Cache.boundary final Cache.finish
  simp only [commit_levels, Function.update_apply]
  split_ifs <;> rfl

theorem final_lower (sortHeight : ℕ) (s : Cache S Q) (v : V)
    (obs : E → Option (Fin Q)) (e : E) :
    Cache.lower S Q (final S Q sortHeight s v obs) e =
      if G.Incident e v then max (Cache.lower S Q s e) (Buckets.bound (s.level v + 1))
      else Cache.lower S Q s e := by
  classical
  have hab := Buckets.bound_mono (Nat.le_succ (s.level v))
  change Cache.boundary S Q s v ≤ Buckets.bound (s.level v + 1) at hab
  unfold Cache.lower
  rw [final_boundary, final_boundary]
  by_cases hl : G.left e = v
  · have hr : G.right e ≠ v := fun h => G.loopless e (hl.trans h.symm)
    simp only [Graph.Incident, hl, hr, true_or, ↓reduceIte]
    omega
  · by_cases hr : G.right e = v
    · simp only [Graph.Incident, hl, hr, false_or, ↓reduceIte]
      omega
    · simp only [Graph.Incident, hl, hr, or_self, ↓reduceIte]

theorem lower_high_of_absent (s : Cache S Q) (v : V) (e : E)
    (hn : s.assigned e = none) (hi : G.Incident e v) (he : e ∉ Plan.keys S Q s v) :
    Buckets.bound (s.level v + 1) ≤ Cache.lower S Q s e := by
  have hla := Cache.lower_at_endpoint S Q s e v hi
  have hne : Cache.lower S Q s e ≠ Cache.boundary S Q s v :=
    fun h => he (Plan.key_of_incident S Q s v e hn hi h)
  rcases Buckets.adjacent (s.level v) (s.level (G.left e)) with hl | hl
  · rcases Buckets.adjacent (s.level v) (s.level (G.right e)) with hr | hr
    · change Cache.boundary S Q s (G.left e) ≤ Cache.boundary S Q s v at hl
      change Cache.boundary S Q s (G.right e) ≤ Cache.boundary S Q s v at hr
      have hmax : Cache.lower S Q s e ≤ Cache.boundary S Q s v := max_le hl hr
      exact (hne (Nat.le_antisymm hmax hla)).elim
    · exact hr.trans (Nat.le_max_right _ _)
  · exact hl.trans (Nat.le_max_left _ _)

theorem final_completion [Fintype E] (sortHeight : ℕ) (s : Cache S Q) (v : V)
    (obs : E → Option (Fin Q)) :
    Cache.completion S Q hQ (final S Q sortHeight s v obs) =
      Law.pi (posterior S Q hQ s v obs) := by
  classical
  unfold Cache.completion
  congr 1
  funext e
  rw [final_assigned]
  by_cases he : e ∈ Plan.keys S Q s v
  · simp only [he, ↓reduceIte, posterior]
    cases ho : obs e with
    | some r => rfl
    | none =>
      have hp := Plan.key_properties S Q s v e he
      have hab : Cache.boundary S Q s v ≤ Buckets.bound (s.level v + 1) :=
        Buckets.bound_mono (show s.level v ≤ s.level v + 1 by omega)
      rw [final_lower]
      simp only [hp.2.1, hp.2.2, ↓reduceIte]
      rw [max_eq_right hab]
      rfl
  · simp only [he, ↓reduceIte, posterior]
    cases ha : s.assigned e with
    | some r => simp only [prior, ha]
    | none =>
      by_cases hi : G.Incident e v
      · rw [final_lower]
        simp only [hi, ↓reduceIte]
        rw [max_eq_left (lower_high_of_absent S Q s v e ha hi he)]
        simp only [prior, ha]
      · rw [final_lower]
        simp only [hi, ↓reduceIte]
        simp only [prior, ha]

end SteinerUpperBound.Matching.Padded.Kernel
