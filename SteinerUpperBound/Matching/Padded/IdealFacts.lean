module

public import SteinerUpperBound.Matching.Padded.Posterior
public import SteinerUpperBound.Matching.Padded.Records

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ)

namespace Cache

theorem consistent_unknown_lower (s : Cache S Q) (ranks : E → Fin Q)
    (hs : Consistent S Q s ranks) (e : E) (hn : s.assigned e = none) :
    lower S Q s e ≤ (ranks e).val := by
  apply max_le
  · by_contra h
    have hr : (ranks e).val < boundary S Q s (G.left e) := by omega
    have he := hs.2 e (G.left e) (G.incident_left e) hr
    rw [hn] at he
    cases he
  · by_contra h
    have hr : (ranks e).val < boundary S Q s (G.right e) := by omega
    have he := hs.2 e (G.right e) (G.incident_right e) hr
    rw [hn] at he
    cases he

end Cache

namespace Posterior

theorem ideal_preserves_assigned (sortHeight : ℕ) (s : Cache S Q) (v : V)
    (ranks : E → Fin Q) (e : E) (r : Fin Q) (hr : s.assigned e = some r) :
    (ideal S Q sortHeight s v ranks).assigned e = some r := by
  have he : e ∉ Plan.keys S Q s v := by
    intro he
    have hn := (Plan.key_properties S Q s v e he).1
    rw [hr] at hn
    cases hn
  rw [ideal, Kernel.final_assigned]
  simpa only [he, ↓reduceIte] using hr

theorem ideal_consistent (sortHeight : ℕ) (s : Cache S Q) (v : V)
    (ranks : E → Fin Q) (hs : Cache.Consistent S Q s ranks) :
    Cache.Consistent S Q (ideal S Q sortHeight s v ranks) ranks := by
  classical
  let obs : E → Option (Fin Q) := fun e => Kernel.observe S Q s v e (ranks e)
  have ha (e : E) :
      (ideal S Q sortHeight s v ranks).assigned e =
        if e ∈ Plan.keys S Q s v then obs e else s.assigned e :=
    Kernel.final_assigned S Q sortHeight s v obs e
  refine ⟨?_, ?_⟩
  · intro e r hr
    rw [ha e] at hr
    by_cases he : e ∈ Plan.keys S Q s v
    · simp only [he, ↓reduceIte] at hr
      dsimp only [obs, Kernel.observe] at hr
      split_ifs at hr
      · exact Option.some.inj hr
    · exact hs.1 e r (by simpa only [he, ↓reduceIte] using hr)
  · intro e u hi hlow
    by_cases huv : u = v
    · subst u
      have hlow' : (ranks e).val < Buckets.bound (s.level v + 1) := by
        simpa only [ideal, Kernel.final_boundary, ↓reduceIte] using hlow
      cases he : s.assigned e with
      | some r =>
        have hknown := hs.1 e r he
        simpa only [hknown] using ideal_preserves_assigned S Q sortHeight s v ranks e r he
      | none =>
        by_cases hk : e ∈ Plan.keys S Q s v
        · rw [ha e]
          simp only [hk, ↓reduceIte, obs, Kernel.observe, hlow', and_self]
        · have hb := Kernel.lower_high_of_absent S Q s v e he hi hk
          have hr := Cache.consistent_unknown_lower S Q s ranks hs e he
          omega
    · have hlow' : (ranks e).val < Cache.boundary S Q s u := by
        simpa only [ideal, Kernel.final_boundary, huv, ↓reduceIte] using hlow
      exact ideal_preserves_assigned S Q sortHeight s v ranks e (ranks e) (hs.2 e u hi hlow')

theorem ideal_legal (sortHeight : ℕ) (s : Cache S Q) (v : V) (ranks : E → Fin Q)
    (hs : Cache.Legal S Q s) (hc : Cache.Consistent S Q s ranks)
    (hb : Buckets.bound (s.level v + 1) ≤ Q) :
    Cache.Legal S Q (ideal S Q sortHeight s v ranks) := by
  have hnew := ideal_consistent S Q sortHeight s v ranks hc
  constructor
  · intro u
    rw [ideal, Kernel.final_boundary]
    split_ifs
    · exact hb
    · exact hs.1 u
  · intro e he
    exact (Cache.consistent_unknown_lower S Q _ ranks hnew e he).trans_lt (ranks e).isLt

end Posterior

end SteinerUpperBound.Matching.Padded
