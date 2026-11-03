module

public import SteinerUpperBound.Matching.Padded.PlanSampling

@[expose] public section

/-!
# Exact posterior law of an implemented bucket extension

`ideal` is used only in the coupling proof. The actual program on the right of
`extension_joint` is `Cache.extend`, whose tests are generated sparsely.
-/

namespace SteinerUpperBound.Matching.Padded.Posterior

open SteinerLowerBound
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ) (hQ : 0 < Q)

noncomputable def ideal (sortHeight : ℕ) (s : Cache S Q) (v : V)
    (ranks : E → Fin Q) : Cache S Q :=
  Kernel.final S Q sortHeight s v (fun e => Kernel.observe S Q s v e (ranks e))

theorem extension_joint [Fintype E] (sortHeight : ℕ) (s : Cache S Q) (v : V)
    (hb : Buckets.bound (s.level v + 1) ≤ Q)
    (f : Cache S Q → (E → Fin Q) → ℝ) :
    (Cache.completion S Q hQ s).expect (fun ranks => f (ideal S Q sortHeight s v ranks) ranks) =
      (Cache.extend S Q hQ sortHeight v s).expect
        (fun s' => (Cache.completion S Q hQ s').expect (f s')) := by
  let g : (E → Option (Fin Q)) × (E → Fin Q) → ℝ := fun z =>
    f (Kernel.final S Q sortHeight s v z.1) z.2
  calc
    _ = ((Cache.completion S Q hQ s).map
        (fun ranks => ((fun e => Kernel.observe S Q s v e (ranks e)), ranks))).expect g := by
      rw [Law.expect_map]
      rfl
    _ = (Law.pi (Kernel.observationLaw S Q hQ s v)).expect
        (fun obs => (Law.pi (Kernel.posterior S Q hQ s v obs)).expect
          (fun ranks => f (Kernel.final S Q sortHeight s v obs) ranks)) := by
      rw [Kernel.joint S Q hQ s v hb, Law.expect_bind]
      simp only [Law.expect_map]
      rfl
    _ = (Cache.collect S Q hQ (Cache.boundary S Q s v) (Buckets.bound (s.level v + 1)) v s).expect
        (fun entries =>
          (Cache.completion S Q hQ (Cache.finish S Q sortHeight v s entries).value).expect
            (f (Cache.finish S Q sortHeight v s entries).value)) := by
      rw [Plan.collect_law S Q hQ s v hb]
      congr 1
      funext obs
      change (Law.pi (Kernel.posterior S Q hQ s v obs)).expect
          (f (Kernel.final S Q sortHeight s v obs)) =
        (Cache.completion S Q hQ (Kernel.final S Q sortHeight s v obs)).expect
          (f (Kernel.final S Q sortHeight s v obs))
      rw [Kernel.final_completion]
    _ = _ := by
      unfold Cache.extend
      simp only [hb, ↓reduceIte, Program.expect_bind, Program.expect_tick, Program.expect_ret]

theorem extension_preserves_rank_law [Fintype E] (sortHeight : ℕ) (s : Cache S Q) (v : V)
    (hb : Buckets.bound (s.level v + 1) ≤ Q) (f : (E → Fin Q) → ℝ) :
    (Cache.extend S Q hQ sortHeight v s).expect
      (fun s' => (Cache.completion S Q hQ s').expect f) =
        (Cache.completion S Q hQ s).expect f :=
  (extension_joint S Q hQ sortHeight s v hb (fun _ ranks => f ranks)).symm

end SteinerUpperBound.Matching.Padded.Posterior
