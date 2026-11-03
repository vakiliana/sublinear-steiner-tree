module

public import SteinerUpperBound.Matching.Padded.IteratorCorrect

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical

variable {V E A B : Type*} {G : Graph V E} {S : Slots G} {Q : ℕ} [Fintype E]

def Joint (hQ : 0 < Q) (s : Cache S Q) (cache : A → Cache S Q)
    (p : Program (Command S) A) (ideal : (E → Fin Q) → A) : Prop :=
  ∀ f : A → (E → Fin Q) → ℝ,
    (Cache.completion S Q hQ s).expect (fun ranks => f (ideal ranks) ranks) =
      p.expect (fun a => (Cache.completion S Q hQ (cache a)).expect (f a))

namespace Joint

theorem ret {hQ : 0 < Q} {s : Cache S Q} {cache : A → Cache S Q} (a : A)
    (h : cache a = s) : Joint hQ s cache (.ret a) (fun _ => a) := by
  intro f
  simp only [Program.expect_ret, h]

theorem tick {hQ : 0 < Q} {s : Cache S Q} {cache : A → Cache S Q}
    {p : Program (Command S) A} {ideal : (E → Fin Q) → A} (c : Command S)
    (h : Joint hQ s cache p ideal) : Joint hQ s cache (.tick c p) ideal := h

theorem bind {hQ : 0 < Q} {s : Cache S Q} {cacheA : A → Cache S Q} {cacheB : B → Cache S Q}
    {p : Program (Command S) A} {k : A → Program (Command S) B}
    {ideal : (E → Fin Q) → A} {next : A → (E → Fin Q) → B}
    (hp : Joint hQ s cacheA p ideal)
    (hk : ∀ a, Joint hQ (cacheA a) cacheB (k a) (next a)) :
    Joint hQ s cacheB (p.bind k) (fun ranks => next (ideal ranks) ranks) := by
  intro f
  rw [Program.expect_bind]
  calc
    _ = p.expect (fun a => (Cache.completion S Q hQ (cacheA a)).expect
        (fun ranks => f (next a ranks) ranks)) := hp _
    _ = _ := by
      apply congrArg p.expect
      funext a
      exact hk a f

theorem map {hQ : 0 < Q} {s : Cache S Q} {cacheA : A → Cache S Q} {cacheB : B → Cache S Q}
    {p : Program (Command S) A} {ideal : (E → Fin Q) → A}
    (hp : Joint hQ s cacheA p ideal) (g : A → B) (hg : ∀ a, cacheB (g a) = cacheA a) :
    Joint hQ s cacheB (p.bind (fun a => .ret (g a))) (fun ranks => g (ideal ranks)) :=
  bind hp (fun a => ret (g a) (hg a))

theorem next (hQ : 0 < Q) (height maxLevel : ℕ) (v : V) (cursor : ℕ) (s : Cache S Q) :
    Joint hQ s Prod.snd (Cache.next S Q hQ height maxLevel v cursor s)
      (Cache.idealNext S Q height maxLevel v cursor s) :=
  Cache.next_joint S Q hQ height maxLevel v cursor s

end Joint

end SteinerUpperBound.Matching.Padded
