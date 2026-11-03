module

public import SteinerUpperBound.Matching.Padded.Safety

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical

variable {V E A : Type*} {G : Graph V E} {S : Slots G} {Q : ℕ} [Fintype E]

theorem Joint.supported {hQ : 0 < Q} {s : Cache S Q} {cache : A → Cache S Q}
    {p : Program (Command S) A} {ideal : (E → Fin Q) → A}
    (h : Joint hQ s cache p ideal) (P : A → Prop)
    (hi : ∀ ranks, 0 < (Cache.completion S Q hQ s).mass ranks → P (ideal ranks)) :
    p.Supported P := by
  classical
  apply Program.supported_of_zero_bad
  have hj := h (fun a _ => if P a then (0 : ℝ) else 1)
  simp only [Law.expect_const] at hj
  rw [← hj]
  apply FiniteLaw.expect_zero_on_support
  intro ranks hm
  simp only [hi ranks hm, ↓reduceIte]

namespace Cache

variable (S : Slots G) (Q : ℕ) (hQ : 0 < Q)

omit [Fintype E] in
theorem extend_prepared (height : ℕ) (v : V) (s : Cache S Q) :
    (extend S Q hQ height v s).Supported (fun t => t.prepared = s.prepared) := by
  unfold extend
  dsimp only
  split_ifs
  · refine Program.supported_bind _ _ (fun _ => True) _ (fun _ => trivial) ?_
    intro entries _
    apply Program.supported_tick
    apply Program.supported_ret
    exact (commit_administration S Q s entries).1
  · exact Program.supported_ret _ _ rfl

variable [Fintype V]

theorem next_supported (P : Parameters S) (v : V) (cursor : ℕ) (s : Cache S P.rankCard)
    (hs : Invariant S P.rankCard s) :
    (next S P.rankCard P.rankCard_pos P.sortHeight (P.rankExponent + 1) v cursor s).Supported
      (fun answer => Invariant S P.rankCard answer.2 ∧
        ∀ x, answer.1 = some x → x.source.1 = v ∧ EntryValid S P.rankCard x) := by
  apply (Joint.next P.rankCard_pos P.sortHeight (P.rankExponent + 1) v cursor s).supported
  intro ranks hm
  have hc := completion_consistent S P.rankCard P.rankCard_pos s hs.legal ranks hm
  have hh := idealNext_safe S P v cursor s ranks hs hc
  exact ⟨hh.invariant, fun x hx => ⟨(hh.valid x hx).1, (hh.valid x hx).2.1⟩⟩

end Cache

end SteinerUpperBound.Matching.Padded
