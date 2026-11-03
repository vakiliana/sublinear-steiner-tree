module

public import SteinerUpperBound.LargeCoverProgram.PointKernel
public import SteinerUpperBound.LargeCoverProgram.Support

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram Matching.Padded
open scoped Classical

variable {Q : Type} {n k d B : ℕ}

def CanonicalVOEnsures (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (d B : ℕ) (vo : VO Q n d B) : Prop :=
  ∀ C ∈ PortGraph.parts I bits cfg, C.card ≤ B → coveredComponent cfg C = false →
    ∀ c, Cache.Correct bits c →
      Causal.Ensures I.weight bits (vo (PortGraph.canonicalFrame I cfg d B C) c)
        (fun reply => Cache.Correct bits reply.2)

theorem afterPointFrame_cache_ensures (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (D : Vector Bool n) (vo : VO Q n d B) (f : LocalAccess.Frame (Fin n) d B)
    (c : Cache Q) (hc : Cache.Correct bits c)
    (hvo : (LocalAccess.hitsResult D f.points).value = false →
      Causal.Ensures w bits (vo f c) (fun reply => Cache.Correct bits reply.2)) :
    Causal.Ensures w bits (afterPointFrame D vo f c) (fun reply => Cache.Correct bits reply.2) := by
  unfold afterPointFrame
  refine Support.ensures_bind_evaluates w bits _ _ _ (LocalAccess.hits_evaluates w bits D f.points) _ ?_
  refine Support.ensures_bind_evaluates w bits _ _ _ (length_evaluates w bits f.points) _ ?_
  apply Support.ensures_tick
  cases hh : (LocalAccess.hitsResult D f.points).value
  · simp only [hh, Bool.false_eq_true, ite_false]
    apply Support.ensures_coin
    intro initiate
    apply Support.ensures_tick
    cases initiate
    · simp only [Bool.false_eq_true, ite_false]
      exact Support.ensures_pure w bits _ _ hc
    · simp only [ite_true]
      apply Support.ensures_bind w bits _ _ (fun reply => Cache.Correct bits reply.2) _
        (hvo hh)
      intro reply hr
      apply Support.ensures_tick
      exact Support.ensures_pure w bits _ _ hr
  · simp only [hh, ite_true]
    exact Support.ensures_pure w bits _ _ hc

theorem point_cache_ensures (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (vo : VO Q n d B) (hvo : CanonicalVOEnsures I bits cfg d B vo)
    (u : Fin (k + 1)) (c : Cache Q) (hc : Cache.Correct bits c) :
    Causal.Ensures I.weight bits
      (point cfg.key cfg.scale (List.finRange n) cfg.terminals.toList cfg.covered vo (cfg.terminals.get u) c)
      (fun reply => Cache.Correct bits reply.2) := by
  unfold point
  refine Support.ensures_bind_evaluates I.weight bits _ _ _
    (Cache.resolve_evaluates I.weight bits _ _) _ ?_
  apply Support.ensures_tick
  have hr := Cache.resolved_correct bits (cfg.key (cfg.terminals.get u)) c hc
  rw [hr.1]
  cases hu : bits (cfg.key (cfg.terminals.get u))
  · simp only [hu, Bool.false_eq_true, ite_false]
    exact Support.ensures_pure I.weight bits _ _ hr.2
  · simp only [hu, ite_true]
    have hx : cfg.terminals.get u ∈ PortGraph.retained I bits cfg :=
      (PortGraph.mem_retained I bits cfg _).mpr
        ⟨(PortGraph.terminal_mem I cfg hT _).mp (terminal_get_mem cfg u), hu⟩
    refine Support.ensures_bind_evaluates I.weight bits _ _ _
      (LocalAccess.locate_evaluates I.weight bits cfg.key cfg.scale d B
        (List.finRange n) cfg.terminals.toList (cfg.terminals.get u) _) _ ?_
    have hlc := LocalAccess.locate_cache_correct I.weight bits cfg.key cfg.scale d B
      (List.finRange n) cfg.terminals.toList (cfg.terminals.get u) _ hr.2
    have hframe := PortGraph.locate_frame I bits cfg d B hT hnd hx
      (Cache.resolved bits (cfg.key (cfg.terminals.get u)) c).value.2 hr.2
    unfold afterPointLocate
    apply Support.ensures_tick
    rw [hframe]
    change Causal.Ensures I.weight bits
      (match (if (componentAt I bits cfg u).card ≤ B then
          some (PortGraph.canonicalFrame I cfg d B (componentAt I bits cfg u)) else none) with
        | none => .pure _
        | some f => afterPointFrame cfg.covered vo f _) _
    by_cases hs : (componentAt I bits cfg u).card ≤ B
    · rw [ite_eq_left hs]
      apply afterPointFrame_cache_ensures I.weight bits _ _ _ _ hlc
      intro hh
      exact hvo _ (componentAt_part I bits cfg hT u hu) hs
        (by simpa only [PortGraph.canonicalFrame_points, coveredComponent] using hh) _ hlc
    · rw [ite_eq_right hs]
      exact Support.ensures_pure I.weight bits _ _ hlc

end SteinerUpperBound.LargeCoverProgram
