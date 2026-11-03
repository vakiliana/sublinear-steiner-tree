module

public import SteinerUpperBound.LargeCoverProgram.PointSupport
public import SteinerUpperBound.LargeCoverProgram.ApproxMean

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

variable {Q A : Type} [Fintype A] {n k d B : ℕ}

/-- An actual matching CODE call may fail on a separately budgeted event.
Its Boolean value law is approximated; cache correctness holds on actual
positive support, without imposing conditions on zero-mass branches. -/
structure VOApproxRefinement (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (d B : ℕ)
    (vo : VO Q n d B) (mu : Law A) (matched : Finset (Fin n) → A → Bool) (delta : ℝ) : Prop where
  cache_correct : CanonicalVOEnsures I bits cfg d B vo
  value_error : ∀ C ∈ PortGraph.parts I bits cfg, C.card ≤ B →
    coveredComponent cfg C = false → ∀ c, Cache.Correct bits c → ∀ F : Bool → ℝ,
      (∀ v, 0 ≤ F v) → (∀ v, F v ≤ 1) →
      |(vo (PortGraph.canonicalFrame I cfg d B C) c).evaluate I.weight bits
        (fun o => F o.value.1) - mu.expect (fun rank => F (matched C rank))| ≤ delta

theorem point_approxKernelSpec (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (vo : VO Q n d B) (mu : Law A) (matched : Finset (Fin n) → A → Bool) (delta : ℝ)
    (hd : 0 ≤ delta) (hvo : VOApproxRefinement I bits cfg d B vo mu matched delta) :
    ApproxKernelSpec
      (fun u c => point cfg.key cfg.scale (List.finRange n) cfg.terminals.toList
        cfg.covered vo (cfg.terminals.get u) c)
      I.weight bits (pointKernel I bits cfg mu) (pointScore I bits cfg B matched) delta := by
  refine ⟨?_, ?_⟩
  · intro u c hc
    exact point_cache_ensures I bits cfg hT hnd vo hvo.cache_correct u c hc
  · intro u c hc F hF₀ hF₁
    rw [point_value I.weight bits cfg.key cfg.scale _ _ cfg.covered vo
      (cfg.terminals.get u) c hc]
    have hcache := (Cache.resolved_correct bits (cfg.key (cfg.terminals.get u)) c hc).2
    have hlcache := LocalAccess.locate_cache_correct I.weight bits cfg.key cfg.scale d B
      (List.finRange n) cfg.terminals.toList (cfg.terminals.get u) _ hcache
    simp only [pointKernel, Law.expect_bind, Law.expect_map]
    cases hu : bits (cfg.key (cfg.terminals.get u))
    · simpa [pointScore, hu] using hd
    · have hx : cfg.terminals.get u ∈ PortGraph.retained I bits cfg :=
        (PortGraph.mem_retained I bits cfg _).mpr
          ⟨(PortGraph.terminal_mem I cfg hT _).mp (terminal_get_mem cfg u), hu⟩
      rw [PortGraph.locate_frame I bits cfg d B hT hnd hx _ hcache]
      rw [show PortGraph.portComponent I bits cfg (cfg.terminals.get u) =
        componentAt I bits cfg u from rfl]
      simp only [ite_true]
      by_cases hs : (componentAt I bits cfg u).card ≤ B
      · rw [ite_eq_left hs]
        have hlen := PortGraph.pointList_length I cfg hT hnd (componentAt I bits cfg u)
          (componentAt_subset I bits cfg u)
        unfold frameValue
        simp only [PortGraph.canonicalFrame_points, hlen]
        rw [show (LocalAccess.hitsResult cfg.covered
          (PortGraph.pointList cfg (componentAt I bits cfg u))).value =
            coveredComponent cfg (componentAt I bits cfg u) from rfl]
        cases hh : coveredComponent cfg (componentAt I bits cfg u)
        · have hv := hvo.value_error (componentAt I bits cfg u)
            (componentAt_part I bits cfg hT u hu) hs hh _ hlcache
            (fun v => F (if v then (1 / 2 : ℝ) else 0))
            (fun v => hF₀ _) (fun v => hF₁ _)
          simp only [pointScore, hu, hs, hh, ite_true, Bool.false_eq_true, ite_false]
          simp_rw [SavingScores.bernoulli_expect]
          simp only [ite_true, Bool.false_eq_true, ite_false, Law.expect_add,
            Law.expect_const_mul, Law.expect_const]
          have he : |(inverseRate (componentAt I bits cfg u).card : ℝ) *
              ((vo (PortGraph.canonicalFrame I cfg d B (componentAt I bits cfg u))
                (LocalAccess.locateResult I.weight bits cfg.key cfg.scale d B (List.finRange n)
                  cfg.terminals.toList (cfg.terminals.get u)
                  (Cache.resolved bits (cfg.key (cfg.terminals.get u)) c).value.2).value.cache).evaluate
                    I.weight bits (fun o => F (if o.value.1 then (1 / 2 : ℝ) else 0)) -
                mu.expect (fun rank => F (if matched (componentAt I bits cfg u) rank then 1 / 2 else 0)))| ≤ delta := by
            rw [abs_mul, abs_of_nonneg (inverseRate _).property.1]
            have hm := mul_le_mul_of_nonneg_left hv
              (inverseRate (componentAt I bits cfg u).card).property.1
            nlinarith [(inverseRate (componentAt I bits cfg u).card).property.2]
          convert he using 1 <;> congr 1 <;> ring
        · simpa only [ite_true, pointScore, hu, hs, hh, Law.expect_const, sub_self, abs_zero] using hd
      · rw [ite_eq_right hs]
        simpa [pointScore, hu, hs] using hd

end SteinerUpperBound.LargeCoverProgram
