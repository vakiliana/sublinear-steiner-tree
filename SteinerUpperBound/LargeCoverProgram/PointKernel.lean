module

public import SteinerUpperBound.LargeCoverProgram.Point
public import SteinerUpperBound.PortGraph.Frames

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

variable {Q A : Type} [Fintype A] {n k d B : ℕ}

noncomputable def componentAt (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (u : Fin (k + 1)) : Finset (Fin n) :=
  PortGraph.portComponent I bits cfg (cfg.terminals.get u)

noncomputable def coveredComponent (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (C : Finset (Fin n)) : Bool :=
  (LocalAccess.hitsResult cfg.covered (PortGraph.pointList cfg C)).value

noncomputable def pointKernel (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (mu : Law A) (u : Fin (k + 1)) :
    Law (A × Bool) :=
  mu.bind fun rank => (CategoricalCoupling.bernoulli
    (inverseRate (componentAt I bits cfg u).card)).map fun coin => (rank, coin)

noncomputable def pointScore (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (B : ℕ)
    (matched : Finset (Fin n) → A → Bool) (u : Fin (k + 1)) (seed : A × Bool) : ℝ :=
  if bits (cfg.key (cfg.terminals.get u)) then
    if (componentAt I bits cfg u).card ≤ B then
      if coveredComponent cfg (componentAt I bits cfg u) then
        1 / ((componentAt I bits cfg u).card : ℝ)
      else if seed.2 then (if matched (componentAt I bits cfg u) seed.1 then 1 / 2 else 0) else 0
    else 0
  else 0

/-- Only genuine frames reached by the point code require a cache law. -/
def CanonicalVOCache (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (d B : ℕ) (vo : VO Q n d B) : Prop :=
  ∀ C ∈ PortGraph.parts I bits cfg, C.card ≤ B → coveredComponent cfg C = false →
    ∀ c, Cache.Correct bits c → ∀ o,
      Runs I.weight bits (vo (PortGraph.canonicalFrame I cfg d B C) c) o →
        Cache.Correct bits o.value.2

/-- This is a genuine one-call matching-value refinement. It neither states a
point-score mean nor a saving bound. `matched` is instantiated with the actual
finite port graph's vertex-oracle predicate in the saving contract. -/
structure VORefinement (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (d B : ℕ)
    (vo : VO Q n d B) (mu : Law A) (matched : Finset (Fin n) → A → Bool) : Prop where
  cache_correct : CanonicalVOCache I bits cfg d B vo
  value_law : ∀ C ∈ PortGraph.parts I bits cfg, C.card ≤ B →
    coveredComponent cfg C = false → ∀ c, Cache.Correct bits c → ∀ F : Bool → ℝ,
      (vo (PortGraph.canonicalFrame I cfg d B C) c).evaluate I.weight bits
        (fun o => F o.value.1) = mu.expect (fun rank => F (matched C rank))

theorem terminal_get_mem (cfg : LocalAccess.SlotConfig Q n (k + 1)) (u : Fin (k + 1)) :
    cfg.terminals.get u ∈ cfg.terminals.toList := by
  exact (Vector.mem_toList_iff).mpr (Vector.getElem_mem u.isLt)

theorem componentAt_part (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (u : Fin (k + 1))
    (hu : bits (cfg.key (cfg.terminals.get u)) = true) :
    componentAt I bits cfg u ∈ PortGraph.parts I bits cfg := by
  apply Covers.Geometry.componentOn_mem_componentsOn
  exact (PortGraph.mem_retained I bits cfg _).mpr
    ⟨(PortGraph.terminal_mem I cfg hT _).mp (terminal_get_mem cfg u), hu⟩

theorem componentAt_subset (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (u : Fin (k + 1)) :
    componentAt I bits cfg u ⊆ I.terminals :=
  (Covers.Geometry.componentOn_subset I _ _ _).trans (PortGraph.retained_subset I bits cfg)

theorem point_cache_canonical (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (vo : VO Q n d B) (hvo : CanonicalVOCache I bits cfg d B vo)
    (u : Fin (k + 1)) (c : Cache Q) (hc : Cache.Correct bits c) :
    ∀ o, Runs I.weight bits
      (point cfg.key cfg.scale (List.finRange n) cfg.terminals.toList cfg.covered vo (cfg.terminals.get u) c) o →
        Cache.Correct bits o.value.2 := by
  intro o ho
  obtain ⟨reply, rest, hr, ht, rfl⟩ := Mean.runs_bind_inv I.weight bits
    (Cache.resolve (cfg.key (cfg.terminals.get u)) c) _ _ ho
  have he := deterministic_run_eq I.weight bits _ (resolve_deterministic _ _) _
    (Cache.resolve_evaluates I.weight bits _ _) reply hr
  subst reply
  have hr := Cache.resolved_correct bits (cfg.key (cfg.terminals.get u)) c hc
  cases ht with
  | tick ht =>
    cases hb : (Cache.resolved bits (cfg.key (cfg.terminals.get u)) c).value.1
    · simp only [hb, Bool.false_eq_true, ite_false] at ht
      cases ht
      exact hr.2
    · simp only [hb, ite_true] at ht
      have hu : bits (cfg.key (cfg.terminals.get u)) = true := hr.1.symm.trans hb
      have hx : cfg.terminals.get u ∈ PortGraph.retained I bits cfg :=
        (PortGraph.mem_retained I bits cfg _).mpr
          ⟨(PortGraph.terminal_mem I cfg hT _).mp (terminal_get_mem cfg u), hu⟩
      obtain ⟨l, z, hl, hz, rfl⟩ := Mean.runs_bind_inv I.weight bits
        (LocalAccess.locateProgram cfg.key cfg.scale d B (List.finRange n) cfg.terminals.toList
          (cfg.terminals.get u) _) _ _ ht
      have he := deterministic_run_eq I.weight bits _ (locate_deterministic _ _ _ _ _ _ _ _) _
        (LocalAccess.locate_evaluates I.weight bits _ _ _ _ _ _ _ _) l hl
      subst l
      have hlc := LocalAccess.locate_cache_correct I.weight bits cfg.key cfg.scale d B
        (List.finRange n) cfg.terminals.toList (cfg.terminals.get u) _ hr.2
      have hframe := PortGraph.locate_frame I bits cfg d B hT hnd hx
        (Cache.resolved bits (cfg.key (cfg.terminals.get u)) c).value.2 hr.2
      change (LocalAccess.locateResult I.weight bits cfg.key cfg.scale d B (List.finRange n)
        cfg.terminals.toList (cfg.terminals.get u) _).value.frame =
          if (componentAt I bits cfg u).card ≤ B then
            some (PortGraph.canonicalFrame I cfg d B (componentAt I bits cfg u)) else none at hframe
      cases hz with
      | tick hz =>
        by_cases hs : (componentAt I bits cfg u).card ≤ B
        · rw [ite_eq_left hs] at hframe
          simp only [afterPointLocate, hframe] at hz
          have hfinal := afterPointFrame_cache_for I.weight bits cfg.covered vo _ _ hlc
            (fun hh => hvo _ (componentAt_part I bits cfg hT u hu) hs
              (by simpa only [PortGraph.canonicalFrame_points, coveredComponent] using hh) _ hlc) _ hz
          simpa only [Outcome.combine, Outcome.add] using hfinal
        · rw [ite_eq_right hs] at hframe
          simp only [afterPointLocate, hframe] at hz
          cases hz
          exact hlc

theorem pointScore_bounds (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (matched : Finset (Fin n) → A → Bool)
    (u : Fin (k + 1)) (seed : A × Bool) :
    0 ≤ pointScore I bits cfg B matched u seed ∧ pointScore I bits cfg B matched u seed ≤ 1 := by
  have hr (c : ℕ) : 0 ≤ 1 / (c : ℝ) ∧ 1 / (c : ℝ) ≤ 1 := by
    by_cases hc : c = 0
    · simp [hc]
    · have hp : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
      have h1 : (1 : ℝ) ≤ c := by exact_mod_cast Nat.pos_of_ne_zero hc
      exact ⟨by positivity, (div_le_one hp).mpr h1⟩
  unfold pointScore
  split_ifs <;> first | exact hr _ | norm_num

/-- The conditional point kernel is independent of every correct incoming
cache. This is derived from actual resolution, exploration, D tests, and the
initiation coin; it is not supplied as a score certificate. -/
theorem point_kernelSpec (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (vo : VO Q n d B) (mu : Law A) (matched : Finset (Fin n) → A → Bool)
    (hvo : VORefinement I bits cfg d B vo mu matched) :
    Mean.KernelSpec
      (fun u c => point cfg.key cfg.scale (List.finRange n) cfg.terminals.toList
        cfg.covered vo (cfg.terminals.get u) c)
      I.weight bits (pointKernel I bits cfg mu) (pointScore I bits cfg B matched) := by
  refine ⟨?_, ?_⟩
  · intro u c hc o ho
    exact point_cache_canonical I bits cfg hT hnd vo hvo.cache_correct u c hc o ho
  · intro u c hc F
    rw [point_value I.weight bits cfg.key cfg.scale _ _ cfg.covered vo
      (cfg.terminals.get u) c hc]
    have hcache := (Cache.resolved_correct bits (cfg.key (cfg.terminals.get u)) c hc).2
    have hlcache := LocalAccess.locate_cache_correct I.weight bits cfg.key cfg.scale d B
      (List.finRange n) cfg.terminals.toList (cfg.terminals.get u) _ hcache
    simp only [pointKernel, Law.expect_bind, Law.expect_map]
    cases hu : bits (cfg.key (cfg.terminals.get u))
    · simp [pointScore, hu]
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
        · have hv := hvo.value_law (componentAt I bits cfg u)
            (componentAt_part I bits cfg hT u hu) hs hh _ hlcache
            (fun v => F (if v then (1 / 2 : ℝ) else 0))
          simp only [pointScore, hu, hs, hh, ite_true, Bool.false_eq_true, ite_false]
          rw [SavingScores.bernoulli_expect]
          simp only [ite_true, Bool.false_eq_true, ite_false]
          rw [hv]
          simp_rw [SavingScores.bernoulli_expect]
          simp only [ite_true, Bool.false_eq_true, ite_false, Law.expect_add,
            Law.expect_const_mul, Law.expect_const]
        · simp only [ite_true, pointScore, hu, hs, hh, Law.expect_const]
      · rw [ite_eq_right hs]
        simp [pointScore, hu, hs]

end SteinerUpperBound.LargeCoverProgram
