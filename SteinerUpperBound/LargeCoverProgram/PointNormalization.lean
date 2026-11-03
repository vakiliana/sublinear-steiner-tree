module

public import SteinerUpperBound.LargeCoverProgram.PointCounters
public import SteinerUpperBound.LargeCoverProgram.Normalization

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

variable {Q : Type} {n k d B : ℕ}

theorem sum_residual_vertex_at (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (C : Finset (Fin n)) (z : ℝ) :
    (∑ V : PortGraph.Vertex I bits cfg B, if V.val = C then z else 0) =
      if C ∈ PortGraph.smallParts I bits cfg B then z else 0 := by
  by_cases hC : C ∈ PortGraph.smallParts I bits cfg B
  · let V0 : PortGraph.Vertex I bits cfg B := ⟨C, hC⟩
    have he (V : PortGraph.Vertex I bits cfg B) : V.val = C ↔ V = V0 := by
      constructor
      · intro h
        apply Subtype.ext
        exact h
      · intro h
        subst V
        rfl
    simp only [he, hC, ite_true]
    simp
  · simp only [hC, ite_false]
    apply Finset.sum_eq_zero
    intro V _
    have hv : V.val ≠ C := fun h => hC (h ▸ V.property)
    simp only [hv, ite_false]

theorem componentAt_small_iff (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (u : Fin (k + 1))
    (hu : bits (cfg.key (cfg.terminals.get u)) = true) :
    componentAt I bits cfg u ∈ PortGraph.smallParts I bits cfg B ↔
      (componentAt I bits cfg u).card ≤ B ∧ coveredComponent cfg (componentAt I bits cfg u) = false := by
  have hp := componentAt_part I bits cfg hT u hu
  simp only [PortGraph.smallParts, Finset.mem_filter, hp, true_and]
  exact and_congr_right (fun _ => (coveredComponent_false I bits cfg hT ⟨_, hp⟩).symm)

/-- The REAL incoming cache of the VO after actual root resolution and eager
component/frame preparation. This is analysis-only, not a runtime oracle. -/
noncomputable def pointOracleCache (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (d B : ℕ)
    (u : Fin (k + 1)) (c : Cache Q) : Cache Q :=
  (LocalAccess.locateResult I.weight bits cfg.key cfg.scale d B (List.finRange n) cfg.terminals.toList
    (cfg.terminals.get u) (Cache.resolved bits (cfg.key (cfg.terminals.get u)) c).value.2).value.cache

theorem pointOracleCache_correct (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (d B : ℕ)
    (u : Fin (k + 1)) (c : Cache Q) (hc : Cache.Correct bits c) :
    Cache.Correct bits (pointOracleCache I bits cfg d B u c) :=
  LocalAccess.locate_cache_correct I.weight bits cfg.key cfg.scale d B (List.finRange n)
    cfg.terminals.toList (cfg.terminals.get u) _
    (Cache.resolved_correct bits (cfg.key (cfg.terminals.get u)) c hc).2

/-- Exact bridge from the actual point callback profile to the fiber selector
normalization. Incoming caches may depend on the sampled point arbitrarily. -/
theorem pointCallCost_as_initiatedPointCharge (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (vo : VO Q n d B) (caches : Fin (k + 1) → Cache Q)
    (hc : ∀ u, Cache.Correct bits (caches u))
    (F : Outcome (Bool × Cache Q) → ℝ) (u : Fin (k + 1)) :
    pointCallCost I.weight bits cfg.key cfg.scale (List.finRange n) cfg.terminals.toList
      cfg.covered vo (cfg.terminals.get u) (caches u) F =
      initiatedPointCharge (B := B) I bits cfg
        (fun v => (vo (PortGraph.canonicalFrame I cfg d B (componentAt I bits cfg v))
          (pointOracleCache I bits cfg d B v (caches v))).evaluate I.weight bits F) u := by
  dsimp only [pointCallCost, initiatedPointCharge]
  cases hu : bits (cfg.key (cfg.terminals.get u))
  · simp only [hu, Bool.false_eq_true, ite_false]
  · simp only [hu, ite_true]
    have hr := (Cache.resolved_correct bits (cfg.key (cfg.terminals.get u)) (caches u) (hc u)).2
    have hx : cfg.terminals.get u ∈ PortGraph.retained I bits cfg :=
      (PortGraph.mem_retained I bits cfg _).mpr
        ⟨(PortGraph.terminal_mem I cfg hT _).mp (terminal_get_mem cfg u), hu⟩
    rw [PortGraph.locate_frame I bits cfg d B hT hnd hx _ hr]
    change (if (componentAt I bits cfg u).card ≤ B then
      some (PortGraph.canonicalFrame I cfg d B (componentAt I bits cfg u)) else none).elim _ _ = _
    simp only [sum_residual_vertex_at, componentAt_small_iff I bits cfg hT u hu]
    by_cases hs : (componentAt I bits cfg u).card ≤ B
    · rw [ite_eq_left hs]
      simp only [Option.elim_some]
      have hlen := PortGraph.pointList_length I cfg hT hnd (componentAt I bits cfg u)
        (componentAt_subset I bits cfg u)
      simp only [frameInitiation, PortGraph.canonicalFrame_points, hlen]
      change (if coveredComponent cfg (componentAt I bits cfg u) then 0 else
          (inverseRate (componentAt I bits cfg u).card : ℝ)) * _ = _
      cases hh : coveredComponent cfg (componentAt I bits cfg u) <;>
        simp only [hh, hs, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false,
          and_true, and_false, true_and, false_and, zero_mul, mul_zero, pointOracleCache]
    · simp only [hs, ite_false, false_and, Option.elim_none, mul_zero]

/-- Arbitrary correct cache families are enough: eager point caches may depend
on the initiating point and on all previous observations. -/
theorem pointCallCost_family_average_bound (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty)
    (vo : VO Q n d B) (caches : Fin (k + 1) → Cache Q)
    (hc : ∀ u, Cache.Correct bits (caches u))
    (F : Outcome (Bool × Cache Q) → ℝ) (budget : ℝ)
    (hfamily : ∀ stores : PortGraph.Vertex I bits cfg B → Cache Q,
      (∀ C, Cache.Correct bits (stores C)) →
      (∑ C, (vo (PortGraph.canonicalFrame I cfg d B C.val) (stores C)).evaluate I.weight bits F) /
        (Nat.card (RetainedIndex bits cfg) : ℝ) ≤ budget) :
    (Covers.Rejection.uniformRetained (fun u => bits (cfg.key (cfg.terminals.get u))) hb).expect
      (fun u => pointCallCost I.weight bits cfg.key cfg.scale (List.finRange n) cfg.terminals.toList
        cfg.covered vo (cfg.terminals.get u) (caches u) F) ≤ budget := by
  let f := fun u => (vo (PortGraph.canonicalFrame I cfg d B (componentAt I bits cfg u))
    (pointOracleCache I bits cfg d B u (caches u))).evaluate I.weight bits F
  have he : (fun u => pointCallCost I.weight bits cfg.key cfg.scale (List.finRange n) cfg.terminals.toList
      cfg.covered vo (cfg.terminals.get u) (caches u) F) =
      initiatedPointCharge (B := B) I bits cfg f := by
    funext u
    exact pointCallCost_as_initiatedPointCharge I bits cfg hT hnd vo caches hc F u
  rw [he]
  apply initiatedPointCharge_family_average_bound I bits cfg hT hnd hb f budget
  intro pick hpick
  let stores := fun C : PortGraph.Vertex I bits cfg B =>
    pointOracleCache I bits cfg d B (pick C).val (caches (pick C).val)
  have hs : ∀ C, Cache.Correct bits (stores C) :=
    fun C => pointOracleCache_correct I bits cfg d B (pick C).val _ (hc _)
  have h := hfamily stores hs
  have hf : (fun C => f (pick C).val) =
      (fun C => (vo (PortGraph.canonicalFrame I cfg d B C.val) (stores C)).evaluate I.weight bits F) := by
    funext C
    have hv : componentAt I bits cfg (pick C).val = C.val := by
      have h := congrArg (fun P : Part I bits cfg => P.val) (hpick C)
      change componentAt I bits cfg (pick C).val = C.val at h
      exact h
    dsimp only [f, stores]
    rw [hv]
  simpa only [hf] using h

theorem point_clipped_average (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty)
    (vo : VO Q n d B) (caches : Fin (k + 1) → Cache Q) (hc : ∀ u, Cache.Correct bits (caches u))
    (threshold : ℝ) (ht : 0 ≤ threshold) (AW AP : ℝ)
    (hwork : ∀ stores : PortGraph.Vertex I bits cfg B → Cache Q,
      (∀ C, Cache.Correct bits (stores C)) →
      (∑ C, (vo (PortGraph.canonicalFrame I cfg d B C.val) (stores C)).evaluate I.weight bits
        (fun o => min (o.work : ℝ) threshold)) / (Nat.card (RetainedIndex bits cfg) : ℝ) ≤ AW)
    (hpositive : ∀ stores : PortGraph.Vertex I bits cfg B → Cache Q,
      (∀ C, Cache.Correct bits (stores C)) →
      (∑ C, (vo (PortGraph.canonicalFrame I cfg d B C.val) (stores C)).evaluate I.weight bits
        (fun o => min (o.positiveReplies : ℝ) threshold)) / (Nat.card (RetainedIndex bits cfg) : ℝ) ≤ AP) :
    let mu := Covers.Rejection.uniformRetained (fun u => bits (cfg.key (cfg.terminals.get u))) hb
    mu.expect (fun u => (point cfg.key cfg.scale (List.finRange n) cfg.terminals.toList
      cfg.covered vo (cfg.terminals.get u) (caches u)).evaluate I.weight bits
        (fun o => min (o.work : ℝ) threshold)) ≤ pointBudget n (k + 1) d B + AW ∧
      mu.expect (fun u => (point cfg.key cfg.scale (List.finRange n) cfg.terminals.toList
        cfg.covered vo (cfg.terminals.get u) (caches u)).evaluate I.weight bits
          (fun o => min (o.positiveReplies : ℝ) threshold)) ≤ (B : ℝ) + 1 + AP := by
  dsimp only
  let mu := Covers.Rejection.uniformRetained (fun u => bits (cfg.key (cfg.terminals.get u))) hb
  have hw := Law.expect_mono mu (fun u =>
    point_work_min I.weight bits cfg.key cfg.scale (List.finRange n) cfg.terminals.toList
      cfg.covered vo (cfg.terminals.get u) (caches u) (hc u) hnd (terminal_get_mem cfg u) threshold)
  have hp := Law.expect_mono mu (fun u =>
    point_positive_min I.weight bits cfg.key cfg.scale (List.finRange n) cfg.terminals.toList
      cfg.covered vo (cfg.terminals.get u) (caches u) (hc u) threshold ht)
  have hw' := pointCallCost_family_average_bound I bits cfg hT hnd hb vo caches hc
    (fun o => min (o.work : ℝ) threshold) AW hwork
  have hp' := pointCallCost_family_average_bound I bits cfg hT hnd hb vo caches hc
    (fun o => min (o.positiveReplies : ℝ) threshold) AP hpositive
  simp only [Law.expect_add, Law.expect_const, List.length_finRange, Vector.length_toList] at hw hp
  constructor <;> linarith

end SteinerUpperBound.LargeCoverProgram
