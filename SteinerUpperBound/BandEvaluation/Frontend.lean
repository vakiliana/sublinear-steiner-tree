module

public import SteinerUpperBound.BandEvaluation.Component

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.BandEvaluation

open QueryProgram Covers.Geometry
open scoped Classical

noncomputable def pointScore {V : Type*} [Fintype V] (I : Instance V) (N : Finset V)
    (a rho tau : ℝ) (B : ℕ) (root : V) : ℝ :=
  let C := componentOn I N a root
  if C.card ≤ B then Band.score I C a rho tau / (3 * a * C.card) else 0

theorem pointScore_outside {V : Type*} [Fintype V] (I : Instance V) (N : Finset V)
    (a rho tau : ℝ) (B : ℕ) (root : V) (hr : root ∉ N) :
    pointScore I N a rho tau B root = 0 := by
  simp [pointScore, component_empty_of_not_mem I N a root hr, band_empty]

theorem pointScore_bounds {V : Type*} [Fintype V] (I : Instance V) (N : Finset V)
    (a rho tau : ℝ) (B : ℕ) (ha : 0 < a) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (hband : tau * a ≤ a - 2 * rho) (root : V) :
    0 ≤ pointScore I N a rho tau B root ∧ pointScore I N a rho tau B root ≤ 1 := by
  by_cases hr : root ∈ N
  · have hb := score_bounds I (componentOn I N a root) a rho tau ha.le hrho htau hband
    have hc : 0 < (componentOn I N a root).card :=
      Finset.card_pos.mpr (component_nonempty I N a root hr)
    have hc' : (0 : ℝ) < (componentOn I N a root).card := by exact_mod_cast hc
    have hc1 : (1 : ℝ) ≤ (componentOn I N a root).card := by exact_mod_cast hc
    have hden : 0 < 3 * a * ((componentOn I N a root).card : ℝ) := by positivity
    dsimp only [pointScore]
    split_ifs
    · exact ⟨div_nonneg hb.1 hden.le, (div_le_one hden).mpr (by nlinarith)⟩
    · norm_num
  · rw [pointScore_outside I N a rho tau B root hr]
    norm_num

variable {Q : Type*} {n : ℕ}

/-- The given root is already retained; its retention bit is not queried or charged again. -/
noncomputable def frontend (key : Fin n → Q) (a : ℝ) (B : ℕ) (terminals : List (Fin n))
    (rho tau : ℝ) (root : Fin n) (c : Cache Q) : Code (Sym2 (Fin n)) Q (ℝ × Cache Q) :=
  (ComponentExplore.program key a B terminals root c).bind (fun answer =>
    .tick 7 (if answer.complete then
      (BandEvaluation.program answer.memory.points a rho tau).bind (fun D =>
        .tick 15 (.pure (D / (3 * a * answer.memory.count), answer.memory.cache)))
      else .pure (0, answer.memory.cache)))

noncomputable def frontendRun (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q) :
    Outcome (ℝ × Cache Q) :=
  let ex := ComponentExplore.result w b key a B terminals root c
  ex.combine ((if ex.value.complete then
    let D := BandEvaluation.run w ex.value.memory.points a rho tau
    D.combine ((Outcome.pure (D.value / (3 * a * ex.value.memory.count), ex.value.memory.cache)).add 16 0 0 0)
    else Outcome.pure (0, ex.value.memory.cache)).add 8 0 0 0)

theorem frontend_evaluates (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q) :
    Code.Evaluates w b (frontend key a B terminals rho tau root c)
      (frontendRun w b key a B terminals rho tau root c) := by
  apply Code.Evaluates.bind _ _ _ _ _ _ (ComponentExplore.program_evaluates _ _ _ _ _ _ _ _)
  apply Code.Evaluates.tick
  split_ifs
  · exact Code.Evaluates.bind _ _ _ _ _ _ (BandEvaluation.program_evaluates _ _ _ _ _ _)
      (Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 15)
  · exact Code.evaluates_pure _ _ _

theorem frontend_noRandom (key : Fin n → Q) (a : ℝ) (B : ℕ) (terminals : List (Fin n))
    (rho tau : ℝ) (root : Fin n) (c : Cache Q) :
    NoRandom (frontend key a B terminals rho tau root c) := by
  apply noRandom_bind _ _ (explore_noRandom _ _ _ _ _ _)
  intro answer
  split_ifs
  · exact noRandom_bind _ _
      (metricOnly_noRandom _ (BandEvaluation.program_metricOnly _ _ _ _)) (fun _ => trivial)
  · trivial

theorem frontendRun_cache (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q) :
    (frontendRun w b key a B terminals rho tau root c).value.2 =
      (ComponentExplore.result w b key a B terminals root c).value.memory.cache := by
  dsimp only [frontendRun]
  split_ifs <;> rfl

theorem frontendRun_value (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q) :
    (frontendRun w b key a B terminals rho tau root c).value.1 =
      if (ComponentExplore.result w b key a B terminals root c).value.complete then
        (BandEvaluation.run w (ComponentExplore.result w b key a B terminals root c).value.memory.points
          a rho tau).value / (3 * a * (ComponentExplore.result w b key a B terminals root c).value.memory.count)
      else 0 := by
  dsimp only [frontendRun]
  split_ifs <;> rfl

theorem frontendRun_cache_correct (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct b c) :
    Cache.Correct b (frontendRun w b key a B terminals rho tau root c).value.2 := by
  rw [frontendRun_cache]
  exact (ComponentExplore.result_valid w b key a B terminals root c hc).cache_correct

theorem frontendRun_correct (I : Instance (Fin n)) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct b c) (hr : root ∈ retainedSet b key terminals)
    (hband : tau * a ≤ a - 2 * rho) :
    (frontendRun I.weight b key a B terminals rho tau root c).value.1 =
      pointScore I (retainedSet b key terminals) a rho tau B root := by
  let ex := ComponentExplore.result I.weight b key a B terminals root c
  have hv := ComponentExplore.result_valid I.weight b key a B terminals root c hc
  have hclass := explore_complete_iff I b key a B terminals root c hc hr
  rw [frontendRun_value]
  cases hcomplete : ex.value.complete with
  | false =>
      have hn : ¬(trueComponent I b key terminals a root).card ≤ B := by
        intro h
        have hh := hclass.mpr h
        change ex.value.complete = true at hh
        simp only [hcomplete, Bool.false_eq_true] at hh
      have hn' : ¬(componentOn I (retainedSet b key terminals) a root).card ≤ B := by
        simpa only [trueComponent] using hn
      simp only [Bool.false_eq_true, ↓reduceIte, pointScore, hn']
  | true =>
      have he := explore_points_of_complete I b key a B terminals root c hc hr hcomplete
      have he' : ex.value.memory.points.toFinset = trueComponent I b key terminals a root := by
        ext x
        simpa only [List.mem_toFinset] using Finset.ext_iff.mp he x
      have hlen : ex.value.memory.points.length = (trueComponent I b key terminals a root).card := by
        have hh := List.toFinset_card_of_nodup hv.points_nodup
        rw [he'] at hh
        exact hh.symm
      have hcount : ex.value.memory.count = (trueComponent I b key terminals a root).card :=
        hv.count_eq.trans hlen
      have hb := BandEvaluation.program_correct I ex.value.memory.points hv.points_nodup a rho tau hband
      have hs := hclass.mp hcomplete
      simp only [↓reduceIte]
      change (BandEvaluation.run I.weight ex.value.memory.points a rho tau).value /
        (3 * a * ex.value.memory.count) = _
      rw [hb, he', hcount]
      have hs' : (componentOn I (retainedSet b key terminals) a root).card ≤ B := by
        simpa only [trueComponent] using hs
      simp only [pointScore, trueComponent, hs', ↓reduceIte]

theorem frontendRun_positive (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q) :
    (frontendRun w b key a B terminals rho tau root c).positiveReplies ≤ B := by
  have he := ComponentExplore.result_positive w b key a B terminals root c
  have hb := BandEvaluation.run_resources w
    (ComponentExplore.result w b key a B terminals root c).value.memory.points a rho tau
  dsimp only [frontendRun, Outcome.combine, Outcome.add, Outcome.pure]
  split_ifs <;> simp only [hb.2, Nat.add_zero] <;> exact he

theorem frontendRun_queries (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct b c) :
    (frontendRun w b key a B terminals rho tau root c).metricQueries ≤
      (n + terminals.length) * (B + 1) := by
  have he := ComponentExplore.result_metric_queries w b key a B terminals root c
  have hb := BandEvaluation.run_queries w
    (ComponentExplore.result w b key a B terminals root c).value.memory.points a rho tau
  have hl := explore_length_le w b key a B terminals root c hc
  have hm := Nat.mul_le_mul_left n hl
  dsimp only [frontendRun, Outcome.combine, Outcome.add, Outcome.pure]
  split_ifs <;> nlinarith

theorem frontendRun_work (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct b c) :
    (frontendRun w b key a B terminals rho tau root c).work ≤
      20000000000 * (n + terminals.length + 1) * (B + 2) ^ 12 := by
  have he := ComponentExplore.result_work w b key a B terminals root c hc
  have hb := BandEvaluation.run_work w
    (ComponentExplore.result w b key a B terminals root c).value.memory.points a rho tau
  have hl := explore_length_le w b key a B terminals root c hc
  have hpow : (B + 2) ^ 2 ≤ (B + 2) ^ 12 := pow_le_pow_right₀ (by omega) (by omega)
  have hex : (terminals.length + 1) * (B + 2) ^ 2 ≤
      (n + terminals.length + 1) * (B + 2) ^ 12 := by gcongr; omega
  have hbx : (n + 1) *
      ((ComponentExplore.result w b key a B terminals root c).value.memory.points.length + 1) ^ 12 ≤
      (n + terminals.length + 1) * (B + 2) ^ 12 := by
    apply Nat.mul_le_mul (by omega)
    exact Nat.pow_le_pow_left (by omega) 12
  have hp : 1 ≤ (n + terminals.length + 1) * (B + 2) ^ 12 := by
    have hh : 0 < (n + terminals.length + 1) * (B + 2) ^ 12 := by positivity
    omega
  dsimp only [frontendRun, Outcome.combine, Outcome.add, Outcome.pure]
  have he' : (ComponentExplore.result w b key a B terminals root c).work ≤
      64 * ((n + terminals.length + 1) * (B + 2) ^ 12) := by
    exact he.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 64 hex)
  have hb' : (BandEvaluation.run w
      (ComponentExplore.result w b key a B terminals root c).value.memory.points a rho tau).work ≤
      10000000000 * ((n + terminals.length + 1) * (B + 2) ^ 12) := by
    exact hb.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 10000000000 hbx)
  simp only [Nat.mul_assoc]
  split_ifs <;> dsimp only <;> omega

end SteinerUpperBound.BandEvaluation
