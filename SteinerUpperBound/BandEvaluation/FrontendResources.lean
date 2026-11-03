module

public import SteinerUpperBound.BandEvaluation.Guarded

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

open QueryProgram Covers.OracleProgram
open scoped Classical

variable {Q : Type*} {n : ℕ}

theorem frontend_compiled_outcome (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q)
    (seed : ((frontend key a B terminals rho tau root c).compile w).Seed) :
    (((frontend key a B terminals rho tau root c).compile w).tree seed).output b =
      frontendRun w b key a B terminals rho tau root c :=
  runs_eq_of_evaluates w b _ (frontend_noRandom _ _ _ _ _ _ _ _) _
    (frontend_evaluates _ _ _ _ _ _ _ _ _ _) _
    (runs_compile w b (frontend key a B terminals rho tau root c) seed)

theorem guarded_compiled_outcome (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q)
    (seed : ((guardedCallback key a B terminals rho tau root c).compile w).Seed) :
    (((guardedCallback key a B terminals rho tau root c).compile w).tree seed).output b =
      guardedRun w b key a B terminals rho tau root c :=
  runs_eq_of_evaluates w b _ (guarded_noRandom _ _ _ _ _ _ _ _) _
    (guarded_evaluates _ _ _ _ _ _ _ _ _ _) _
    (runs_compile w b (guardedCallback key a B terminals rho tau root c) seed)

theorem frontend_compiled_spec (I : Instance (Fin n)) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct b c) (hr : root ∈ retainedSet b key terminals)
    (ha : 0 < a) (hrho : 0 ≤ rho) (htau : 0 ≤ tau) (hband : tau * a ≤ a - 2 * rho)
    (seed : ((frontend key a B terminals rho tau root c).compile I.weight).Seed) :
    let o := (((frontend key a B terminals rho tau root c).compile I.weight).tree seed).output b
    o.value.1 = pointScore I (retainedSet b key terminals) a rho tau B root ∧
      Cache.Correct b o.value.2 ∧ 0 ≤ o.value.1 ∧ o.value.1 ≤ 1 ∧
      o.metricQueries ≤ (n + terminals.length) * (B + 1) ∧
      o.work ≤ 20000000000 * (n + terminals.length + 1) * (B + 2) ^ 12 ∧
      o.positiveReplies ≤ B := by
  dsimp only
  rw [frontend_compiled_outcome]
  have he := frontendRun_correct I b key a B terminals rho tau root c hc hr hband
  have hb := pointScore_bounds I (retainedSet b key terminals) a rho tau B ha hrho htau hband root
  refine ⟨he, frontendRun_cache_correct _ _ _ _ _ _ _ _ _ _ hc, ?_, ?_,
    frontendRun_queries _ _ _ _ _ _ _ _ _ _ hc, frontendRun_work _ _ _ _ _ _ _ _ _ _ hc,
    frontendRun_positive _ _ _ _ _ _ _ _ _ _⟩
  · simpa only [he] using hb.1
  · simpa only [he] using hb.2

theorem guarded_compiled_resources (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct b c)
    (seed : ((guardedCallback key a B terminals rho tau root c).compile w).Seed) :
    let o := (((guardedCallback key a B terminals rho tau root c).compile w).tree seed).output b
    Cache.Correct b o.value.2 ∧ o.metricQueries ≤ (n + terminals.length) * (B + 1) ∧
      o.work ≤ 40000000000 * (n + terminals.length + 1) * (B + 2) ^ 12 ∧ o.positiveReplies ≤ B + 1 := by
  dsimp only
  rw [guarded_compiled_outcome]
  exact ⟨guarded_cache_correct _ _ _ _ _ _ _ _ _ _ hc,
    guarded_queries _ _ _ _ _ _ _ _ _ _ hc, guarded_work _ _ _ _ _ _ _ _ _ _ hc,
    guarded_positive _ _ _ _ _ _ _ _ _ _⟩

theorem guarded_compiled_positive_cached (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) (root : Fin n) (c : Cache Q)
    (hc : c (key root) = some true)
    (seed : ((guardedCallback key a B terminals rho tau root c).compile w).Seed) :
    ((((guardedCallback key a B terminals rho tau root c).compile w).tree seed).output b).positiveReplies ≤ B := by
  rw [guarded_compiled_outcome]
  exact guarded_positive_cached _ _ _ _ _ _ _ _ _ _ hc

theorem terminals_length (terminals : List (Fin n)) (h : terminals.Nodup) : terminals.length ≤ n := by
  have hh := Finset.card_le_univ terminals.toFinset
  simpa only [List.toFinset_card_of_nodup h, Fintype.card_fin] using hh

theorem frontendRun_work_nodup (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (key : Fin n → Q)
    (a : ℝ) (B : ℕ) (terminals : List (Fin n)) (hl : terminals.Nodup) (rho tau : ℝ)
    (root : Fin n) (c : Cache Q) (hc : Cache.Correct b c) :
    (frontendRun w b key a B terminals rho tau root c).work ≤ 80000000000 * n * (B + 2) ^ 12 := by
  have he := frontendRun_work w b key a B terminals rho tau root c hc
  have hl' := terminals_length terminals hl
  have hn := root.isLt
  have hcoef : n + terminals.length + 1 ≤ 4 * n := by omega
  calc
    _ ≤ 20000000000 * (n + terminals.length + 1) * (B + 2) ^ 12 := he
    _ ≤ 20000000000 * (4 * n) * (B + 2) ^ 12 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcoef)
    _ = _ := by ring

end SteinerUpperBound.BandEvaluation
