module

public import SteinerUpperBound.MSTApproximation.PointProgram
public import SteinerUpperBound.MSTApproximation.SamplingLaw

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry QueryProgram
open scoped Classical BigOperators

variable {V Q : Type*} [Fintype V]

structure ScoresAnswer (Q : Type*) where
  total : ℝ
  cache : Cache Q

noncomputable def scoresProgram (key : V → Q) (a : ℝ) (B : ℕ) (l : List V) :
    List V → Cache Q → Code (Sym2 V) Q (ScoresAnswer Q)
  | [], cache => .tick 1 (.pure ⟨0, cache⟩)
  | root :: roots, cache =>
      (pointProgram key a B l root cache).bind (fun r =>
        .tick 3 ((scoresProgram key a B l roots r.cache).map
          (fun t => ⟨r.score + t.total, t.cache⟩)))

noncomputable def scoresResult (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) : List V → Cache Q → Outcome (ScoresAnswer Q)
  | [], cache => ⟨⟨0, cache⟩, 2, 0, 0, 0⟩
  | root :: roots, cache =>
      let r := pointResult w b key a B l root cache
      r.combine (((scoresResult w b key a B l roots r.value.cache).map
        (fun t => ⟨r.value.score + t.total, t.cache⟩)).add 4 0 0 0)

theorem scoresProgram_evaluates (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l roots : List V) (cache : Cache Q) :
    Code.Evaluates w b (scoresProgram key a B l roots cache)
      (scoresResult w b key a B l roots cache) := by
  induction roots generalizing cache with
  | nil => intro F; rfl
  | cons root roots ih =>
    intro F
    rw [scoresProgram, Code.evaluate_bind, pointProgram_evaluates]
    simp only [Code.evaluate, Code.evaluate_map]
    rw [ih]
    rfl

theorem scoresResult_cache (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l roots : List V) (cache : Cache Q) (hc : Cache.Correct b cache) :
    Cache.Correct b (scoresResult w b key a B l roots cache).value.cache := by
  induction roots generalizing cache with
  | nil => exact hc
  | cons root roots ih =>
    exact ih _ (pointResult_cache w b key a B l root cache hc)

theorem scoresResult_correct (I : Instance V) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l roots : List V) (cache : Cache Q) (hc : Cache.Correct b cache)
    (hroots : ∀ x ∈ roots, x ∈ ComponentExplore.retained b key l.toFinset) :
    (scoresResult I.weight b key a B l roots cache).value.total =
      (roots.map (scoreOn I (ComponentExplore.retained b key l.toFinset) a B)).sum := by
  induction roots generalizing cache with
  | nil => rfl
  | cons root roots ih =>
    have hroot := hroots root List.mem_cons_self
    have hp := pointResult_correct I b key a B l root cache hc hroot
    have ht := ih _ (pointResult_cache I.weight b key a B l root cache hc)
      (fun x hx => hroots x (List.mem_cons_of_mem _ hx))
    change (pointResult I.weight b key a B l root cache).value.score +
      (scoresResult I.weight b key a B l roots
        (pointResult I.weight b key a B l root cache).value.cache).value.total = _
    rw [ht, hp, ← scoreOn_mem I _ a B hroot]
    rfl

theorem scoresResult_resources (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l roots : List V) (cache : Cache Q) (hc : Cache.Correct b cache) :
    (scoresResult w b key a B l roots cache).metricQueries ≤ (B + 1) * l.length * roots.length ∧
      (scoresResult w b key a B l roots cache).positiveReplies ≤ B * roots.length ∧
      (scoresResult w b key a B l roots cache).work ≤
        (80 * (l.length + 1) * (B + 2) ^ 2 + 4) * roots.length + 2 := by
  induction roots generalizing cache with
  | nil => simp only [scoresResult, List.length_nil, Nat.mul_zero, le_refl, and_self]
  | cons root roots ih =>
    obtain ⟨hm, hp, hw⟩ := ih _ (pointResult_cache w b key a B l root cache hc)
    have hm0 := pointResult_metric_queries w b key a B l root cache
    have hp0 := pointResult_positive w b key a B l root cache
    have hw0 := pointResult_work w b key a B l root cache hc
    change (pointResult w b key a B l root cache).metricQueries +
        (0 + (scoresResult w b key a B l roots
          (pointResult w b key a B l root cache).value.cache).metricQueries) ≤ _ ∧
      (pointResult w b key a B l root cache).positiveReplies +
        (0 + (scoresResult w b key a B l roots
          (pointResult w b key a B l root cache).value.cache).positiveReplies) ≤ _ ∧
      (pointResult w b key a B l root cache).work +
        (4 + (scoresResult w b key a B l roots
          (pointResult w b key a B l root cache).value.cache).work) ≤ _
    simp only [List.length_cons, Nat.zero_add]
    constructor
    · nlinarith
    constructor <;> nlinarith

end SteinerUpperBound.MSTApproximation
