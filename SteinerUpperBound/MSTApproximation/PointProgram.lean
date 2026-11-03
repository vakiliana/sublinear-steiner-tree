module

public import SteinerUpperBound.MSTApproximation.Score
public import SteinerUpperBound.ComponentExplore

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry QueryProgram
open scoped Classical BigOperators

variable {V Q : Type*} [Fintype V]

structure PointAnswer (Q : Type*) where
  score : ℝ
  cache : Cache Q

noncomputable def answerScore (r : ComponentExplore.Answer V Q) : ℝ :=
  if r.complete then 1 / (r.memory.points.length : ℝ) else 0

noncomputable def pointProgram (key : V → Q) (a : ℝ) (B : ℕ) (l : List V)
    (root : V) (cache : Cache Q) : Code (Sym2 V) Q (PointAnswer Q) :=
  .tick (B + 7) ((ComponentExplore.program key a B l root cache).map
    (fun r => ⟨answerScore r, r.memory.cache⟩))

noncomputable abbrev pointResult (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V) (cache : Cache Q) : Outcome (PointAnswer Q) :=
  ((ComponentExplore.result w b key a B l root cache).map
    (fun r => ⟨answerScore r, r.memory.cache⟩)).add (B + 8) 0 0 0

theorem pointProgram_evaluates (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V) (cache : Cache Q) :
    Code.Evaluates w b (pointProgram key a B l root cache)
      (pointResult w b key a B l root cache) := by
  intro F
  simp only [pointProgram, Code.evaluate, Code.evaluate_map]
  rw [ComponentExplore.program_evaluates]

theorem explored_component_eq (I : Instance V) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (T : Finset V) {root : V} (hroot : root ∈ ComponentExplore.retained b key T) :
    ComponentExplore.component (ComponentExplore.retainedGraph I.weight b key T a) root =
      componentOn I (ComponentExplore.retained b key T) a root := by
  ext x
  simp only [ComponentExplore.component, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_componentOn]
  have he : ComponentExplore.retainedGraph I.weight b key T a =
      thresholdOn I (ComponentExplore.retained b key T) a :=
    below_eq_thresholdOn I _ a
  constructor
  · intro hx
    exact ⟨ComponentExplore.reachable_retained I.weight b key T a hroot hx, he ▸ hx⟩
  · intro hx
    exact he ▸ hx.2

theorem pointResult_correct (I : Instance V) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V) (cache : Cache Q)
    (hc : Cache.Correct b cache) (hroot : root ∈ ComponentExplore.retained b key l.toFinset) :
    (pointResult I.weight b key a B l root cache).value.score =
      pointScore I (ComponentExplore.retained b key l.toFinset) a B ⟨root, hroot⟩ := by
  let o := ComponentExplore.result I.weight b key a B l root cache
  let C := componentOn I (ComponentExplore.retained b key l.toFinset) a root
  have hv := ComponentExplore.result_valid I.weight b key a B l root cache hc
  have hr := ComponentExplore.result_correct I.weight b key a B l root cache hc hroot
  change (∀ y ∈ o.value.memory.points.toFinset,
      (ComponentExplore.retainedGraph I.weight b key l.toFinset a).Reachable root y) ∧
    (if o.value.complete then
      o.value.memory.points.toFinset =
        ComponentExplore.component (ComponentExplore.retainedGraph I.weight b key l.toFinset a) root ∧
        o.value.memory.points.toFinset.card ≤ B
      else o.value.memory.points.toFinset.card = B + 1) at hr
  have hcard : o.value.memory.points.toFinset.card = o.value.memory.points.length :=
    List.toFinset_card_of_nodup hv.points_nodup
  have he : ComponentExplore.component (ComponentExplore.retainedGraph I.weight b key l.toFinset a)
      root = C := explored_component_eq I b key a l.toFinset hroot
  change answerScore o.value = if C.card ≤ B then 1 / (C.card : ℝ) else 0
  cases hcomplete : o.value.complete with
  | true =>
    have hs := hr.2
    rw [hcomplete, if_pos rfl, he] at hs
    have hsmall : C.card ≤ B := hs.1 ▸ hs.2
    unfold answerScore
    rw [hcomplete, if_pos rfl, if_pos hsmall, ← hcard, hs.1]
  | false =>
    have hs := hr.2
    rw [hcomplete, if_neg Bool.false_ne_true] at hs
    have hsub : o.value.memory.points.toFinset ⊆ C := by
      intro x hx
      rw [← he]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.1 x hx⟩
    have hlarge : B < C.card := by
      have h := Finset.card_le_card hsub
      omega
    simp only [answerScore, hcomplete, Bool.false_eq_true, ite_false, not_le.mpr hlarge]

theorem pointResult_cache (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V) (cache : Cache Q) (hc : Cache.Correct b cache) :
    Cache.Correct b (pointResult w b key a B l root cache).value.cache :=
  (ComponentExplore.result_valid w b key a B l root cache hc).cache_correct

theorem pointResult_metric_queries (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V) (cache : Cache Q) :
    (pointResult w b key a B l root cache).metricQueries ≤ (B + 1) * l.length := by
  simpa only [pointResult, Outcome.map, Outcome.add, Nat.zero_add] using
    ComponentExplore.result_metric_queries w b key a B l root cache

theorem pointResult_positive (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V) (cache : Cache Q) :
    (pointResult w b key a B l root cache).positiveReplies ≤ B := by
  simpa only [pointResult, Outcome.map, Outcome.add, Nat.zero_add] using
    ComponentExplore.result_positive w b key a B l root cache

theorem pointResult_work (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V) (cache : Cache Q) (hc : Cache.Correct b cache) :
    (pointResult w b key a B l root cache).work ≤ 80 * (l.length + 1) * (B + 2) ^ 2 := by
  have h := ComponentExplore.result_work w b key a B l root cache hc
  change B + 8 + (ComponentExplore.result w b key a B l root cache).work ≤ _
  nlinarith [Nat.zero_le (l.length * B ^ 2), Nat.zero_le (l.length * B)]

end SteinerUpperBound.MSTApproximation
