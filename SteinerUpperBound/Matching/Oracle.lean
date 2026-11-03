module

public import SteinerUpperBound.Matching.Semantics

@[expose] public section

/-!
# The memoized local matching oracle

The cache is fresh for each vertex request. Every invocation, including a cache
hit, is recorded. Ancestors are stored in reverse order, with the immediate
caller first. A cache miss scans the lower-ranked incident copies in increasing
order; no recursive call is made after the first positive answer.
-/

namespace SteinerUpperBound.Matching

open scoped Classical BigOperators

namespace Graph

abbrev Memo (E : Type*) := Directed E → Option Bool

structure Invocation (E : Type*) where
  state : Directed E
  ancestors : List (Directed E)
  cached : Bool

structure Run (E A : Type*) where
  value : A
  memo : Memo E
  calls : List (Invocation E)

namespace Run

variable {E A : Type*}

/-- Stateful short-circuiting search, concatenating the actual invocation logs. -/
noncomputable def scan (call : A → Memo E → Run E Bool) :
    List A → Memo E → Run E (Option A)
  | [], μ => ⟨none, μ, []⟩
  | a :: xs, μ =>
    let r := call a μ
    if r.value then ⟨some a, r.memo, r.calls⟩ else
      let s := scan call xs r.memo
      ⟨s.value, s.memo, r.calls ++ s.calls⟩

theorem scan_spec (call : A → Memo E → Run E Bool) (good : A → Bool)
    (I : Memo E → Prop) (xs : List A)
    (hcall : ∀ a ∈ xs, ∀ μ, I μ →
      (call a μ).value = good a ∧ I (call a μ).memo)
    (μ : Memo E) (hμ : I μ) :
    (scan call xs μ).value = xs.find? good ∧ I (scan call xs μ).memo := by
  induction xs generalizing μ with
  | nil => exact ⟨rfl, hμ⟩
  | cons a xs ih =>
    obtain ⟨ha, hi⟩ := hcall a (by simp) μ hμ
    have hs := ih (fun b hb => hcall b (by simp [hb])) (call a μ).memo hi
    simp only [scan]
    split_ifs with h
    · have hg : good a = true := ha ▸ h
      simp only [List.find?_cons, hg]
      exact ⟨trivial, hi⟩
    · have hg : good a = false := Bool.eq_false_iff.mpr (ha ▸ h)
      simp only [List.find?_cons, hg]
      exact hs

end Run

variable {V E : Type*} [Fintype E]

/-- The recursive evaluator. Termination is by the rank of the queried copy. -/
noncomputable def runEO (G : Graph V E) (ρ : Rank E)
    (d : Directed E) (ancestors : List (Directed E)) (μ : Memo E) : Run E Bool :=
  match μ d with
  | some b => ⟨b, μ, [⟨d, ancestors, true⟩]⟩
  | none =>
    let r := Run.scan
      (fun f ν =>
        if _h : ρ.index f < ρ.index d.1 then
          runEO G ρ (G.away (G.head d) f) (d :: ancestors) ν
        else ⟨false, ν, []⟩)
      (G.candidates ρ (ρ.index d.1) (G.head d)) μ
    let b := r.value.isNone
    ⟨b, Function.update r.memo d (some b), ⟨d, ancestors, false⟩ :: r.calls⟩
termination_by ρ.index d.1
decreasing_by simpa using _h

variable (G : Graph V E) (ρ : Rank E)

def MemoSound (μ : Memo E) : Prop :=
  ∀ d b, μ d = some b → b = G.freeBefore ρ d

theorem empty_memo_sound : G.MemoSound ρ (fun _ => none) := by
  intro d b h
  cases h

theorem memo_sound_update {μ : Memo E} (hμ : G.MemoSound ρ μ) (d : Directed E) :
    G.MemoSound ρ (Function.update μ d (some (G.freeBefore ρ d))) := by
  classical
  intro d' b hb
  by_cases hd : d' = d
  · subst d'
    simpa using hb.symm
  · exact hμ d' b (by simpa [Function.update_of_ne hd] using hb)

theorem runEO_spec (G : Graph V E) (ρ : Rank E)
    (d : Directed E) (ancestors : List (Directed E))
    (μ : Memo E) (hμ : G.MemoSound ρ μ) :
    (G.runEO ρ d ancestors μ).value = G.freeBefore ρ d ∧
      G.MemoSound ρ (G.runEO ρ d ancestors μ).memo := by
  classical
  rw [runEO]
  cases hc : μ d with
  | some b => exact ⟨hμ d b hc, hμ⟩
  | none =>
    let call : E → Memo E → Run E Bool := fun f ν =>
      if h : ρ.index f < ρ.index d.1 then
        G.runEO ρ (G.away (G.head d) f) (d :: ancestors) ν
      else ⟨false, ν, []⟩
    have hs := Run.scan_spec call (fun f => G.freeBefore ρ (G.away (G.head d) f))
      (G.MemoSound ρ) (G.candidates ρ (ρ.index d.1) (G.head d))
      (fun f hf ν hν => by
        have hr := ((G.mem_candidates ρ _ _ f).mp hf).1
        dsimp only [call]
        simp only [hr, ↓reduceDIte]
        exact runEO_spec G ρ (G.away (G.head d) f) (d :: ancestors) ν hν) μ hμ
    have hv : (Run.scan call (G.candidates ρ (ρ.index d.1) (G.head d)) μ).value.isNone =
        G.freeBefore ρ d := by
      apply Bool.eq_iff_iff.mpr
      rw [Option.isNone_iff_eq_none, hs.1]
      exact (G.localFirst_eq_none ρ (ρ.index d.1) (G.head d)).trans (by
        simp only [freeBefore, decide_eq_true_eq])
    change (Run.scan call _ μ).value.isNone = G.freeBefore ρ d ∧
      G.MemoSound ρ (Function.update (Run.scan call _ μ).memo d
        (some (Run.scan call _ μ).value.isNone))
    rw [hv]
    exact ⟨rfl, G.memo_sound_update ρ hs.2 d⟩
termination_by ρ.index d.1
decreasing_by simpa using hr

/-- A standalone directed query, with its own empty cache. -/
noncomputable def edgeOracle (d : Directed E) : Run E Bool :=
  G.runEO ρ d [] (fun _ => none)

/-- A vertex request: the returned identifier is the first accepted copy, or none. -/
noncomputable def vertexOracle (v : V) : Run E (Option E) :=
  Run.scan (fun e μ => G.runEO ρ (G.away v e) [] μ)
    (G.candidates ρ (Fintype.card E) v) (fun _ => none)

theorem edgeOracle_correct (d : Directed E) :
    (G.edgeOracle ρ d).value = G.freeBefore ρ d :=
  (G.runEO_spec ρ d [] _ (G.empty_memo_sound ρ)).1

theorem vertexOracle_correct (v : V) :
    (G.vertexOracle ρ v).value = G.greedyMate ρ (Fintype.card E) v := by
  have hs := Run.scan_spec (fun e μ => G.runEO ρ (G.away v e) [] μ)
    (fun e => G.freeBefore ρ (G.away v e)) (G.MemoSound ρ)
    (G.candidates ρ (Fintype.card E) v)
    (fun e _ μ hμ => G.runEO_spec ρ (G.away v e) [] μ hμ)
    (fun _ => none) (G.empty_memo_sound ρ)
  exact hs.1.trans (G.localFirst_eq_greedyMate ρ _ v)

theorem vertexOracle_eq_none (v : V) :
    (G.vertexOracle ρ v).value = none ↔ G.Free (G.greedy ρ) v := by
  rw [G.vertexOracle_correct ρ v, G.greedyMate_eq_none]
  rfl

theorem vertexOracle_eq_some {v : V} {e : E}
    (h : (G.vertexOracle ρ v).value = some e) :
    e ∈ G.greedy ρ ∧ G.Incident e v := by
  rw [G.vertexOracle_correct ρ v] at h
  obtain ⟨he, _, hi⟩ := G.greedyMate_eq_some ρ h
  exact ⟨he, hi⟩

theorem vertexOracle_eq_some_iff (v : V) (e : E) :
    (G.vertexOracle ρ v).value = some e ↔ e ∈ G.greedy ρ ∧ G.Incident e v := by
  constructor
  · exact G.vertexOracle_eq_some ρ
  · rintro ⟨he, hi⟩
    cases hv : (G.vertexOracle ρ v).value with
    | none => exact ((G.vertexOracle_eq_none ρ v).mp hv e he hi).elim
    | some f =>
      obtain ⟨hf, hfi⟩ := G.vertexOracle_eq_some ρ hv
      have hfe := G.greedy_isMatching ρ f hf e he ⟨v, hfi, hi⟩
      simp [hfe]

end Graph

end SteinerUpperBound.Matching
