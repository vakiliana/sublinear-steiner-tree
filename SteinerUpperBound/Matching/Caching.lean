module

public import SteinerUpperBound.Matching.Trace

@[expose] public section

namespace SteinerUpperBound.Matching

open scoped Classical BigOperators

namespace Graph

variable {E : Type*}

def misses (cs : List (Invocation E)) : List (Directed E) :=
  (cs.filter fun c => !c.cached).map Invocation.state

@[simp] theorem misses_nil : misses ([] : List (Invocation E)) = [] := rfl

@[simp] theorem misses_append (xs ys : List (Invocation E)) :
    misses (xs ++ ys) = misses xs ++ misses ys := by simp [misses]

def MemoExtends (μ ν : Memo E) : Prop :=
  ∀ d b, μ d = some b → ν d = some b

theorem MemoExtends.refl (μ : Memo E) : MemoExtends μ μ := fun _ _ h => h

theorem MemoExtends.trans {μ ν ξ : Memo E} (h : MemoExtends μ ν) (h' : MemoExtends ν ξ) :
    MemoExtends μ ξ := fun d b hd => h' d b (h d b hd)

theorem MemoExtends.present {μ ν : Memo E} (h : MemoExtends μ ν) (d : Directed E)
    (hd : μ d ≠ none) : ν d ≠ none := by
  cases he : μ d with
  | none => exact (hd he).elim
  | some b => rw [h d b he]; simp

structure CacheJournal (μ ν : Memo E) (cs : List (Invocation E)) : Prop where
  extends_memo : MemoExtends μ ν
  unique_misses : (misses cs).Nodup
  absent : ∀ d ∈ misses cs, μ d = none
  present : ∀ d ∈ misses cs, ν d ≠ none

theorem CacheJournal.empty (μ : Memo E) : CacheJournal μ μ [] :=
  ⟨MemoExtends.refl μ, by simp, by simp, by simp⟩

theorem CacheJournal.append {μ ν ξ : Memo E} {xs ys : List (Invocation E)}
    (h : CacheJournal μ ν xs) (h' : CacheJournal ν ξ ys) :
    CacheJournal μ ξ (xs ++ ys) := by
  refine ⟨h.extends_memo.trans h'.extends_memo, ?_, ?_, ?_⟩
  · rw [misses_append, List.nodup_append]
    refine ⟨h.unique_misses, h'.unique_misses, ?_⟩
    intro a ha b hb heq
    subst b
    exact h.present a ha (h'.absent a hb)
  · rw [misses_append]
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact h.absent d hd
    · cases he : μ d with
      | none => rfl
      | some b =>
        have hn := h.extends_memo d b he
        rw [h'.absent d hd] at hn
        cases hn
  · rw [misses_append]
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact h'.extends_memo.present d (h.present d hd)
    · exact h'.present d hd

namespace Run

variable {A : Type*}

theorem scan_cacheJournal (call : A → Memo E → Run E Bool) (xs : List A)
    (hcall : ∀ a ∈ xs, ∀ μ, CacheJournal μ (call a μ).memo (call a μ).calls)
    (μ : Memo E) : CacheJournal μ (scan call xs μ).memo (scan call xs μ).calls := by
  induction xs generalizing μ with
  | nil => exact CacheJournal.empty μ
  | cons a xs ih =>
    have ha := hcall a (by simp) μ
    have ht := ih (fun b hb => hcall b (by simp [hb])) (call a μ).memo
    simp only [scan]
    split_ifs
    · exact ha
    · exact ha.append ht

end Run

variable {V : Type*} [Fintype E]

theorem runEO_rank_le (G : Graph V E) (ρ : Rank E)
    (d : Directed E) (ancestors : List (Directed E)) (μ : Memo E) :
    ∀ c ∈ (G.runEO ρ d ancestors μ).calls, ρ.index c.state.1 ≤ ρ.index d.1 := by
  classical
  rw [runEO]
  cases hc : μ d with
  | some b =>
    intro c h
    have heq : c = ⟨d, ancestors, true⟩ := by simpa using h
    simp [heq]
  | none =>
    let call : E → Memo E → Run E Bool := fun f ν =>
      if h : ρ.index f < ρ.index d.1 then
        G.runEO ρ (G.away (G.head d) f) (d :: ancestors) ν
      else ⟨false, ν, []⟩
    have hs := Run.scan_all_calls call (G.candidates ρ (ρ.index d.1) (G.head d))
      (fun c => ρ.index c.state.1 ≤ ρ.index d.1)
      (fun f hf ν c hc => by
        have hr := ((G.mem_candidates ρ _ _ f).mp hf).1
        dsimp only [call] at hc
        simp only [hr, ↓reduceDIte] at hc
        exact (runEO_rank_le G ρ (G.away (G.head d) f) (d :: ancestors) ν c hc).trans
          hr.le) μ
    change ∀ c ∈ (⟨d, ancestors, false⟩ :: (Run.scan call _ μ).calls),
      ρ.index c.state.1 ≤ ρ.index d.1
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact le_refl _
    · exact hs c hc
termination_by ρ.index d.1
decreasing_by simpa using hr

theorem runEO_cacheJournal (G : Graph V E) (ρ : Rank E)
    (d : Directed E) (ancestors : List (Directed E)) (μ : Memo E) :
    CacheJournal μ (G.runEO ρ d ancestors μ).memo (G.runEO ρ d ancestors μ).calls := by
  classical
  rw [runEO]
  cases hc : μ d with
  | some b =>
    exact ⟨MemoExtends.refl μ, by simp [misses], by simp [misses], by simp [misses]⟩
  | none =>
    let call : E → Memo E → Run E Bool := fun f ν =>
      if h : ρ.index f < ρ.index d.1 then
        G.runEO ρ (G.away (G.head d) f) (d :: ancestors) ν
      else ⟨false, ν, []⟩
    let r := Run.scan call (G.candidates ρ (ρ.index d.1) (G.head d)) μ
    have hj : CacheJournal μ r.memo r.calls := by
      apply Run.scan_cacheJournal
      intro f hf ν
      have hr := ((G.mem_candidates ρ _ _ f).mp hf).1
      dsimp only [call]
      simp only [hr, ↓reduceDIte]
      exact runEO_cacheJournal G ρ (G.away (G.head d) f) (d :: ancestors) ν
    have hrank : ∀ c ∈ r.calls, ρ.index c.state.1 < ρ.index d.1 := by
      apply Run.scan_all_calls call _ (fun c => ρ.index c.state.1 < ρ.index d.1)
      intro f hf ν c hc
      have hr := ((G.mem_candidates ρ _ _ f).mp hf).1
      dsimp only [call] at hc
      simp only [hr, ↓reduceDIte] at hc
      exact (G.runEO_rank_le ρ _ _ ν c hc).trans_lt hr
    have hnot : d ∉ misses r.calls := by
      intro hd
      obtain ⟨c, hc, heq⟩ := List.mem_map.mp hd
      have hc' : c ∈ r.calls := (List.mem_filter.mp hc).1
      have hlt := hrank c hc'
      simp only [heq, lt_self_iff_false] at hlt
    change CacheJournal μ (Function.update r.memo d (some r.value.isNone))
      (⟨d, ancestors, false⟩ :: r.calls)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s b hs
      have hsd : s ≠ d := by
        intro heq
        subst s
        rw [hc] at hs
        cases hs
      rw [Function.update_of_ne hsd]
      exact hj.extends_memo s b hs
    · simpa [misses] using List.nodup_cons.mpr ⟨hnot, hj.unique_misses⟩
    · simp only [misses, List.filter_cons, Bool.not_false,
        ↓reduceIte, List.map_cons]
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hc
      · exact hj.absent s hs
    · simp only [misses, List.filter_cons, Bool.not_false,
        ↓reduceIte, List.map_cons]
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · simp
      · have hsd : s ≠ d := fun heq => hnot (heq ▸ hs)
        rw [Function.update_of_ne hsd]
        exact hj.present s hs
termination_by ρ.index d.1
decreasing_by simpa using hr

variable (G : Graph V E) (ρ : Rank E)

theorem vertexOracle_cacheJournal (v : V) :
    CacheJournal (fun _ => none) (G.vertexOracle ρ v).memo (G.vertexOracle ρ v).calls :=
  Run.scan_cacheJournal _ _ (fun _ _ μ => G.runEO_cacheJournal ρ _ [] μ) _

theorem vertexOracle_misses_nodup (v : V) :
    (misses (G.vertexOracle ρ v).calls).Nodup :=
  (G.vertexOracle_cacheJournal ρ v).unique_misses

theorem vertexOracle_misses_le (v : V) :
    (misses (G.vertexOracle ρ v).calls).length ≤ 2 * Fintype.card E := by
  have h := (G.vertexOracle_misses_nodup ρ v).length_le_card
  simpa only [Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using h

end Graph

end SteinerUpperBound.Matching
