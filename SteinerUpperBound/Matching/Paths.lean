module

public import SteinerUpperBound.Matching.DegreeShrink

@[expose] public section

namespace SteinerUpperBound.Matching

open scoped Classical BigOperators

namespace Graph

namespace Run

variable {E A : Type*}

theorem scan_calls_property (call : A → Memo E → Run E Bool) (good : A → Bool)
    (I : Memo E → Prop) (P : Invocation E → Prop) (xs : List A)
    (hspec : ∀ a ∈ xs, ∀ μ, I μ →
      (call a μ).value = good a ∧ I (call a μ).memo)
    (hcalls : ∀ pre a post, xs = pre ++ a :: post → pre.find? good = none →
      ∀ μ, I μ → ∀ c ∈ (call a μ).calls, P c)
    (μ : Memo E) (hμ : I μ) :
    ∀ c ∈ (scan call xs μ).calls, P c := by
  induction xs generalizing μ with
  | nil => simp [scan]
  | cons a xs ih =>
    obtain ⟨ha, hi⟩ := hspec a (by simp) μ hμ
    have hca := hcalls [] a xs rfl rfl μ hμ
    simp only [scan]
    split_ifs with h
    · exact hca
    · have hga : good a = false := Bool.eq_false_iff.mpr (ha ▸ h)
      have htail := ih (fun b hb => hspec b (by simp [hb]))
        (fun pre b post heq hn ν hν =>
          hcalls (a :: pre) b post (by simpa using congrArg (List.cons a) heq)
            (by simpa only [List.find?_cons, hga] using hn) ν hν)
        (call a μ).memo hi
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hca c hc
      · exact htail c hc

end Run

variable {V E : Type*} [Fintype E]
variable (G : Graph V E) (ρ : Rank E)

/-- Every state that is actually reached has a free tail at its own rank. -/
def TailFree (d : Directed E) : Prop :=
  G.Free (G.greedyPrefix ρ (ρ.index d.1)) (G.tail d)

theorem reached_tail_free (k : ℕ) (v : V) (pre : List E) (f : E) (post : List E)
    (hxs : G.candidates ρ k v = pre ++ f :: post)
    (hn : pre.find? (fun e => G.freeBefore ρ (G.away v e)) = none) :
    G.TailFree ρ (G.away v f) := by
  have hmem : f ∈ G.candidates ρ k v := by rw [hxs]; simp
  obtain ⟨hrf, hif⟩ := (G.mem_candidates ρ k v f).mp hmem
  have hsort := G.candidates_pairwise ρ k v
  rw [hxs, List.pairwise_append] at hsort
  have hpost := (List.pairwise_cons.mp hsort.2.1).1
  unfold TailFree
  rw [away_edge, G.tail_away hif]
  intro g hg hig
  obtain ⟨hrg, hag⟩ := (G.mem_greedyPrefix ρ (ρ.index f) g).mp hg
  have hgmem : g ∈ G.candidates ρ k v :=
    (G.mem_candidates ρ k v g).mpr ⟨hrg.trans hrf, hig⟩
  rw [hxs, List.mem_append, List.mem_cons] at hgmem
  have hgpre : g ∈ pre := by
    rcases hgmem with h | h | h
    · exact h
    · subst g
      omega
    · have hlt := hpost g h
      omega
  have hgtrue : G.freeBefore ρ (G.away v g) = true := by
    simp only [freeBefore, decide_eq_true_eq]
    exact G.accepted_free_head ρ (G.away v g) hag
  exact (List.find?_eq_none.mp hn g hgpre) hgtrue

def StackStep (child parent : Directed E) : Prop :=
  ρ.index child.1 < ρ.index parent.1 ∧ G.tail child = G.head parent

/-- A reverse stack, starting with the currently invoked directed state. -/
def ValidStack (ds : List (Directed E)) : Prop :=
  (∀ d ∈ ds, G.TailFree ρ d) ∧ ds.IsChain (G.StackStep ρ)

theorem validStack_singleton (d : Directed E) (hd : G.TailFree ρ d) :
    G.ValidStack ρ [d] := by
  exact ⟨by simpa, by simp⟩

theorem validStack_cons (child parent : Directed E) (ancestors : List (Directed E))
    (hc : G.TailFree ρ child) (hp : G.ValidStack ρ (parent :: ancestors))
    (hstep : G.StackStep ρ child parent) :
    G.ValidStack ρ (child :: parent :: ancestors) := by
  refine ⟨?_, List.isChain_cons_cons.mpr ⟨hstep, hp.2⟩⟩
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact hc
  · exact hp.1 d hd

theorem runEO_validStack (G : Graph V E) (ρ : Rank E)
    (d : Directed E) (ancestors : List (Directed E)) (μ : Memo E)
    (hμ : G.MemoSound ρ μ) (hp : G.ValidStack ρ (d :: ancestors)) :
    ∀ c ∈ (G.runEO ρ d ancestors μ).calls,
      G.ValidStack ρ (c.state :: c.ancestors) := by
  classical
  rw [runEO]
  cases hc : μ d with
  | some b =>
    intro c h
    have heq : c = ⟨d, ancestors, true⟩ := by simpa using h
    simpa [heq] using hp
  | none =>
    let call : E → Memo E → Run E Bool := fun f ν =>
      if h : ρ.index f < ρ.index d.1 then
        G.runEO ρ (G.away (G.head d) f) (d :: ancestors) ν
      else ⟨false, ν, []⟩
    have hs := Run.scan_calls_property call
      (fun f => G.freeBefore ρ (G.away (G.head d) f))
      (G.MemoSound ρ) (fun c => G.ValidStack ρ (c.state :: c.ancestors))
      (G.candidates ρ (ρ.index d.1) (G.head d))
      (fun f hf ν hν => by
        have hr := ((G.mem_candidates ρ _ _ f).mp hf).1
        dsimp only [call]
        simp only [hr, ↓reduceDIte]
        exact G.runEO_spec ρ _ _ ν hν)
      (fun pre f post hxs hn ν hν => by
        have hmem : f ∈ G.candidates ρ (ρ.index d.1) (G.head d) := by rw [hxs]; simp
        obtain ⟨hr, hi⟩ := (G.mem_candidates ρ _ _ f).mp hmem
        have ht := G.reached_tail_free ρ _ _ pre f post hxs hn
        have hnew := G.validStack_cons ρ (G.away (G.head d) f) d ancestors ht hp
          ⟨hr, G.tail_away hi⟩
        dsimp only [call]
        simp only [hr, ↓reduceDIte]
        exact runEO_validStack G ρ (G.away (G.head d) f) (d :: ancestors) ν hν hnew)
      μ hμ
    change ∀ c ∈ (⟨d, ancestors, false⟩ :: (Run.scan call _ μ).calls),
      G.ValidStack ρ (c.state :: c.ancestors)
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hp
    · exact hs c hc
termination_by ρ.index d.1
decreasing_by simpa using hr

/-- This applies also to cached invocations; the trace never drops them. -/
theorem vertexOracle_validStack (v : V) :
    ∀ c ∈ (G.vertexOracle ρ v).calls,
      G.ValidStack ρ (c.state :: c.ancestors) := by
  apply Run.scan_calls_property (fun e μ => G.runEO ρ (G.away v e) [] μ)
    (fun e => G.freeBefore ρ (G.away v e)) (G.MemoSound ρ)
    (fun c => G.ValidStack ρ (c.state :: c.ancestors))
    (G.candidates ρ (Fintype.card E) v)
  · intro e _ μ hμ
    exact G.runEO_spec ρ _ _ μ hμ
  · intro pre e post hxs hn μ hμ
    have ht := G.reached_tail_free ρ _ v pre e post hxs hn
    exact G.runEO_validStack ρ (G.away v e) [] μ hμ (G.validStack_singleton ρ _ ht)
  · exact G.empty_memo_sound ρ

theorem vertexOracle_tailFree (v : V) (c : Invocation E)
    (hc : c ∈ (G.vertexOracle ρ v).calls) : G.TailFree ρ c.state :=
  (G.vertexOracle_validStack ρ v c hc).1 c.state (by simp)

theorem stack_step_residual (child parent : Directed E) (k : ℕ)
    (hc : G.TailFree ρ child) (hp : G.TailFree ρ parent)
    (hs : G.StackStep ρ child parent) (hk : k ≤ ρ.index child.1) :
    parent.1 ∈ G.residual ρ k := by
  have ht := G.free_mono (G.greedyPrefix_mono ρ (hk.trans hs.1.le)) hp
  have hh : G.Free (G.greedyPrefix ρ k) (G.head parent) := by
    rw [← hs.2]
    exact G.free_mono (G.greedyPrefix_mono ρ hk) hc
  apply (G.mem_residual ρ k parent.1).mpr
  cases parent with | mk e b => cases b <;> first | exact ⟨hh, ht⟩ | exact ⟨ht, hh⟩

end Graph

end SteinerUpperBound.Matching
