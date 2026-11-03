module

public import SteinerUpperBound.Matching.Rotation

@[expose] public section

namespace SteinerUpperBound.Matching

open scoped Classical BigOperators

namespace Graph

def Invocation.stack {E : Type*} (c : Invocation E) : List (Directed E) :=
  c.state :: c.ancestors

namespace Run

variable {E A B : Type*}

theorem scan_all_calls (call : A → Memo E → Run E Bool) (xs : List A)
    (P : Invocation E → Prop)
    (hcall : ∀ a ∈ xs, ∀ μ, ∀ c ∈ (call a μ).calls, P c)
    (μ : Memo E) : ∀ c ∈ (scan call xs μ).calls, P c := by
  induction xs generalizing μ with
  | nil => simp [scan]
  | cons a xs ih =>
    simp only [scan]
    split_ifs
    · exact hcall a (by simp) μ
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hcall a (by simp) μ c hc
      · exact ih (fun b hb => hcall b (by simp [hb])) (call a μ).memo c hc

theorem scan_map_calls_nodup (call : A → Memo E → Run E Bool) (xs : List A)
    (f : Invocation E → B) (hxs : xs.Nodup)
    (hcall : ∀ a ∈ xs, ∀ μ, ((call a μ).calls.map f).Nodup)
    (hdisj : ∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → ∀ μ ν,
      ∀ c ∈ (call a μ).calls, ∀ c' ∈ (call b ν).calls, f c ≠ f c')
    (μ : Memo E) : ((scan call xs μ).calls.map f).Nodup := by
  induction xs generalizing μ with
  | nil => simp [scan]
  | cons a xs ih =>
    obtain ⟨han, hnd⟩ := List.nodup_cons.mp hxs
    have ha := hcall a (by simp) μ
    have ht := ih hnd (fun b hb => hcall b (by simp [hb]))
      (fun b hb c hc => hdisj b (by simp [hb]) c (by simp [hc])) (call a μ).memo
    simp only [scan]
    split_ifs
    · exact ha
    · rw [List.map_append, List.nodup_append]
      refine ⟨ha, ht, ?_⟩
      intro z hz z' hz'
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hz'
      have hproperty : ∀ q ∈ (scan call xs (call a μ).memo).calls, f c ≠ f q := by
        apply scan_all_calls call xs (fun q => f c ≠ f q)
        intro b hb ν q hq
        exact hdisj a (by simp) b (by simp [hb]) (fun heq => han (heq ▸ hb))
          μ ν c hc q hq
      exact hproperty c' hc'

end Run

variable {V E : Type*} [Fintype E]

theorem runEO_stack_suffix (G : Graph V E) (ρ : Rank E)
    (d : Directed E) (ancestors : List (Directed E)) (μ : Memo E) :
    ∀ c ∈ (G.runEO ρ d ancestors μ).calls, d :: ancestors <:+ c.stack := by
  classical
  rw [runEO]
  cases hc : μ d with
  | some b =>
    intro c h
    have heq : c = ⟨d, ancestors, true⟩ := by simpa using h
    simp [heq, Invocation.stack]
  | none =>
    let call : E → Memo E → Run E Bool := fun f ν =>
      if h : ρ.index f < ρ.index d.1 then
        G.runEO ρ (G.away (G.head d) f) (d :: ancestors) ν
      else ⟨false, ν, []⟩
    have hs := Run.scan_all_calls call (G.candidates ρ (ρ.index d.1) (G.head d))
      (fun c => d :: ancestors <:+ c.stack)
      (fun f hf ν c hc => by
        have hr := ((G.mem_candidates ρ _ _ f).mp hf).1
        dsimp only [call] at hc
        simp only [hr, ↓reduceDIte] at hc
        exact (List.suffix_cons _ _).trans
          (runEO_stack_suffix G ρ (G.away (G.head d) f) (d :: ancestors) ν c hc)) μ
    change ∀ c ∈ (⟨d, ancestors, false⟩ :: (Run.scan call _ μ).calls),
      d :: ancestors <:+ c.stack
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨[], rfl⟩
    · exact hs c hc
termination_by ρ.index d.1
decreasing_by simpa using hr

theorem suffix_same_length {A : Type*} {xs ys zs : List A}
    (hx : xs <:+ zs) (hy : ys <:+ zs) (hlen : xs.length = ys.length) : xs = ys := by
  rw [List.suffix_iff_eq_drop] at hx hy
  rw [hx, hy, hlen]

theorem runEO_stacks_nodup (G : Graph V E) (ρ : Rank E)
    (d : Directed E) (ancestors : List (Directed E)) (μ : Memo E) :
    ((G.runEO ρ d ancestors μ).calls.map Invocation.stack).Nodup := by
  classical
  rw [runEO]
  cases hc : μ d with
  | some b => simp
  | none =>
    let call : E → Memo E → Run E Bool := fun f ν =>
      if h : ρ.index f < ρ.index d.1 then
        G.runEO ρ (G.away (G.head d) f) (d :: ancestors) ν
      else ⟨false, ν, []⟩
    have hshape (f : E) (hf : f ∈ G.candidates ρ (ρ.index d.1) (G.head d))
        (ν : Memo E) (c : Invocation E) (hc : c ∈ (call f ν).calls) :
        G.away (G.head d) f :: d :: ancestors <:+ c.stack := by
      have hr := ((G.mem_candidates ρ _ _ f).mp hf).1
      dsimp only [call] at hc
      simp only [hr, ↓reduceDIte] at hc
      exact G.runEO_stack_suffix ρ _ _ ν c hc
    have hs := Run.scan_map_calls_nodup call
      (G.candidates ρ (ρ.index d.1) (G.head d)) Invocation.stack
      (G.candidates_nodup ρ _ _)
      (fun f hf ν => by
        have hr := ((G.mem_candidates ρ _ _ f).mp hf).1
        dsimp only [call]
        simp only [hr, ↓reduceDIte]
        exact runEO_stacks_nodup G ρ (G.away (G.head d) f) (d :: ancestors) ν)
      (fun f hf g hg hfg ν ξ c hc c' hc' heq => by
        have h1 := hshape f hf ν c hc
        have h2 := hshape g hg ξ c' hc'
        rw [← heq] at h2
        have hsame := suffix_same_length h1 h2 rfl
        have he : f = g := congrArg (fun ds => (ds.head?).map Prod.fst) hsame |>
          Option.some.inj
        exact hfg he) μ
    have hshort : ∀ c ∈ (Run.scan call
        (G.candidates ρ (ρ.index d.1) (G.head d)) μ).calls,
        c.stack ≠ d :: ancestors := by
      apply Run.scan_all_calls call _ (fun c => c.stack ≠ d :: ancestors)
      intro f hf ν c hc heq
      have hl := (hshape f hf ν c hc).length_le
      rw [heq] at hl
      simp only [List.length_cons] at hl
      omega
    change (Invocation.stack ⟨d, ancestors, false⟩ ::
      ((Run.scan call _ μ).calls.map Invocation.stack)).Nodup
    rw [List.nodup_cons]
    refine ⟨?_, hs⟩
    intro hm
    obtain ⟨c, hc, heq⟩ := List.mem_map.mp hm
    exact hshort c hc heq
termination_by ρ.index d.1
decreasing_by simpa using hr

variable (G : Graph V E) (ρ : Rank E)

theorem vertexOracle_stacks_nodup (v : V) :
    ((G.vertexOracle ρ v).calls.map Invocation.stack).Nodup := by
  apply Run.scan_map_calls_nodup _ _ Invocation.stack (G.candidates_nodup ρ _ v)
  · intro e _ μ
    exact G.runEO_stacks_nodup ρ _ [] μ
  · intro e _ f _ hef μ ν c hc c' hc' heq
    have h1 := G.runEO_stack_suffix ρ (G.away v e) [] μ c hc
    have h2 := G.runEO_stack_suffix ρ (G.away v f) [] ν c' hc'
    rw [← heq] at h2
    have hsame := suffix_same_length h1 h2 rfl
    have he : e = f := congrArg (fun ds => (ds.head?).map Prod.fst) hsame |>
      Option.some.inj
    exact hef he

theorem vertexOracle_root (v : V) (c : Invocation E)
    (hc : c ∈ (G.vertexOracle ρ v).calls) :
    ∃ d : Directed E, [d] <:+ c.stack ∧ G.tail d = v := by
  have h := Run.scan_all_calls
    (fun e μ => G.runEO ρ (G.away v e) [] μ) (G.candidates ρ (Fintype.card E) v)
    (fun c => ∃ d : Directed E, [d] <:+ c.stack ∧ G.tail d = v)
    (fun e he μ q hq =>
      ⟨G.away v e, G.runEO_stack_suffix ρ _ [] μ q hq,
        G.tail_away ((G.mem_candidates ρ _ v e).mp he).2⟩)
    (fun _ => none)
  exact h c hc

theorem vertexOracle_stacks_disjoint {v w : V} (hvw : v ≠ w)
    (c c' : Invocation E) (hc : c ∈ (G.vertexOracle ρ v).calls)
    (hc' : c' ∈ (G.vertexOracle ρ w).calls) : c.stack ≠ c'.stack := by
  intro heq
  obtain ⟨d, hd, hdt⟩ := G.vertexOracle_root ρ v c hc
  obtain ⟨d', hd', hdt'⟩ := G.vertexOracle_root ρ w c' hc'
  rw [← heq] at hd'
  have hdd : d = d' := List.singleton_inj.mp (suffix_same_length hd hd' rfl)
  exact hvw (hdt.symm.trans (hdd ▸ hdt'))

end Graph

end SteinerUpperBound.Matching
