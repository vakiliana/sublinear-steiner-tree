module

public import SteinerUpperBound.Matching.Caching

@[expose] public section

namespace SteinerUpperBound.Matching

open scoped Classical BigOperators

namespace Graph

variable {E : Type*}

/-- Number of invocations to a directed state; cache hits are included. -/
noncomputable def requests (cs : List (Invocation E)) (d : Directed E) : ℕ :=
  cs.countP fun c => decide (c.state = d)

@[simp] theorem requests_append (xs ys : List (Invocation E)) (d : Directed E) :
    requests (xs ++ ys) d = requests xs d + requests ys d := by
  simp [requests]

namespace Run

variable {A : Type*}

theorem scan_requests_bound (call : A → Memo E → Run E Bool) (root : A → Directed E)
    (xs : List A) (d : Directed E)
    (hcall : ∀ a ∈ xs, ∀ μ, requests (call a μ).calls d ≤
      (if root a = d then 1 else 0) + (misses (call a μ).calls).length)
    (μ : Memo E) :
    requests (scan call xs μ).calls d ≤
      xs.countP (fun a => decide (root a = d)) + (misses (scan call xs μ).calls).length := by
  classical
  induction xs generalizing μ with
  | nil => simp [scan, requests]
  | cons a xs ih =>
    have ha := hcall a (by simp) μ
    have ht := ih (fun b hb => hcall b (by simp [hb])) (call a μ).memo
    simp only [scan]
    split_ifs
    · simp only [List.countP_cons, decide_eq_true_eq]
      split_ifs at ha ⊢ <;> omega
    · simp only [requests_append, misses_append, List.length_append, List.countP_cons,
        decide_eq_true_eq]
      split_ifs at ha ⊢ <;> omega

end Run

theorem nodup_countP_eq_le_one {A B : Type*} [DecidableEq B]
    (xs : List A) (f : A → B) (b : B)
    (hn : xs.Nodup) (hf : Function.Injective f) :
    xs.countP (fun a => decide (f a = b)) ≤ 1 := by
  classical
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha, hxs⟩ := List.nodup_cons.mp hn
    by_cases hab : f a = b
    · have hzero : xs.countP (fun a => decide (f a = b)) = 0 := by
        apply List.countP_eq_zero.mpr
        intro x hx
        simp only [decide_eq_true_eq]
        intro hxb
        exact ha (hf (hab.trans hxb.symm) ▸ hx)
      simp [hab, hzero]
    · simpa [List.countP_cons, hab] using ih hxs

variable {V : Type*} [Fintype E]

theorem runEO_requests_bound (G : Graph V E) (ρ : Rank E)
    (d s : Directed E) (ancestors : List (Directed E)) (μ : Memo E) :
    requests (G.runEO ρ d ancestors μ).calls s ≤
      (if d = s then 1 else 0) + (misses (G.runEO ρ d ancestors μ).calls).length := by
  classical
  rw [runEO]
  cases hc : μ d with
  | some b => simp [requests, misses]
  | none =>
    let call : E → Memo E → Run E Bool := fun f ν =>
      if h : ρ.index f < ρ.index d.1 then
        G.runEO ρ (G.away (G.head d) f) (d :: ancestors) ν
      else ⟨false, ν, []⟩
    let r := Run.scan call (G.candidates ρ (ρ.index d.1) (G.head d)) μ
    have hs : requests r.calls s ≤
        (G.candidates ρ (ρ.index d.1) (G.head d)).countP
          (fun f => decide (G.away (G.head d) f = s)) + (misses r.calls).length := by
      apply Run.scan_requests_bound
      intro f hf ν
      have hr := ((G.mem_candidates ρ _ _ f).mp hf).1
      dsimp only [call]
      simp only [hr, ↓reduceDIte]
      exact runEO_requests_bound G ρ (G.away (G.head d) f) s (d :: ancestors) ν
    have hdirect := nodup_countP_eq_le_one
      (G.candidates ρ (ρ.index d.1) (G.head d)) (G.away (G.head d)) s
      (G.candidates_nodup ρ _ _) (fun _ _ h => congrArg Prod.fst h)
    change (G.candidates ρ (ρ.index d.1) (G.head d)).countP
      (fun f => decide (G.away (G.head d) f = s)) ≤ 1 at hdirect
    have hbound : requests r.calls s ≤ 1 + (misses r.calls).length :=
      hs.trans (Nat.add_le_add_right hdirect _)
    change requests (⟨d, ancestors, false⟩ :: r.calls) s ≤
      (if d = s then 1 else 0) + (misses (⟨d, ancestors, false⟩ :: r.calls)).length
    simp only [requests, List.countP_cons, decide_eq_true_eq, misses, List.filter_cons, Bool.not_false,
      ↓reduceIte, List.map_cons, List.length_cons]
    change (requests r.calls s + if d = s then 1 else 0) ≤
      (if d = s then 1 else 0) + ((misses r.calls).length + 1)
    omega
termination_by ρ.index d.1
decreasing_by simpa using hr

variable (G : Graph V E) (ρ : Rank E)

theorem vertexOracle_requests_le (v : V) (d : Directed E) :
    requests (G.vertexOracle ρ v).calls d ≤ 2 * Fintype.card E + 1 := by
  have hs := Run.scan_requests_bound
    (fun e μ => G.runEO ρ (G.away v e) [] μ) (G.away v)
    (G.candidates ρ (Fintype.card E) v) d
    (fun e _ μ => G.runEO_requests_bound ρ (G.away v e) d [] μ) (fun _ => none)
  have hdirect := nodup_countP_eq_le_one (G.candidates ρ (Fintype.card E) v)
    (G.away v) d (G.candidates_nodup ρ _ v) (fun _ _ h => congrArg Prod.fst h)
  change (G.candidates ρ (Fintype.card E) v).countP
    (fun e => decide (G.away v e = d)) ≤ 1 at hdirect
  have hmiss := G.vertexOracle_misses_le ρ v
  change requests (G.vertexOracle ρ v).calls d ≤
    (G.candidates ρ (Fintype.card E) v).countP (fun e => decide (G.away v e = d)) +
      (misses (G.vertexOracle ρ v).calls).length at hs
  have hbound := hs.trans (Nat.add_le_add hdirect hmiss)
  omega

/-- Invocations summed over separate, fresh-cache requests at all roots. -/
noncomputable def Q [Fintype V] (d : Directed E) : ℕ :=
  ∑ v, requests (G.vertexOracle ρ v).calls d

theorem Q_le [Fintype V] (d : Directed E) :
    G.Q ρ d ≤ Fintype.card V * (2 * Fintype.card E + 1) := by
  calc
    _ ≤ ∑ _v : V, (2 * Fintype.card E + 1) :=
      Finset.sum_le_sum fun v _ => G.vertexOracle_requests_le ρ v d
    _ = _ := by simp [Nat.mul_comm]

end Graph

end SteinerUpperBound.Matching
