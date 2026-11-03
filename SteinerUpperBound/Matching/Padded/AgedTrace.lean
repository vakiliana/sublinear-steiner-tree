module

public import SteinerUpperBound.Matching.Padded.OracleWorkBasic

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical

namespace Program

variable {C A B : Type*}

theorem Bound.shift {p : Program C A} {charge : C → ℝ} {rate : ℝ} {post : A → ℝ} {budget : ℝ}
    (h : p.Bound charge rate post budget) (c : ℝ) :
    p.Bound charge rate (fun a => post a + c) (budget + c) := by
  intro leaf
  have hh := h leaf
  linarith

theorem Bound.weaken {p : Program C A} {charge : C → ℝ} {rate : ℝ} {post : A → ℝ} {b B : ℝ}
    (h : p.Bound charge rate post b) (hb : b ≤ B) : p.Bound charge rate post B :=
  fun leaf => (h leaf).trans hb

theorem bound_bind_supported (p : Program C A) (k : A → Program C B)
    (charge : C → ℝ) (rate : ℝ) (mid : A → ℝ) (post : B → ℝ) (budget : ℝ) (P : A → Prop)
    (hp : p.Bound charge rate mid budget) (hs : p.Supported P)
    (hk : ∀ a, P a → (k a).Bound charge rate post (mid a)) :
    (p.bind k).Bound charge rate post budget := by
  induction p generalizing budget with
  | ret a =>
    intro leaf
    have hh := hp PUnit.unit
    have ht := hk a (hs PUnit.unit) leaf
    change 0 + mid a ≤ budget at hh
    change (k a).cost charge rate leaf + post ((k a).output leaf) ≤ budget
    exact ht.trans (by linarith)
  | tick c p ih =>
    apply bound_tick
    apply ih
    · intro leaf
      have hh := hp leaf
      change charge c + p.cost charge rate leaf + mid (p.output leaf) ≤ budget at hh
      linarith
    · exact hs
  | draw n hn next ih =>
    apply bound_draw
    intro i
    apply ih i
    · intro leaf
      have hh := hp ⟨i, leaf⟩
      change rate + (next i).cost charge rate leaf + mid ((next i).output leaf) ≤ budget at hh
      linarith
    · exact fun leaf => hs ⟨i, leaf⟩

end Program

variable {E : Type*}

def agedTrace (baseline : ℝ) (cs : List (Invocation E)) : ℝ :=
  (cs.map (fun c => (c.ancestors.length : ℝ) + 1 - baseline)).sum

@[simp] theorem agedTrace_nil (baseline : ℝ) : agedTrace baseline ([] : List (Invocation E)) = 0 := rfl

theorem agedTrace_cons (baseline : ℝ) (c : Invocation E) (cs : List (Invocation E)) :
    agedTrace baseline (c :: cs) = c.ancestors.length + 1 - baseline + agedTrace baseline cs := rfl

theorem agedTrace_append (baseline : ℝ) (xs ys : List (Invocation E)) :
    agedTrace baseline (xs ++ ys) = agedTrace baseline xs + agedTrace baseline ys := by
  simp [agedTrace, List.map_append, List.sum_append]

theorem agedTrace_shift (baseline : ℝ) (cs : List (Invocation E)) :
    agedTrace baseline cs = agedTrace (baseline + 1) cs + cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [agedTrace_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih]
    ring

namespace Oracle

variable {V : Type*} {G : Graph V E} (S : Slots G) [Fintype V] (P : Parameters S)

theorem edge_calls_nonempty (d : Directed E) (rank : Fin P.rankCard)
    (ancestors : List (Directed E)) (s : Cache S P.rankCard) (μ : Memo E) :
    (Oracle.edge S P d rank ancestors s μ).Supported (fun r => r.calls ≠ []) := by
  rw [Oracle.edge]
  apply Program.supported_tick
  cases hm : μ d with
  | some value => exact Program.supported_ret _ _ (by simp)
  | none =>
    dsimp only
    refine Program.supported_bind
      (A := LocalRun S P.rankCard (Option (Entry S P.rankCard)))
      (B := LocalRun S P.rankCard Bool) _ _ (fun _ => True) _ (fun _ => trivial) ?_
    intro r _
    apply Program.supported_tick
    exact Program.supported_ret _ _ (by simp)

end Oracle

end SteinerUpperBound.Matching.Padded
