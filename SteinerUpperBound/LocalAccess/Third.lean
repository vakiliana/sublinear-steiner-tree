module

public import SteinerUpperBound.LocalAccess.Centers
public import SteinerUpperBound.ComponentExplore.Memory
public import SteinerUpperBound.ComponentExplore.Step

@[expose] public section

namespace SteinerUpperBound.LocalAccess

open QueryProgram
open scoped Classical

set_option maxHeartbeats 800000

variable {V Q : Type*}

structure ThirdAnswer (Q : Type*) where
  found : Bool
  cache : Cache Q

noncomputable def thirdProgram (key : V → Q) (r : ℝ) (v : V) (C D : List V) :
    List V → Cache Q → Code (Sym2 V) Q (ThirdAnswer Q)
  | [], c => .tick 0 (.pure ⟨false, c⟩)
  | y :: l, c =>
      .tick 0 ((ComponentExplore.member y C).bind (fun hc =>
        .tick 0 (if hc then thirdProgram key r v C D l c else
          (ComponentExplore.member y D).bind (fun hd =>
            .tick 0 (if hd then thirdProgram key r v C D l c else
              .metric (Sym2.mk v y) (fun d =>
                .tick 0 (if d ≤ r then
                  (Cache.resolve (key y) c).bind (fun z =>
                    .tick 0 (if z.1 then .pure ⟨true, z.2⟩
                      else thirdProgram key r v C D l z.2))
                else thirdProgram key r v C D l c)))))))

noncomputable def thirdResult (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (r : ℝ) (v : V) (C D : List V) : List V → Cache Q → Outcome (ThirdAnswer Q)
  | [], c => (Outcome.pure ⟨false, c⟩).add 1 0 0 0
  | y :: l, c =>
      let pc := ComponentExplore.memberResult y C
      let rest : Outcome (ThirdAnswer Q) :=
        if pc.value then thirdResult w b key r v C D l c else
          let pd := ComponentExplore.memberResult y D
          let next : Outcome (ThirdAnswer Q) :=
            if pd.value then thirdResult w b key r v C D l c else
              let z : Outcome (ThirdAnswer Q) :=
                if w (Sym2.mk v y) ≤ r then
                  let s := Cache.resolved b (key y) c
                  let tail : Outcome (ThirdAnswer Q) :=
                    if s.value.1 then Outcome.pure ⟨true, s.value.2⟩
                    else thirdResult w b key r v C D l s.value.2
                  s.combine (tail.add 1 0 0 0)
                else thirdResult w b key r v C D l c
              (z.add 1 0 0 0).add 1 1 0 0
          pd.combine (next.add 1 0 0 0)
      (pc.combine (rest.add 1 0 0 0)).add 1 0 0 0

theorem third_evaluates (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (r : ℝ) (v : V) (C D l : List V) (c : Cache Q) :
    Code.Evaluates w b (thirdProgram key r v C D l c) (thirdResult w b key r v C D l c) := by
  induction l generalizing c with
  | nil => intro F; rfl
  | cons y l ih =>
      intro F
      simp only [thirdProgram, thirdResult, Code.evaluate, Code.evaluate_bind]
      rw [ComponentExplore.member_evaluates w b y C]
      cases hc : (ComponentExplore.memberResult y C).value <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, Code.evaluate]
      · rw [Code.evaluate_bind, ComponentExplore.member_evaluates w b y D]
        cases hd : (ComponentExplore.memberResult y D).value <;>
          simp only [Bool.false_eq_true, ite_false, ite_true, Code.evaluate]
        · by_cases hr : w (Sym2.mk v y) ≤ r
          · simp only [hr, ite_true, Code.evaluate_bind]
            rw [Cache.resolve_evaluates w b (key y) c]
            cases hz : (Cache.resolved b (key y) c).value.1 <;>
              simp only [Bool.false_eq_true, ite_false, ite_true, Code.evaluate] <;> rw [ih]
          · simp only [hr, ite_false]
            rw [ih]
        · rw [ih]
      · rw [ih]

theorem third_work (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (r : ℝ) (v : V) (C D l : List V) (c : Cache Q) :
    (thirdResult w b key r v C D l c).work ≤
      (2 * (C.length + D.length) + 12) * (l.length + 1) := by
  induction l generalizing c with
  | nil => simp [thirdResult, Outcome.add, Outcome.pure]
  | cons y l ih =>
      have hC := ComponentExplore.member_work y C
      have hD := ComponentExplore.member_work y D
      have hcache := Cache.resolved_work_le b (key y) c
      have ht := ih c
      have hn := ih (Cache.resolved b (key y) c).value.2
      cases hc : (ComponentExplore.memberResult y C).value <;>
        cases hd : (ComponentExplore.memberResult y D).value <;>
        by_cases hr : w (Sym2.mk v y) ≤ r <;>
        cases hz : (Cache.resolved b (key y) c).value.1 <;>
        simp only [thirdResult, hc, hd, hr, hz, Bool.false_eq_true, ite_false, ite_true,
          Outcome.add, Outcome.combine, Outcome.pure, List.length_cons] <;> nlinarith

theorem third_metric_queries (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (r : ℝ) (v : V) (C D l : List V) (c : Cache Q) :
    (thirdResult w b key r v C D l c).metricQueries ≤ l.length := by
  induction l generalizing c with
  | nil => exact Nat.zero_le _
  | cons y l ih =>
      have hC := (ComponentExplore.member_counters y C).1
      have hD := (ComponentExplore.member_counters y D).1
      have hcache : (Cache.resolved b (key y) c).metricQueries = 0 := by
        cases h : c (key y) <;> simp only [Cache.resolved, h]
      have ht := ih c
      have hn := ih (Cache.resolved b (key y) c).value.2
      cases hc : (ComponentExplore.memberResult y C).value <;>
        cases hd : (ComponentExplore.memberResult y D).value <;>
        by_cases hr : w (Sym2.mk v y) ≤ r <;>
        cases hz : (Cache.resolved b (key y) c).value.1 <;>
        simp only [thirdResult, hc, hd, hr, hz, Bool.false_eq_true, ite_false, ite_true,
          Outcome.add, Outcome.combine, Outcome.pure, List.length_cons, hC, hD, hcache] <;> omega

theorem third_positive (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (r : ℝ) (v : V) (C D l : List V) (c : Cache Q) :
    (thirdResult w b key r v C D l c).positiveReplies ≤ 1 := by
  induction l generalizing c with
  | nil => exact Nat.zero_le _
  | cons y l ih =>
      have hC := (ComponentExplore.member_counters y C).2.2
      have hD := (ComponentExplore.member_counters y D).2.2
      have hcache := ComponentExplore.resolved_positive_bit b (key y) c
      have ht := ih c
      have hn := ih (Cache.resolved b (key y) c).value.2
      cases hc : (ComponentExplore.memberResult y C).value <;>
        cases hd : (ComponentExplore.memberResult y D).value <;>
        by_cases hr : w (Sym2.mk v y) ≤ r <;>
        cases hz : (Cache.resolved b (key y) c).value.1 <;>
        simp only [hz, Bool.false_eq_true, ite_false, ite_true] at hcache <;>
        simp only [thirdResult, hc, hd, hr, hz, Bool.false_eq_true, ite_false, ite_true,
          Outcome.add, Outcome.combine, Outcome.pure, hC, hD] <;> omega

theorem third_cache_correct (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (r : ℝ) (v : V) (C D l : List V) (c : Cache Q) (h : Cache.Correct b c) :
    Cache.Correct b (thirdResult w b key r v C D l c).value.cache := by
  induction l generalizing c with
  | nil => exact h
  | cons y l ih =>
      have hcache := (Cache.resolved_correct b (key y) c h).2
      have ht := ih c h
      have hn := ih _ hcache
      cases hc : (ComponentExplore.memberResult y C).value <;>
        cases hd : (ComponentExplore.memberResult y D).value <;>
        by_cases hr : w (Sym2.mk v y) ≤ r <;>
        cases hz : (Cache.resolved b (key y) c).value.1 <;>
        simp only [thirdResult, hc, hd, hr, hz, Bool.false_eq_true, ite_false, ite_true,
          Outcome.add, Outcome.combine, Outcome.pure] <;>
        first | exact hcache | exact hn | exact ht

theorem third_value (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (r : ℝ) (v : V) (C D l : List V) (c : Cache Q) (h : Cache.Correct b c) :
    (thirdResult w b key r v C D l c).value.found = true ↔
      ∃ y ∈ l, y ∉ C ∧ y ∉ D ∧ w (Sym2.mk v y) ≤ r ∧ b (key y) = true := by
  induction l generalizing c with
  | nil => simp [thirdResult, Outcome.add, Outcome.pure]
  | cons y l ih =>
      have hcache := Cache.resolved_correct b (key y) c h
      have ht := ih c h
      have hn := ih _ hcache.2
      by_cases hc : y ∈ C <;> by_cases hd : y ∈ D <;>
        by_cases hr : w (Sym2.mk v y) ≤ r <;> cases hz : b (key y) <;>
        simp [thirdResult, ComponentExplore.member_value_eq, hc, hd, hr, hcache.1,
          hz, Outcome.add, Outcome.combine, Outcome.pure, ht, hn]

end SteinerUpperBound.LocalAccess
