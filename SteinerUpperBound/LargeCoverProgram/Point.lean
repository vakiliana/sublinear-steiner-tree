module

public import SteinerUpperBound.LargeCoverProgram.Selection

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {Q : Type*} {n d B : ℕ}

abbrev VO (Q : Type*) (n d B : ℕ) :=
  LocalAccess.Frame (Fin n) d B → Cache Q →
    Code (Sym2 (Fin n)) Q (Bool × Cache Q)

noncomputable def inverseRate (size : ℕ) : Rate :=
  ⟨1 / (max 1 size : ℕ), (by positivity), (by
    have hs : (1 : ℝ) ≤ (max 1 size : ℕ) := by exact_mod_cast le_max_left 1 size
    apply (div_le_one (by positivity)).mpr
    exact hs)⟩

theorem inverseRate_value (size : ℕ) (hs : 0 < size) :
    (inverseRate size : ℝ) = 1 / (size : ℝ) := by
  simp only [inverseRate, max_eq_right (show 1 ≤ size by omega)]

noncomputable def afterPointFrame (D : Vector Bool n) (vo : VO Q n d B)
    (f : LocalAccess.Frame (Fin n) d B) (c : Cache Q) :
    Code (Sym2 (Fin n)) Q (ℝ × Cache Q) :=
  (LocalAccess.hitsProgram D f.points).bind (fun hit =>
    (lengthProgram f.points).bind (fun size =>
      .tick 7 (if hit then .pure (1 / (size : ℝ), c)
        else .coin (inverseRate size) (fun initiate =>
          .tick 3 (if initiate then
            (vo f c).bind (fun reply =>
              .tick 3 (.pure ((if reply.1 then (1 / 2 : ℝ) else 0), reply.2)))
          else .pure (0, c))))))

noncomputable def afterPointLocate (D : Vector Bool n) (vo : VO Q n d B)
    (located : LocalAccess.Located (Fin n) Q d B) :
    Code (Sym2 (Fin n)) Q (ℝ × Cache Q) :=
  .tick 3 (match located.frame with
    | none => .pure (0, located.cache)
    | some f => afterPointFrame D vo f located.cache)

/-- Actual cached point score. A rejected/nonretained root or a large
component scores zero. No graph, component partition, or metric is an input. -/
noncomputable def point (key : Fin n → Q) (a : ℝ) (vertices terminals : List (Fin n))
    (D : Vector Bool n) (vo : VO Q n d B) (root : Fin n) (c : Cache Q) :
    Code (Sym2 (Fin n)) Q (ℝ × Cache Q) :=
  (Cache.resolve (key root) c).bind (fun reply =>
    .tick 3 (if reply.1 then
      (LocalAccess.locateProgram key a d B vertices terminals root reply.2).bind
        (afterPointLocate D vo)
    else .pure (0, reply.2)))

noncomputable def frameValue (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (D : Vector Bool n) (vo : VO Q n d B)
    (f : LocalAccess.Frame (Fin n) d B) (c : Cache Q) (F : ℝ → ℝ) : ℝ :=
  if (LocalAccess.hitsResult D f.points).value then F (1 / (f.points.length : ℝ))
  else (CategoricalCoupling.bernoulli (inverseRate f.points.length)).expect (fun initiate =>
    if initiate then (vo f c).evaluate w bits
      (fun o => F (if o.value.1 then (1 / 2 : ℝ) else 0)) else F 0)

theorem afterPointFrame_value (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (D : Vector Bool n) (vo : VO Q n d B) (f : LocalAccess.Frame (Fin n) d B)
    (c : Cache Q) (F : ℝ → ℝ) :
    (afterPointFrame D vo f c).evaluate w bits (fun o => F o.value.1) =
      frameValue w bits D vo f c F := by
  simp only [afterPointFrame, Code.evaluate_bind]
  rw [LocalAccess.hits_evaluates w bits, length_evaluates w bits]
  simp only [(length_result f.points).1, Code.evaluate, Outcome.add, Outcome.combine,
    Outcome.pure]
  cases hhit : (LocalAccess.hitsResult D f.points).value
  · simp only [hhit, Bool.false_eq_true, ite_false, frameValue]
    apply congrArg (CategoricalCoupling.bernoulli (inverseRate f.points.length)).expect
    funext initiate
    cases initiate <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, Code.evaluate, Code.evaluate_bind,
        Outcome.add, Outcome.combine, Outcome.pure]
  · simp only [frameValue, hhit, ite_true, Code.evaluate, Outcome.pure]

theorem point_value (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (key : Fin n → Q) (a : ℝ) (vertices terminals : List (Fin n))
    (D : Vector Bool n) (vo : VO Q n d B) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct bits c) (F : ℝ → ℝ) :
    (point key a vertices terminals D vo root c).evaluate w bits (fun o => F o.value.1) =
      if bits (key root) then
        let located := (LocalAccess.locateResult w bits key a d B vertices terminals root
          (Cache.resolved bits (key root) c).value.2).value
        match located.frame with
        | none => F 0
        | some f => frameValue w bits D vo f located.cache F
      else F 0 := by
  rw [point, Code.evaluate_bind, Cache.resolve_evaluates w bits]
  have hr := (Cache.resolved_correct bits (key root) c hc).1
  simp only [Code.evaluate, Outcome.add, Outcome.combine, hr]
  cases hb : bits (key root)
  · simp [hb, Code.evaluate, Outcome.pure]
  · simp only [hb, ite_true]
    rw [Code.evaluate_bind, LocalAccess.locate_evaluates w bits]
    simp only [afterPointLocate, Code.evaluate, Outcome.add, Outcome.combine]
    split
    · rfl
    · exact afterPointFrame_value w bits D vo _ _ F

theorem afterPointFrame_cache_for (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (D : Vector Bool n) (vo : VO Q n d B)
    (f : LocalAccess.Frame (Fin n) d B) (c : Cache Q) (hc : Cache.Correct bits c)
    (hvo : (LocalAccess.hitsResult D f.points).value = false →
      ∀ o, Covers.OracleProgram.Runs w bits (vo f c) o → Cache.Correct bits o.value.2) :
    ∀ o, Covers.OracleProgram.Runs w bits (afterPointFrame D vo f c) o → Cache.Correct bits o.value.2 := by
  intro o ho
  obtain ⟨h, z, hh, hz, rfl⟩ := Covers.OracleProgram.Mean.runs_bind_inv w bits (LocalAccess.hitsProgram D f.points) _ _ ho
  have he := deterministic_run_eq w bits _ (hits_deterministic D f.points) _
    (LocalAccess.hits_evaluates w bits D f.points) h hh
  subst h
  obtain ⟨l, z', hl, hz', rfl⟩ := Covers.OracleProgram.Mean.runs_bind_inv w bits (lengthProgram f.points) _ _ hz
  have he := deterministic_run_eq w bits _ (length_deterministic f.points) _
    (length_evaluates w bits f.points) l hl
  subst l
  cases hz' with
  | tick hz' =>
      cases hb : (LocalAccess.hitsResult D f.points).value
      · simp only [hb, Bool.false_eq_true, ite_false] at hz'
        cases hz' with
        | coin initiate hz' =>
            cases hz' with
            | tick hz' =>
                cases initiate
                · simp only [Bool.false_eq_true, ite_false] at hz'; cases hz'; exact hc
                · simp only [ite_true] at hz'
                  obtain ⟨v, t, hv, ht, rfl⟩ := Covers.OracleProgram.Mean.runs_bind_inv w bits (vo f c) _ _ hz'
                  cases ht with
                  | tick ht => cases ht; exact hvo hb v hv
      · simp only [hb, ite_true] at hz'
        cases hz'
        exact hc

theorem afterPointFrame_cache (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (D : Vector Bool n) (vo : VO Q n d B)
    (hvo : ∀ f c, Cache.Correct bits c → ∀ o, Covers.OracleProgram.Runs w bits (vo f c) o →
      Cache.Correct bits o.value.2)
    (f : LocalAccess.Frame (Fin n) d B) (c : Cache Q) (hc : Cache.Correct bits c) :
    ∀ o, Covers.OracleProgram.Runs w bits (afterPointFrame D vo f c) o → Cache.Correct bits o.value.2 :=
  afterPointFrame_cache_for w bits D vo f c hc (fun _ => hvo f c hc)

theorem point_cache (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (key : Fin n → Q) (a : ℝ) (vertices terminals : List (Fin n))
    (D : Vector Bool n) (vo : VO Q n d B)
    (hvo : ∀ f c, Cache.Correct bits c → ∀ o, Covers.OracleProgram.Runs w bits (vo f c) o →
      Cache.Correct bits o.value.2)
    (root : Fin n) (c : Cache Q) (hc : Cache.Correct bits c) :
    ∀ o, Covers.OracleProgram.Runs w bits (point key a vertices terminals D vo root c) o →
      Cache.Correct bits o.value.2 := by
  intro o ho
  obtain ⟨reply, rest, hr, ht, rfl⟩ := Covers.OracleProgram.Mean.runs_bind_inv w bits (Cache.resolve (key root) c) _ _ ho
  have he := deterministic_run_eq w bits _ (resolve_deterministic _ _) _
    (Cache.resolve_evaluates w bits _ _) reply hr
  subst reply
  have hc' := (Cache.resolved_correct bits (key root) c hc).2
  cases ht with
  | tick ht =>
      cases hb : (Cache.resolved bits (key root) c).value.1
      · simp only [hb, Bool.false_eq_true, ite_false] at ht
        cases ht
        exact hc'
      · simp only [hb, ite_true] at ht
        obtain ⟨l, z, hl, hz, rfl⟩ := Covers.OracleProgram.Mean.runs_bind_inv w bits
          (LocalAccess.locateProgram key a d B vertices terminals root _) _ _ ht
        have he := deterministic_run_eq w bits _ (locate_deterministic _ _ _ _ _ _ _ _) _
          (LocalAccess.locate_evaluates w bits _ _ _ _ _ _ _ _) l hl
        subst l
        have hlc := LocalAccess.locate_cache_correct w bits key a d B vertices terminals root _ hc'
        cases hz with
        | tick hz =>
            cases hf : (LocalAccess.locateResult w bits key a d B vertices terminals root
                (Cache.resolved bits (key root) c).value.2).value.frame
            · simp only [afterPointLocate, hf] at hz
              cases hz
              exact hlc
            · simp only [afterPointLocate, hf] at hz
              have hfinal := afterPointFrame_cache w bits D vo hvo _ _ hlc _ hz
              simpa only [Outcome.combine, Outcome.add] using hfinal

end SteinerUpperBound.LargeCoverProgram
