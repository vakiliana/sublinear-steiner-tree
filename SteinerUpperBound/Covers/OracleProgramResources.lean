module

public import SteinerUpperBound.Covers.OracleProgramBasic

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {V Q R : Type*} {k : ℕ}

theorem reply_remaining (s : State Q) (q : Q) (v : Bool) :
    (s.reply q v).remaining = s.remaining := by
  cases he : s.cache q <;> simp [State.reply, he]

theorem scan_resources (cfg : Config V Q k) (m : Sym2 V → ℝ) (b : Q → Bool)
    (q : Q) (B ψ : ℕ) (s : State Q) (D W : ℕ) (hD : s.remaining = some D)
    (next : Bool → State Q → Code (Sym2 V) Q (Result Q R))
    (hnext : ∀ v t d, t.remaining = some d → ∀ o, Runs m b (next v t) o →
      o.metricQueries ≤ W + d ∧ o.work ≤ 32 * (W + d + 1) + 4 ∧ o.retentionQueries = 0) :
    ∀ o, Runs m b (scan cfg q B ψ s next (fun t => .pure (.abort t))) o →
      o.metricQueries ≤ W + D ∧ o.work ≤ 32 * (W + D + 1) + 8 ∧ o.retentionQueries = 0 := by
  induction B generalizing ψ s D with
  | zero =>
    intro o hr
    rw [scan] at hr
    cases hr with
    | tick hr =>
      have h := hnext false s D hD _ hr
      simp only [Outcome.add] at *
      omega
  | succ B ih =>
    cases ψ with
    | zero =>
      intro o hr
      rw [scan] at hr
      cases hr with
      | tick hr =>
        have h := hnext false s D hD _ hr
        simp only [Outcome.add] at *
        omega
    | succ ψ =>
      intro o hr
      rw [scan] at hr
      cases hr with
      | tick hr =>
        cases D with
        | zero =>
          rw [if_pos hD] at hr
          cases hr
          simp [Outcome.add, Outcome.pure] <;> omega
        | succ D =>
          have hn : s.remaining ≠ some 0 := by rw [hD]; simp
          rw [if_neg hn] at hr
          cases hr with
          | uniform y hr =>
            cases hr with
            | tick hr =>
              have hdraw : s.draw.remaining = some D := by simp [State.draw, hD]
              by_cases hy : y = cfg.target q
              · rw [if_pos hy] at hr
                have h := hnext true s.draw D hdraw _ hr
                simp only [Outcome.add] at *
                omega
              · rw [if_neg hy] at hr
                cases hr with
                | metric hr =>
                  cases hr with
                  | tick hr =>
                    have h := ih (if m (Sym2.mk (cfg.label (cfg.target q)) (cfg.label y)) ≤
                        cfg.radius q then ψ else ψ + 1) s.draw D hdraw _ hr
                    simp only [Outcome.add] at *
                    omega

theorem resolve_pure_resources (cfg : Config V Q k) (m : Sym2 V → ℝ) (b : Q → Bool)
    (r : R) (s : State Q) (W D : ℕ) :
    ∀ o, Runs m b (resolve cfg (.pure r) s) o →
      o.metricQueries ≤ W + D ∧ o.work ≤ 32 * (W + D + 1) ∧ o.retentionQueries = 0 := by
  intro o hr
  rw [resolve] at hr
  cases hr with
  | tick hr =>
    cases hr
    simp [Outcome.add, Outcome.pure] <;> omega

theorem resolve_cap_resources (cfg : Config V Q k) (m : Sym2 V → ℝ) (b : Q → Bool)
    (p : Code (Sym2 V) Q R) (W : ℕ) (s : State Q) (D : ℕ) (hD : s.remaining = some D) :
    ∀ o, Runs m b (resolve cfg (p.cap W) s) o →
      o.metricQueries ≤ W + D ∧ o.work ≤ 32 * (W + D + 1) ∧ o.retentionQueries = 0 := by
  induction p generalizing W s D with
  | pure r => exact resolve_pure_resources cfg m b (some r) s W D
  | metric q next ih =>
    by_cases hW : 1 ≤ W
    · rw [Code.cap, if_pos hW, resolve]
      intro o hr
      cases hr with
      | tick hr =>
        cases hr with
        | metric hr =>
          have h := ih (m q) (W - 1) s D hD _ hr
          simp only [Outcome.add] at *
          omega
    · rw [Code.cap, if_neg hW]
      exact resolve_pure_resources cfg m b none s W D
  | retained q next ih =>
    by_cases hW : 1 ≤ W
    · rw [Code.cap, if_pos hW, resolve]
      intro o hr
      cases hr with
      | tick hr =>
        cases he : s.cache q with
        | some v =>
          rw [he] at hr
          cases hr with
          | tick hr =>
            have h := ih v (W - 1) (s.reply q v) D (by rwa [reply_remaining]) _ hr
            simp only [Outcome.add] at *
            omega
        | none =>
          rw [he] at hr
          have hn :
              ∀ (v : Bool) (t : State Q) (d : ℕ), t.remaining = some d → ∀ o,
                Runs m b (.tick 3 (resolve cfg ((next v).cap (W - 1)) (t.reply q v))) o →
                  o.metricQueries ≤ (W - 1) + d ∧
                    o.work ≤ 32 * ((W - 1) + d + 1) + 4 ∧ o.retentionQueries = 0 := by
            intro v t d hd o ho
            cases ho with
            | tick ho =>
              have h := ih v (W - 1) (t.reply q v) d (by rwa [reply_remaining]) _ ho
              simp only [Outcome.add] at *
              omega
          have h := scan_resources cfg m b q (cfg.caps q) (cfg.trials q) s D (W - 1) hD
            (fun v t => .tick 3 (resolve cfg ((next v).cap (W - 1)) (t.reply q v))) hn _ hr
          simp only [Outcome.add] at *
          omega
    · rw [Code.cap, if_neg hW]
      exact resolve_pure_resources cfg m b none s W D
  | uniform n next ih =>
    by_cases hW : 1 ≤ W
    · rw [Code.cap, if_pos hW, resolve]
      intro o hr
      cases hr with
      | tick hr =>
        cases hr with
        | uniform a hr =>
          have h := ih a (W - 1) s D hD _ hr
          simp only [Outcome.add] at *
          omega
    · rw [Code.cap, if_neg hW]
      exact resolve_pure_resources cfg m b none s W D
  | coin rate next ih =>
    by_cases hW : 2 ≤ W
    · rw [Code.cap, if_pos hW, resolve]
      intro o hr
      cases hr with
      | tick hr =>
        cases hr with
        | coin a hr =>
          have h := ih a (W - 2) s D hD _ hr
          simp only [Outcome.add] at *
          omega
    · rw [Code.cap, if_neg hW]
      exact resolve_pure_resources cfg m b none s W D
  | tick n next ih =>
    by_cases hW : n + 1 ≤ W
    · rw [Code.cap, if_pos hW, resolve]
      intro o hr
      cases hr with
      | tick hr =>
        cases hr with
        | tick hr =>
          have h := ih (W - (n + 1)) s D hD _ hr
          simp only [Outcome.add] at *
          omega
    · rw [Code.cap, if_neg hW]
      exact resolve_pure_resources cfg m b none s W D

/-- Worst-case counters of every compiled execution, not expectation bounds or
a resource contract supplied by a caller. -/
theorem factory_resources (cfg : Config V Q k) (m : Sym2 V → ℝ) (b : Q → Bool)
    (cache : Q → Option Bool) (W D : ℕ) (p : Code (Sym2 V) Q R)
    (seed : ((factory cfg cache W D p).compile m).Seed) :
    let o := (((factory cfg cache W D p).compile m).tree seed).output b
    o.metricQueries ≤ W + D ∧ o.work ≤ 32 * (W + D + 1) ∧ o.retentionQueries = 0 :=
  resolve_cap_resources cfg m b p W (State.initial cache D) D rfl _
    (runs_compile m b (factory cfg cache W D p) seed)

theorem scan_value_invariant (cfg : Config V Q k) (m : Sym2 V → ℝ) (b : Q → Bool)
    (q : Q) (B ψ : ℕ) (s : State Q) (P : State Q → Prop)
    (hs : P s) (hdraw : ∀ t, P t → t.remaining ≠ some 0 → P t.draw)
    (next : Bool → State Q → Code (Sym2 V) Q (Result Q R))
    (hnext : ∀ v t, P t → ∀ o, Runs m b (next v t) o → P o.value.state) :
    ∀ o, Runs m b (scan cfg q B ψ s next (fun t => .pure (.abort t))) o →
      P o.value.state := by
  induction B generalizing ψ s with
  | zero =>
    intro o hr
    rw [scan] at hr
    cases hr with
    | tick hr =>
      have h := hnext false s hs _ hr
      exact h
  | succ B ih =>
    cases ψ with
    | zero =>
      intro o hr
      rw [scan] at hr
      cases hr with
      | tick hr =>
        have h := hnext false s hs _ hr
        exact h
    | succ ψ =>
      intro o hr
      rw [scan] at hr
      cases hr with
      | tick hr =>
        by_cases hn : s.remaining = some 0
        · rw [if_pos hn] at hr
          cases hr
          exact hs
        · rw [if_neg hn] at hr
          cases hr with
          | uniform y hr =>
            cases hr with
            | tick hr =>
              have hd := hdraw s hs hn
              by_cases hy : y = cfg.target q
              · rw [if_pos hy] at hr
                have h := hnext true s.draw hd _ hr
                exact h
              · rw [if_neg hy] at hr
                cases hr with
                | metric hr =>
                  cases hr with
                  | tick hr =>
                    have h := ih _ s.draw hd _ hr
                    exact h

theorem resolve_value_invariant (cfg : Config V Q k) (m : Sym2 V → ℝ) (b : Q → Bool)
    (p : Code (Sym2 V) Q R) (s : State Q) (P : State Q → Prop)
    (hs : P s) (hdraw : ∀ t, P t → t.remaining ≠ some 0 → P t.draw)
    (hreply : ∀ t q v, P t → P (t.reply q v)) :
    ∀ o, Runs m b (resolve cfg p s) o → P o.value.state := by
  induction p generalizing s with
  | pure r =>
    intro o hr
    rw [resolve] at hr
    cases hr with
    | tick hr => cases hr; exact hs
  | metric q next ih =>
    intro o hr
    rw [resolve] at hr
    cases hr with
    | tick hr =>
      cases hr with
      | metric hr =>
        have h := ih (m q) s hs _ hr
        exact h
  | retained q next ih =>
    intro o hr
    rw [resolve] at hr
    cases hr with
    | tick hr =>
      cases he : s.cache q with
      | some v =>
        rw [he] at hr
        cases hr with
        | tick hr =>
          have h := ih v (s.reply q v) (hreply s q v hs) _ hr
          exact h
      | none =>
        rw [he] at hr
        apply scan_value_invariant cfg m b q _ _ s P hs hdraw _ _ _ hr
        intro v t ht o ho
        cases ho with
        | tick ho =>
          have h := ih v (t.reply q v) (hreply t q v ht) _ ho
          exact h
  | uniform n next ih =>
    intro o hr
    rw [resolve] at hr
    cases hr with
    | tick hr =>
      cases hr with
      | uniform a hr =>
        have h := ih a s hs _ hr
        exact h
  | coin rate next ih =>
    intro o hr
    rw [resolve] at hr
    cases hr with
    | tick hr =>
      cases hr with
      | coin a hr =>
        have h := ih a s hs _ hr
        exact h
  | tick n next ih =>
    intro o hr
    rw [resolve] at hr
    cases hr with
    | tick hr =>
      cases hr with
      | tick hr =>
        have h := ih s hs _ hr
        exact h

theorem factory_positive_le (cfg : Config V Q k) (m : Sym2 V → ℝ) (b : Q → Bool)
    (cache : Q → Option Bool) (W D : ℕ) (p : Code (Sym2 V) Q R)
    (seed : ((factory cfg cache W D p).compile m).Seed) :
    let s := ((((factory cfg cache W D p).compile m).tree seed).output b).value.state
    s.newPositive ≤ s.frontPositive :=
  resolve_value_invariant cfg m b (p.cap W) (State.initial cache D)
    (fun s => s.newPositive ≤ s.frontPositive) (Nat.le_refl 0)
    (fun _ h _ => h) (fun t q v ht => State.reply_positive t q v ht) _
    (runs_compile m b (factory cfg cache W D p) seed)

theorem factory_draw_balance (cfg : Config V Q k) (m : Sym2 V → ℝ) (b : Q → Bool)
    (cache : Q → Option Bool) (W D : ℕ) (p : Code (Sym2 V) Q R)
    (seed : ((factory cfg cache W D p).compile m).Seed) :
    let s := ((((factory cfg cache W D p).compile m).tree seed).output b).value.state
    ∃ d, s.remaining = some d ∧ s.draws + d = D := by
  apply resolve_value_invariant cfg m b (p.cap W) (State.initial cache D)
    (fun s => ∃ d, s.remaining = some d ∧ s.draws + d = D)
    ⟨D, rfl, by simp [State.initial]⟩ _ _ _
    (runs_compile m b (factory cfg cache W D p) seed)
  · intro t ht hn
    obtain ⟨d, hd, he⟩ := ht
    have hd0 : d ≠ 0 := fun he => hn (by simpa only [he] using hd)
    have hpos : 0 < d := Nat.pos_of_ne_zero hd0
    refine ⟨d - 1, ?_, ?_⟩
    · simp [State.draw, hd, Nat.pred_eq_sub_one]
    · simp only [State.draw]
      omega
  · intro t q v ht
    obtain ⟨d, hd, he⟩ := ht
    refine ⟨d, by rwa [reply_remaining], ?_⟩
    cases hc : t.cache q <;> simpa only [State.reply, hc] using he

end SteinerUpperBound.Covers.OracleProgram
