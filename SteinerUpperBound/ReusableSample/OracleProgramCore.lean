module

public import SteinerUpperBound.QueryProgram.Composition
public import SteinerUpperBound.ReusableSample.MembershipMatrix

@[expose] public section

namespace SteinerUpperBound.ReusableSample.OracleProgram

open SteinerLowerBound
open SteinerUpperBound.QueryProgram
open scoped BigOperators Classical

variable {M Q R S : Type*}

/-- Pathwise semantics, including zero-probability random branches. -/
def Sure (m : M → ℝ) (b : Q → Bool) :
    Code M Q R → (Outcome R → Prop) → Prop
  | .pure r, P => P (.pure r)
  | .metric q next, P => Sure m b (next (m q)) (fun o => P (o.add 1 1 0 0))
  | .retained q next, P =>
      Sure m b (next (b q)) (fun o => P (o.add 1 0 1 (if b q then 1 else 0)))
  | .uniform _ next, P => ∀ a, Sure m b (next a) (fun o => P (o.add 1 0 0 0))
  | .coin _ next, P => ∀ a, Sure m b (next a) (fun o => P (o.add 2 0 0 0))
  | .tick n next, P => Sure m b next (fun o => P (o.add (n + 1) 0 0 0))

theorem Sure.mono (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    {P P' : Outcome R → Prop} (hp : Sure m b p P) (h : ∀ o, P o → P' o) :
    Sure m b p P' := by
  induction p generalizing P P' with
  | pure r => exact h _ hp
  | metric q next ih => exact ih (m q) hp (fun o => h _)
  | retained q next ih => exact ih (b q) hp (fun o => h _)
  | uniform n next ih => exact fun a => ih a (hp a) (fun o => h _)
  | coin rate next ih => exact fun a => ih a (hp a) (fun o => h _)
  | tick n next ih => exact ih hp (fun o => h _)

theorem Sure.bind (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (k : R → Code M Q S) (P : Outcome S → Prop)
    (h : Sure m b p (fun a => Sure m b (k a.value) (fun o => P (a.combine o)))) :
    Sure m b (p.bind k) P := by
  induction p generalizing P with
  | pure r => simpa only [Sure, Code.bind, Outcome.pure, Outcome.combine, Nat.zero_add] using h
  | metric q next ih =>
      apply ih (m q) (fun o => P (o.add 1 1 0 0))
      simpa only [Sure, Outcome.add, Outcome.combine, Nat.add_assoc] using h
  | retained q next ih =>
      apply ih (b q) (fun o => P (o.add 1 0 1 (if b q then 1 else 0)))
      simpa only [Sure, Outcome.add, Outcome.combine, Nat.add_assoc] using h
  | uniform n next ih =>
      intro a
      apply ih a (fun o => P (o.add 1 0 0 0))
      simpa only [Outcome.add, Outcome.combine, Nat.add_assoc] using h a
  | coin rate next ih =>
      intro a
      apply ih a (fun o => P (o.add 2 0 0 0))
      simpa only [Outcome.add, Outcome.combine, Nat.add_assoc] using h a
  | tick n next ih =>
      apply ih (fun o => P (o.add (n + 1) 0 0 0))
      simpa only [Sure, Outcome.add, Outcome.combine, Nat.add_assoc] using h

theorem Sure.compile (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (P : Outcome R → Prop) (h : Sure m b p P) :
    ∀ s : (p.compile m).Seed, P (((p.compile m).tree s).output b) := by
  induction p generalizing P with
  | pure r => intro s; exact h
  | metric q next ih =>
      intro s
      simpa only [Code.compile, Compiled.map, DecisionTree.output_map] using ih (m q) _ h s
  | retained q next ih =>
      intro s
      cases hb : b q
      · simpa only [Code.compile, Compiled.query, DecisionTree.output, hb,
          Bool.false_eq_true, ↓reduceIte, Compiled.map, DecisionTree.output_map] using
          ih false _ (by simpa only [Sure, hb, Bool.false_eq_true, ↓reduceIte] using h) s.1
      · simpa only [Code.compile, Compiled.query, DecisionTree.output, hb,
          ↓reduceIte, Compiled.map, DecisionTree.output_map] using
          ih true _ (by simpa only [Sure, hb, ↓reduceIte] using h) s.2
  | uniform n next ih =>
      intro s
      simpa only [Code.compile, Compiled.map, Compiled.choose, DecisionTree.output_map] using
        ih s.1 _ (h s.1) s.2
  | coin rate next ih =>
      intro s
      simpa only [Code.compile, Compiled.map, Compiled.choose, DecisionTree.output_map] using
        ih s.1 _ (h s.1) s.2
  | tick n next ih =>
      intro s
      simpa only [Code.compile, Compiled.map, DecisionTree.output_map] using ih _ h s

def Good (P : R → Prop) (work queries : ℕ) (o : Outcome R) : Prop :=
  P o.value ∧ o.work ≤ work ∧ o.metricQueries = queries ∧
    o.retentionQueries = 0 ∧ o.positiveReplies = 0

theorem good_mono (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    {P P' : R → Prop} {w w' q : ℕ}
    (h : Sure m b p (Good P w q)) (hw : w ≤ w') (hp : ∀ r, P r → P' r) :
    Sure m b p (Good P' w' q) :=
  h.mono m b p (fun _ ho =>
    ⟨hp _ ho.1, ho.2.1.trans hw, ho.2.2.1, ho.2.2.2.1, ho.2.2.2.2⟩)

theorem good_pure (m : M → ℝ) (b : Q → Bool) (r : R) :
    Sure m b (.pure r) (Good (· = r) 0 0) := by
  simp [Sure, Good, Outcome.pure]

theorem good_tick (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (P : R → Prop) (w q n : ℕ) (h : Sure m b p (Good P w q)) :
    Sure m b (.tick n p) (Good P (n + 1 + w) q) := by
  apply h.mono m b p
  intro o ho
  rcases ho with ⟨hp, hw, hq, hr, hz⟩
  exact ⟨hp, Nat.add_le_add_left hw _, by simpa [Outcome.add] using hq,
    by simpa [Outcome.add] using hr, by simpa [Outcome.add] using hz⟩

theorem good_metric (m : M → ℝ) (b : Q → Bool) (q : M)
    (next : ℝ → Code M Q R) (P : R → Prop) (w queries : ℕ)
    (h : Sure m b (next (m q)) (Good P w queries)) :
    Sure m b (.metric q next) (Good P (1 + w) (1 + queries)) := by
  apply h.mono m b (next (m q))
  intro o ho
  exact ⟨ho.1, Nat.add_le_add_left ho.2.1 _, by simp [Outcome.add, ho.2.2.1],
    by simp [Outcome.add, ho.2.2.2.1], by simp [Outcome.add, ho.2.2.2.2]⟩

theorem good_coin (m : M → ℝ) (b : Q → Bool) (rate : Rate)
    (next : Bool → Code M Q R) (P : R → Prop) (w queries : ℕ)
    (h : ∀ a, Sure m b (next a) (Good P w queries)) :
    Sure m b (.coin rate next) (Good P (2 + w) queries) := by
  intro a
  apply (h a).mono m b (next a)
  intro o ho
  exact ⟨ho.1, Nat.add_le_add_left ho.2.1 _, by simp [Outcome.add, ho.2.2.1],
    by simp [Outcome.add, ho.2.2.2.1], by simp [Outcome.add, ho.2.2.2.2]⟩

theorem good_bind (m : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (k : R → Code M Q S)
    (P : R → Prop) (P' : S → Prop) (w q w' q' : ℕ)
    (hp : Sure m b p (Good P w q))
    (hk : ∀ r, P r → Sure m b (k r) (Good P' w' q')) :
    Sure m b (p.bind k) (Good P' (w + w') (q + q')) := by
  apply Sure.bind m b p k
  apply hp.mono m b p
  intro a ha
  apply (hk a.value ha.1).mono m b (k a.value)
  intro o ho
  have haW := ha.2.1
  have hoW := ho.2.1
  exact ⟨ho.1, by dsimp [Outcome.combine]; omega,
    by simp [Outcome.combine, ha.2.2.1, ho.2.2.1],
    by simp [Outcome.combine, ha.2.2.2.1, ho.2.2.2.1],
    by simp [Outcome.combine, ha.2.2.2.2, ho.2.2.2.2]⟩

theorem good_bind_value (m : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (k : R → Code M Q S)
    (r : R) (P : S → Prop) (w q w' q' : ℕ)
    (hp : Sure m b p (Good (· = r) w q))
    (hk : Sure m b (k r) (Good P w' q')) :
    Sure m b (p.bind k) (Good P (w + w') (q + q')) :=
  good_bind m b p k (· = r) P w q w' q' hp (fun _ he => he ▸ hk)

theorem evaluate_value_of_good (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (r : R) (w q : ℕ) (h : Sure m b p (Good (· = r) w q)) (F : R → ℝ) :
    p.evaluate m b (fun o => F o.value) = F r := by
  rw [← Code.compile_expect]
  change (p.compile m).law.expect (fun s => F ((((p.compile m).tree s).output b).value)) = _
  have hv := h.compile m b p _
  have he : (fun s => F ((((p.compile m).tree s).output b).value)) = fun _ => F r :=
    funext fun s => congrArg F (hv s).1
  rw [he, Law.expect_const]

theorem evaluate_bind_value (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (k : R → Code M Q S) (F : S → ℝ) :
    (p.bind k).evaluate m b (fun o => F o.value) =
      p.evaluate m b (fun a => (k a.value).evaluate m b (fun o => F o.value)) := by
  rw [Code.evaluate_bind]
  rfl

def fill : (n : ℕ) → Bool → Code M Q (Fin n → Bool)
  | 0, _ => .tick 0 (.pure Fin.elim0)
  | n + 1, bit => .tick 1 ((fill n bit).bind fun tail =>
      .tick 0 (.pure (Fin.cons bit tail)))

theorem fill_good (m : M → ℝ) (b : Q → Bool) (n : ℕ) (bit : Bool) :
    Sure m b (fill n bit : Code M Q _) (Good (· = fun _ => bit) (3 * n + 1) 0) := by
  induction n with
  | zero =>
      apply good_mono m b _ (good_tick m b _ _ _ _ 0 (good_pure m b Fin.elim0))
      · omega
      · intro v hv; subst v; funext j; exact Fin.elim0 j
  | succ n ih =>
      have he : (Fin.cons bit (fun _ : Fin n => bit) : Fin (n + 1) → Bool) =
          fun _ => bit := by
        funext i
        refine Fin.cases rfl (fun _ => rfl) i
      have h := good_bind_value m b (fill n bit)
        (fun tail => .tick 0 (.pure (Fin.cons bit tail))) (fun _ => bit)
        (· = fun _ => bit) (3 * n + 1) 0 1 0 ih (by
          rw [he]
          exact good_tick m b _ _ 0 0 0 (good_pure m b _))
      exact good_mono m b _ (good_tick m b _ _ _ _ 1 h) (by omega) (fun _ h => h)

def count {n : ℕ} (live row : Fin n → Bool) : ℕ :=
  ∑ i, if live i && row i then 1 else 0

def deleted {n : ℕ} (live row : Fin n → Bool) : Fin n → Bool :=
  fun i => live i && !(row i)

/-- Scan the record arrays once. The second returned bitmap is already cleared;
acceptance merely chooses this bitmap, and rejection keeps the old one. -/
def scan : {n : ℕ} → (Fin n → Bool) → (Fin n → Bool) →
    Code M Q (ℕ × (Fin n → Bool))
  | 0, _, _ => .tick 0 (.pure (0, Fin.elim0))
  | _ + 1, live, row => .tick 3
      ((scan (fun i => live i.succ) (fun i => row i.succ)).bind fun v =>
        .tick 11 (.pure
          (v.1 + (if live 0 && row 0 then 1 else 0),
            Fin.cons (live 0 && !(row 0)) v.2)))

theorem scan_good (m : M → ℝ) (b : Q → Bool) {n : ℕ} (live row : Fin n → Bool) :
    Sure m b (scan live row : Code M Q _)
      (Good (· = (count live row, deleted live row)) (16 * n + 1) 0) := by
  induction n with
  | zero =>
      apply good_mono m b _ (good_tick m b _ _ _ _ 0 (good_pure m b (0, Fin.elim0)))
      · omega
      · intro v hv; subst v
        apply Prod.ext
        · simp [count]
        · funext i; exact Fin.elim0 i
  | succ n ih =>
      have he :
          (count (fun i => live i.succ) (fun i => row i.succ) +
              (if live 0 && row 0 then 1 else 0),
            Fin.cons (live 0 && !(row 0))
              (deleted (fun i => live i.succ) (fun i => row i.succ))) =
            (count live row, deleted live row) := by
        apply Prod.ext
        · change count (fun i => live i.succ) (fun i => row i.succ) +
            (if live 0 && row 0 then 1 else 0) = count live row
          simp only [count, Fin.sum_univ_succ]
          omega
        · funext i; refine Fin.cases rfl (fun _ => rfl) i
      let k : (ℕ × (Fin n → Bool)) → Code M Q (ℕ × (Fin (n + 1) → Bool)) := fun v =>
        .tick 11 (.pure (v.1 + (if live 0 && row 0 then 1 else 0),
          Fin.cons (live 0 && !(row 0)) v.2))
      have h := good_bind_value m b (scan (fun i => live i.succ) (fun i => row i.succ)) k
        (count (fun i => live i.succ) (fun i => row i.succ),
          deleted (fun i => live i.succ) (fun i => row i.succ))
        (· = (count live row, deleted live row)) (16 * n + 1) 0 12 0 (ih _ _) (by
          dsimp [k]
          rw [he]
          exact good_tick m b _ _ 0 0 11 (good_pure m b _))
      exact good_mono m b _ (good_tick m b _ _ _ _ 3 h) (by omega) (fun _ h => h)

end SteinerUpperBound.ReusableSample.OracleProgram
