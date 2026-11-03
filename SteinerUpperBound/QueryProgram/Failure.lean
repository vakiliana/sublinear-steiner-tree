module

public import SteinerUpperBound.QueryProgram.MetricSimulation

@[expose] public section

namespace SteinerUpperBound.QueryProgram.Code

open SteinerLowerBound
open scoped Classical

variable {M Q R S : Type*}

noncomputable def valueProbability (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (P : R → Prop) : ℝ :=
  p.evaluate m bits (fun o => if P o.value then 1 else 0)

theorem valueProbability_nonneg (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R) (P : R → Prop) :
    0 ≤ valueProbability m bits p P :=
  evaluate_nonneg m bits p (fun _ => by split_ifs <;> norm_num)

theorem valueProbability_le_one (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R) (P : R → Prop) :
    valueProbability m bits p P ≤ 1 := by
  have h := evaluate_mono m bits p
    (F := fun o => if P o.value then (1 : ℝ) else 0) (G := fun _ => 1)
    (fun _ => by split_ifs <;> norm_num)
  simpa only [valueProbability, evaluate_const] using h

theorem valueProbability_bind (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (k : R → Code M Q S) (P : S → Prop) :
    valueProbability m bits (p.bind k) P =
      p.evaluate m bits (fun o => valueProbability m bits (k o.value) P) := by
  unfold valueProbability
  rw [evaluate_bind]
  rfl

theorem evaluate_const_mul (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (c : ℝ) (F : Outcome R → ℝ) :
    p.evaluate m bits (fun o => c * F o) = c * p.evaluate m bits F := by
  rw [← compile_expect m bits p (fun o => c * F o), ← compile_expect m bits p F]
  exact Law.expect_const_mul _ _ _

theorem bind_success (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (k : R → Code M Q S) (P : R → Prop) (T : S → Prop) (delta epsilon : ℝ)
    (hd : 0 ≤ delta) (he : 0 ≤ epsilon)
    (hp : 1 - delta ≤ valueProbability m bits p P)
    (hk : ∀ r, P r → 1 - epsilon ≤ valueProbability m bits (k r) T) :
    1 - delta - epsilon ≤ valueProbability m bits (p.bind k) T := by
  by_cases he₁ : epsilon ≤ 1
  · have hpoint (o : Outcome R) :
        (1 - epsilon) * (if P o.value then (1 : ℝ) else 0) ≤
          valueProbability m bits (k o.value) T := by
      by_cases h : P o.value
      · simpa only [h, ite_true, mul_one] using hk o.value h
      · simpa only [h, ite_false, mul_zero] using valueProbability_nonneg m bits (k o.value) T
    have hmono := evaluate_mono m bits p hpoint
    rw [evaluate_const_mul, ← valueProbability_bind] at hmono
    change (1 - epsilon) * valueProbability m bits p P ≤ _ at hmono
    have hmul := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr he₁)
    have hprod := mul_nonneg hd he
    nlinarith
  · have hn := valueProbability_nonneg m bits (p.bind k) T
    linarith

theorem foldList_success {A : Type*} (m : M → ℝ) (bits : Q → Bool)
    (body : R → A → Code M Q R) (P : R → Prop) (error : A → ℝ)
    (l : List A) (s : R) (hs : P s) (he : ∀ a ∈ l, 0 ≤ error a)
    (hstep : ∀ r, P r → ∀ a ∈ l, 1 - error a ≤ valueProbability m bits (body r a) P) :
    1 - (l.map error).sum ≤ valueProbability m bits (foldList body l s) P := by
  induction l generalizing s with
  | nil => simp [foldList, valueProbability, evaluate, Outcome.pure, hs]
  | cons a l ih =>
      have htail : 0 ≤ (l.map error).sum := by
        apply List.sum_nonneg
        intro x hx
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
        exact he b (List.mem_cons_of_mem _ hb)
      have hk (r : R) (hr : P r) :
          1 - (l.map error).sum ≤ valueProbability m bits (foldList body l r) P :=
        ih r hr (fun b hb => he b (List.mem_cons_of_mem _ hb))
          (fun r hr b hb => hstep r hr b (List.mem_cons_of_mem _ hb))
      have hb := bind_success m bits (body s a) (fun r => foldList body l r) P P
        (error a) (l.map error).sum (he a List.mem_cons_self) htail
        (hstep s hs a List.mem_cons_self) hk
      change 1 - (error a + (l.map error).sum) ≤
        valueProbability m bits ((body s a).bind (fun r => foldList body l r)) P
      rw [sub_add_eq_sub_sub]
      exact hb

theorem work_tail (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R) (budget : ℕ) :
    p.evaluate m bits (fun o => if budget < o.work then (1 : ℝ) else 0) ≤
      p.evaluate m bits (fun o => (o.work : ℝ)) / (budget + 1 : ℕ) := by
  let c := p.compile m
  have hmark := c.law.markov
    (f := fun s => ((((c.tree s).output bits).work : ℕ) : ℝ)) (fun _ => Nat.cast_nonneg _)
    (show (0 : ℝ) < ((budget + 1 : ℕ) : ℝ) by positivity)
  have heq : c.law.prob {s | ((budget + 1 : ℕ) : ℝ) ≤ (((c.tree s).output bits).work : ℝ)} =
      c.expect bits (fun o => if budget < o.work then (1 : ℝ) else 0) := by
    rw [Law.prob_eq_expect]
    apply congrArg c.law.expect
    funext s
    have hiff : ((budget + 1 : ℕ) : ℝ) ≤ (((c.tree s).output bits).work : ℝ) ↔
        budget < ((c.tree s).output bits).work := by
      norm_cast <;> omega
    simp only [Set.mem_setOf_eq, hiff]
  rw [heq, compile_expect] at hmark
  have hcost : c.law.expect (fun s => ((((c.tree s).output bits).work : ℕ) : ℝ)) =
      p.evaluate m bits (fun o => (o.work : ℝ)) := by
    change (p.compile m).expect bits (fun o => (o.work : ℝ)) = _
    exact compile_expect m bits p _
  rw [hcost] at hmark
  exact hmark

def SomeGood (P : R → Prop) (r : Option R) : Prop :=
  ∃ x, r = some x ∧ P x

theorem some_indicator (P : R → Prop) (r : Option R) :
    (if SomeGood P r then (1 : ℝ) else 0) = r.elim 0 (fun x => if P x then 1 else 0) := by
  cases r <;> simp [SomeGood]

theorem cap_success_eq (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (budget : ℕ) (P : R → Prop) :
    valueProbability m bits (p.cap budget) (SomeGood P) =
      p.evaluate m bits (fun o => if o.work ≤ budget then (if P o.value then 1 else 0) else 0) := by
  unfold valueProbability
  have hfun : (fun o : Outcome (Option R) => if SomeGood P o.value then (1 : ℝ) else 0) =
      (fun o => o.value.elim 0 (fun x => if P x then 1 else 0)) := by
    funext o
    exact some_indicator P o.value
  rw [hfun, cap_expect]

theorem evaluate_sub (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (F G : Outcome R → ℝ) :
    p.evaluate m bits (fun o => F o - G o) = p.evaluate m bits F - p.evaluate m bits G := by
  rw [← compile_expect m bits p (fun o => F o - G o),
    ← compile_expect m bits p F, ← compile_expect m bits p G]
  exact Law.expect_sub _ _ _

theorem cap_success (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (budget : ℕ) (P : R → Prop) :
    valueProbability m bits p P - p.evaluate m bits (fun o => (o.work : ℝ)) / (budget + 1 : ℕ) ≤
      valueProbability m bits (p.cap budget) (SomeGood P) := by
  have hpoint (o : Outcome R) :
      (if P o.value then (1 : ℝ) else 0) - (if budget < o.work then 1 else 0) ≤
        if o.work ≤ budget then (if P o.value then 1 else 0) else 0 := by
    by_cases hp : P o.value <;> by_cases hw : o.work ≤ budget <;>
      simp_all <;> split_ifs <;> norm_num
  have h := evaluate_mono m bits p hpoint
  rw [evaluate_sub, ← cap_success_eq] at h
  have ht := work_tail m bits p budget
  change valueProbability m bits p P -
    p.evaluate m bits (fun o => if budget < o.work then 1 else 0) ≤ _ at h
  linarith

theorem valueProbability_map (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (f : R → S) (P : S → Prop) :
    valueProbability m bits (p.map f) P = valueProbability m bits p (fun r => P (f r)) := by
  unfold valueProbability
  rw [evaluate_map]
  rfl

end SteinerUpperBound.QueryProgram.Code
