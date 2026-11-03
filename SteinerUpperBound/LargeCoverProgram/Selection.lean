module

public import SteinerUpperBound.LargeCoverProgram.Deterministic

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {V M Q : Type*}

structure Selection (V : Type*) where
  centers : List V
  count : ℕ

def selectionValue : {n : ℕ} → (Fin n → V) → (Fin n → Bool) → Selection V
  | 0, _, _ => ⟨[], 0⟩
  | _ + 1, centers, bits =>
      let tail := selectionValue (fun i => centers i.succ) (fun i => bits i.succ)
      if bits 0 then ⟨centers 0 :: tail.centers, tail.count + 1⟩ else tail

/-- Public-order compaction of the actual acceptance bits. Both the list and
its stored length are built in the charged loop. -/
def selectionProgram : {n : ℕ} → (Fin n → V) → (Fin n → Bool) → Code M Q (Selection V)
  | 0, _, _ => .tick 0 (.pure ⟨[], 0⟩)
  | _ + 1, centers, bits => .tick 3
      ((selectionProgram (fun i => centers i.succ) (fun i => bits i.succ)).bind fun tail =>
        .tick 3 (.pure (if bits 0 then
          ⟨centers 0 :: tail.centers, tail.count + 1⟩ else tail)))

def selectionResult : {n : ℕ} → (Fin n → V) → (Fin n → Bool) → Outcome (Selection V)
  | 0, _, _ => (Outcome.pure ⟨[], 0⟩).add 1 0 0 0
  | _ + 1, centers, bits =>
      let tail := selectionResult (fun i => centers i.succ) (fun i => bits i.succ)
      (tail.map (fun v => if bits 0 then
        ⟨centers 0 :: v.centers, v.count + 1⟩ else v)).add 8 0 0 0

theorem selection_evaluates (m : M → ℝ) (b : Q → Bool) {n : ℕ}
    (centers : Fin n → V) (bits : Fin n → Bool) :
    Code.Evaluates m b (selectionProgram centers bits) (selectionResult centers bits) := by
  induction n with
  | zero => intro F; rfl
  | succ n ih =>
      intro F
      simp only [selectionProgram, Code.evaluate, Code.evaluate_bind]
      rw [ih]
      simp only [Code.evaluate, selectionResult, Outcome.add, Outcome.combine,
        Outcome.pure, Outcome.map, Nat.zero_add, Nat.add_zero, Nat.add_assoc]
      congr 1
      congr 1
      omega

theorem selection_deterministic {n : ℕ} (centers : Fin n → V) (bits : Fin n → Bool) :
    Deterministic (selectionProgram centers bits : Code M Q _) := by
  induction n with
  | zero => trivial
  | succ n ih => exact deterministic_bind _ _ (ih _ _) (fun _ => trivial)

theorem selection_value {n : ℕ} (centers : Fin n → V) (bits : Fin n → Bool) :
    (selectionResult centers bits).value = selectionValue centers bits := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [selectionResult, selectionValue, Outcome.add, Outcome.map, ih]

theorem selection_count {n : ℕ} (centers : Fin n → V) (bits : Fin n → Bool) :
    (selectionValue centers bits).count = ReusableSample.acceptances bits ∧
      (selectionValue centers bits).centers.length = (selectionValue centers bits).count := by
  induction n with
  | zero => simp [selectionValue, ReusableSample.acceptances]
  | succ n ih =>
      have hh := ih (fun i => centers i.succ) (fun i => bits i.succ)
      rw [ReusableSample.acceptances_succ]
      cases hb : bits 0 <;> simp [selectionValue, hb, hh.1, hh.2, Nat.add_comm]

theorem selection_mem {n : ℕ} (centers : Fin n → V) (bits : Fin n → Bool) (x : V) :
    x ∈ (selectionValue centers bits).centers ↔ ∃ i, bits i = true ∧ centers i = x := by
  induction n with
  | zero => simp [selectionValue]
  | succ n ih =>
      simp only [selectionValue, Fin.exists_fin_succ]
      cases hb : bits 0 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte,
        List.mem_cons, ih, false_and, false_or, true_and] <;> aesop

theorem selection_nodup {n : ℕ} (centers : Fin n → V) (hi : Function.Injective centers)
    (bits : Fin n → Bool) : (selectionValue centers bits).centers.Nodup := by
  induction n with
  | zero => simp [selectionValue]
  | succ n ih =>
      have hinj : Function.Injective (fun i : Fin n => centers i.succ) :=
        hi.comp (Fin.succ_injective n)
      have ht := ih (fun i => centers i.succ) hinj (fun i => bits i.succ)
      cases hb : bits 0
      · simpa [selectionValue, hb] using ht
      · simp only [selectionValue, hb, ↓reduceIte, List.nodup_cons]
        refine ⟨?_, ht⟩
        intro hx
        obtain ⟨i, _, he⟩ := (selection_mem _ _ _).mp hx
        have hh := hi he
        exact (Nat.succ_ne_zero i.val) (congrArg Fin.val hh)

theorem selection_resources {n : ℕ} (centers : Fin n → V) (bits : Fin n → Bool) :
    (selectionResult centers bits).work = 8 * n + 1 ∧
      (selectionResult centers bits).metricQueries = 0 ∧
      (selectionResult centers bits).retentionQueries = 0 ∧
      (selectionResult centers bits).positiveReplies = 0 := by
  induction n with
  | zero => simp [selectionResult, Outcome.add, Outcome.pure]
  | succ n ih =>
      have hh := ih (fun i => centers i.succ) (fun i => bits i.succ)
      simp only [selectionResult, Outcome.add, Outcome.map]
      constructor
      · rw [hh.1]; ring
      · simpa only [Nat.zero_add] using hh.2

def lengthProgram (l : List V) : Code M Q ℕ :=
  Code.foldList (fun count _ => .tick 0 (.pure (count + 1))) l 0

def lengthResult (l : List V) : Outcome ℕ :=
  Code.folded (fun count _ => (Outcome.pure (count + 1)).add 1 0 0 0) l 0

theorem length_evaluates (m : M → ℝ) (b : Q → Bool) (l : List V) :
    Code.Evaluates m b (lengthProgram l) (lengthResult l) :=
  Code.foldList_evaluates m b _ _ (fun count _ => fun _ => rfl) l 0

theorem length_deterministic (l : List V) :
    Deterministic (lengthProgram l : Code M Q _) :=
  deterministic_foldList (fun (count : ℕ) (_ : V) => .tick 0 (.pure (count + 1)))
    (fun _ _ => trivial) l 0

theorem length_result (l : List V) :
    (lengthResult l).value = l.length ∧ (lengthResult l).work = 2 * l.length ∧
      (lengthResult l).metricQueries = 0 ∧ (lengthResult l).retentionQueries = 0 ∧
      (lengthResult l).positiveReplies = 0 := by
  have he : ∀ (l : List V) (c : ℕ),
      Code.folded (fun count (_ : V) => (Outcome.pure (count + 1)).add 1 0 0 0) l c =
        ⟨c + l.length, 2 * l.length, 0, 0, 0⟩ := by
    intro l
    induction l with
    | nil => intro c; rfl
    | cons x l ih =>
        intro c
        rw [Code.folded, ih]
        simp only [Outcome.add, Outcome.combine, Outcome.pure, List.length_cons]
        congr 1 <;> omega
  simp [lengthResult, he]

end SteinerUpperBound.LargeCoverProgram
