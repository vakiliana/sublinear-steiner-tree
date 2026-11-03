module

public import SteinerLowerBound.RetainedProtocol

@[expose] public section

namespace SteinerLowerBound.Simulation

open scoped Classical

variable {X Y Z : Type*}

def bind (t : DecisionTree X Bool Y) (k : Y → DecisionTree X Bool Z) :
    DecisionTree X Bool Z :=
  match t with
  | .leaf y => k y
  | .query x next => .query x (fun b => bind (next b) k)

theorem output_bind (t : DecisionTree X Bool Y) (k : Y → DecisionTree X Bool Z)
    (o : X → Bool) : (bind t k).output o = (k (t.output o)).output o := by
  induction t with
  | leaf => rfl
  | query x next ih => exact ih (o x)

structure Cache (X : Type*) where
  read : Finset X
  kept : Finset X

def Cache.empty : Cache X := ⟨∅, ∅⟩

noncomputable def Cache.record (s : Cache X) (x : X) (b : Bool) : Cache X :=
  ⟨insert x s.read, if b then insert x s.kept else s.kept⟩

def Cache.Consistent (s : Cache X) (o : X → Bool) : Prop :=
  s.kept ⊆ s.read ∧ ∀ x ∈ s.read, (x ∈ s.kept ↔ o x = true)

theorem Cache.empty_consistent (o : X → Bool) : Cache.empty.Consistent o := by
  simp [Consistent, empty]

theorem Cache.record_consistent (s : Cache X) (o : X → Bool) (x : X)
    (hs : s.Consistent o) (hx : x ∉ s.read) :
    (s.record x (o x)).Consistent o := by
  classical
  have hxk : x ∉ s.kept := fun h => hx (hs.1 h)
  constructor
  · intro y hy
    by_cases hb : o x = true
    · simp only [record, hb, ↓reduceIte, Finset.mem_insert] at hy ⊢
      exact hy.imp_right (fun hy => hs.1 hy)
    · simp only [record, hb, Bool.false_eq_true, ↓reduceIte] at hy
      exact Finset.mem_insert_of_mem (hs.1 hy)
  · intro y hy
    by_cases hyx : y = x
    · subst y
      cases hb : o x <;> simp [record, hb, hxk]
    · have hyr : y ∈ s.read := by
        simpa only [record, Finset.mem_insert, hyx, false_or] using hy
      cases hb : o x <;> simpa [record, hb, hyx] using hs.2 y hyr

theorem Cache.read_subset_record (s : Cache X) (x : X) (b : Bool) :
    s.read ⊆ (s.record x b).read := Finset.subset_insert _ _

theorem Cache.kept_subset_record (s : Cache X) (x : X) (b : Bool) :
    s.kept ⊆ (s.record x b).kept := by
  cases b <;> simp [record]

theorem Cache.record_kept_card (s : Cache X) (x : X) (b : Bool) :
    (s.record x b).kept.card ≤ s.kept.card + if b then 1 else 0 := by
  cases b
  · simp [record]
  · simpa [record] using Finset.card_insert_le x s.kept

def Spec (get : Y → Cache X) (P : Y → Prop) (s : Cache X) :
    DecisionTree X Bool Y → Prop
  | .leaf y => get y = s ∧ P y
  | .query x next => x ∉ s.read ∧ ∀ b, Spec get P (s.record x b) (next b)

theorem Spec.mono (get : Y → Cache X) (P P' : Y → Prop) (s : Cache X)
    (t : DecisionTree X Bool Y) (ht : Spec get P s t)
    (h : ∀ y, P y → P' y) : Spec get P' s t := by
  induction t generalizing s with
  | leaf y => exact ⟨ht.1, h y ht.2⟩
  | query x next ih => exact ⟨ht.1, fun b => ih b _ (ht.2 b)⟩

theorem Spec.bind (get : Y → Cache X) (get' : Z → Cache X)
    (P : Y → Prop) (P' : Z → Prop) (s : Cache X)
    (t : DecisionTree X Bool Y) (k : Y → DecisionTree X Bool Z)
    (ht : Spec get P s t)
    (hk : ∀ y, P y → Spec get' P' (get y) (k y)) :
    Spec get' P' s (Simulation.bind t k) := by
  induction t generalizing s with
  | leaf y => simpa only [Simulation.bind, ht.1] using hk y ht.2
  | query x next ih => exact ⟨ht.1, fun b => ih b _ (ht.2 b)⟩

theorem Spec.output (get : Y → Cache X) (P : Y → Prop) (s : Cache X)
    (t : DecisionTree X Bool Y) (ht : Spec get P s t) (o : X → Bool) :
    P (t.output o) := by
  induction t generalizing s with
  | leaf => exact ht.2
  | query x next ih => exact ih (o x) _ (ht.2 (o x))

theorem Spec.consistent (get : Y → Cache X) (P : Y → Prop) (s : Cache X)
    (t : DecisionTree X Bool Y) (ht : Spec get P s t) (o : X → Bool)
    (hs : s.Consistent o) : (get (t.output o)).Consistent o := by
  induction t generalizing s with
  | leaf y => simpa only [DecisionTree.output, ht.1] using hs
  | query x next ih =>
      exact ih (o x) _ (ht.2 (o x)) (s.record_consistent o x hs ht.1)

theorem Spec.monotone (get : Y → Cache X) (P : Y → Prop) (s : Cache X)
    (t : DecisionTree X Bool Y) (ht : Spec get P s t) (o : X → Bool) :
    s.read ⊆ (get (t.output o)).read ∧ s.kept ⊆ (get (t.output o)).kept := by
  induction t generalizing s with
  | leaf y => simp only [DecisionTree.output, ht.1, Finset.Subset.refl, and_self]
  | query x next ih =>
      obtain ⟨hr, hk⟩ := ih (o x) _ (ht.2 (o x))
      exact ⟨(s.read_subset_record x (o x)).trans hr,
        (s.kept_subset_record x (o x)).trans hk⟩

theorem Spec.valid {V : Type*} (D : Finset V → Finset X) (cap : Finset V → Prop)
    (get : Y → Cache X) (P : Y → Prop) (s : Cache X)
    (t : DecisionTree X Bool Y) (ht : Spec get P s t)
    (hP : ∀ y, P y → ∃ Q, cap Q ∧ (get y).read ⊆ D Q) :
    Protocol.Valid D cap s.read t := by
  induction t generalizing s with
  | leaf y =>
      change ∃ Q, cap Q ∧ s.read ⊆ D Q
      simpa only [ht.1] using hP y ht.2
  | query x next ih => exact ⟨ht.1, fun b => ih b _ (ht.2 b)⟩

def retainedRead : DecisionTree X Bool Y → (X → Bool) → ℕ
  | .leaf _, _ => 0
  | .query x next, o => (if o x then 1 else 0) + retainedRead (next (o x)) o

theorem Spec.kept_card (get : Y → Cache X) (P : Y → Prop) (s : Cache X)
    (t : DecisionTree X Bool Y) (ht : Spec get P s t) (o : X → Bool) :
    (get (t.output o)).kept.card ≤ s.kept.card + retainedRead t o := by
  induction t generalizing s with
  | leaf y => simp [DecisionTree.output, ht.1, retainedRead]
  | query x next ih =>
      have hi := ih (o x) _ (ht.2 (o x))
      have hc := s.record_kept_card x (o x)
      simp only [DecisionTree.output, retainedRead]
      omega

theorem output_lift (t : DecisionTree X Bool Y) (o : X → Option Bool) :
    (RetainedProtocol.lift t).output o = t.output (fun x => RetainedProtocol.retained (o x)) := by
  induction t with
  | leaf => rfl
  | query x next ih => exact ih (RetainedProtocol.retained (o x))

theorem retainedRead_le_proposals (t : DecisionTree X Bool Y) (o : X → Option Bool) :
    retainedRead t (fun x => RetainedProtocol.retained (o x)) ≤
      ProposalProtocol.proposalsRead (RetainedProtocol.lift t) o := by
  induction t with
  | leaf => exact Nat.le_refl _
  | query x next ih =>
      have hi := ih (RetainedProtocol.retained (o x))
      cases hb : o x with
      | none => simpa [retainedRead, RetainedProtocol.lift,
          ProposalProtocol.proposalsRead, hb, RetainedProtocol.retained] using hi
      | some b =>
          cases b
          · simp only [hb, RetainedProtocol.retained] at hi
            simpa [retainedRead, RetainedProtocol.lift,
              ProposalProtocol.proposalsRead, hb, RetainedProtocol.retained] using
              hi.trans (Nat.le_add_left _ 1)
          · simp only [hb, RetainedProtocol.retained] at hi
            simpa [retainedRead, RetainedProtocol.lift,
              ProposalProtocol.proposalsRead, hb, RetainedProtocol.retained] using
              Nat.add_le_add_left hi 1

theorem valid_map {A V : Type*} [Fintype A] (D : Finset V → Finset X)
    (cap : Finset V → Prop) (I : Finset X) (t : DecisionTree X A Y)
    (ht : Protocol.Valid D cap I t) (f : Y → Z) :
    Protocol.Valid D cap I (t.map f) := by
  induction t generalizing I with
  | leaf => exact ht
  | query x next ih => exact ⟨ht.1, fun a => ih a _ (ht.2 a)⟩

theorem valid_mono_cap {A V : Type*} [Fintype A] (D : Finset V → Finset X)
    (cap cap' : Finset V → Prop) (I : Finset X) (t : DecisionTree X A Y)
    (ht : Protocol.Valid D cap I t) (hcap : ∀ Q, cap Q → cap' Q) :
    Protocol.Valid D cap' I t := by
  induction t generalizing I with
  | leaf =>
      obtain ⟨Q, hQ, hI⟩ := ht
      exact ⟨Q, hcap Q hQ, hI⟩
  | query x next ih => exact ⟨ht.1, fun a => ih a _ (ht.2 a)⟩

theorem retainedRead_map (t : DecisionTree X Bool Y) (f : Y → Z) (o : X → Bool) :
    retainedRead (t.map f) o = retainedRead t o := by
  induction t with
  | leaf => rfl
  | query x next ih => simp only [DecisionTree.map, retainedRead, ih]

end SteinerLowerBound.Simulation
