module

public import SteinerLowerBound.MetricComparison
public import SteinerLowerBound.DeferredSampling
public import SteinerLowerBound.Screening.Exchange

@[expose] public section

namespace SteinerLowerBound.MetricComparison.Compiler

open scoped BigOperators Classical

structure Decoder (Q A C S : Type*) where
  shape : Q → A ⊕ (C × S)
  respond : Bool → A
  contact_unique : ∀ q q' c u,
    shape q = .inr (c, u) → shape q' = .inr (c, u) → q = q'

namespace Decoder

variable {Q A C S Z : Type*}

def reply (D : Decoder Q A C S) (q : Q) (b : Bool) : A :=
  (D.shape q).elim id (fun _ => D.respond b)

def step (D : Decoder Q A C S) (t : DecisionTree Q A Z) (b : Bool) :
    DecisionTree Q A Z :=
  match t with
  | .leaf r => .leaf r
  | .query q next => next (D.reply q b)

def replay (D : Decoder Q A C S) (t : DecisionTree Q A Z) :
    List Bool → DecisionTree Q A Z
  | [] => t
  | b :: rest => D.replay (D.step t b) rest

theorem replay_append (D : Decoder Q A C S) (t : DecisionTree Q A Z)
    (l : List Bool) (b : Bool) :
    D.replay t (l ++ [b]) = D.step (D.replay t l) b := by
  induction l generalizing t with
  | nil => rfl
  | cons a l ih => exact ih (D.step t a)

def request (D : Decoder Q A C S) : DecisionTree Q A Z → Option (C × S)
  | .leaf _ => none
  | .query q _ => (D.shape q).getRight?

noncomputable def schedule (D : Decoder Q A C S) (root : DecisionTree Q A Z)
    (x : Control C (History S)) : Option (C × S) :=
  match D.request (D.replay root x.past) with
  | none => none
  | some (c, u) => if (x.history c).Fresh u then some (c, u) else none

theorem schedule_nonrepeating (D : Decoder Q A C S) (root : DecisionTree Q A Z) :
    Control.Nonrepeating (History.memory S) (D.schedule root) := by
  classical
  intro x _ c u he
  unfold schedule at he
  split at he
  · contradiction
  · rename_i c' u' hr
    split_ifs at he with hf
    · have hcu := Option.some.inj he
      cases hcu
      exact hf

variable [Fintype A]

def Invariant (D : Decoder Q A C S) (t : DecisionTree Q A Z)
    (x : Control C (History S)) : Prop :=
  t.NoRepeats ∧ ∀ c u, u ∈ (x.history c).positive ∨ u ∈ (x.history c).negative →
    ∀ q ∈ t.used, D.shape q ≠ .inr (c, u)

theorem invariant_initial (D : Decoder Q A C S) (t : DecisionTree Q A Z)
    (ht : t.NoRepeats) :
    D.Invariant t (Control.initial (History.memory S)) := by
  refine ⟨ht, ?_⟩
  intro c u hu
  simpa only [Control.initial, History.initial, Finset.notMem_empty, or_self] using hu

theorem invariant_fresh (D : Decoder Q A C S) (q : Q) (next : A → DecisionTree Q A Z)
    (x : Control C (History S)) (hi : D.Invariant (.query q next) x)
    (c : C) (u : S) (hq : D.shape q = .inr (c, u)) : (x.history c).Fresh u := by
  constructor
  · intro hu
    exact hi.2 c u (Or.inl hu) q (Finset.mem_insert_self _ _) hq
  · intro hu
    exact hi.2 c u (Or.inr hu) q (Finset.mem_insert_self _ _) hq

theorem schedule_eq_request (D : Decoder Q A C S) (root : DecisionTree Q A Z)
    (x : Control C (History S)) (hi : D.Invariant (D.replay root x.past) x) :
    D.schedule root x = D.request (D.replay root x.past) := by
  classical
  cases he : D.replay root x.past with
  | leaf r => simp [schedule, he, request]
  | query q next =>
    have hi' : D.Invariant (.query q next) x := he ▸ hi
    cases hq : D.shape q with
    | inl a => simp [schedule, he, request, hq]
    | inr cu =>
      rcases cu with ⟨c, u⟩
      have hf := D.invariant_fresh q next x hi' c u hq
      simp [schedule, he, request, hq, hf]

theorem branch_used_subset (q : Q) (next : A → DecisionTree Q A Z) (a : A) :
    (next a).used ⊆ (DecisionTree.query q next).used := by
  intro r hr
  exact Finset.mem_insert_of_mem
    (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hr⟩)

theorem mem_history_update (h : History S) (u v : S) (b : Bool) :
    v ∈ (h.update u b).positive ∨ v ∈ (h.update u b).negative ↔
      v = u ∨ v ∈ h.positive ∨ v ∈ h.negative := by
  classical
  cases b <;> simp only [History.update, Bool.false_eq_true, ↓reduceIte,
    Finset.mem_insert] <;> tauto

theorem invariant_advance (D : Decoder Q A C S) (root : DecisionTree Q A Z)
    (x : Control C (History S)) (hi : D.Invariant (D.replay root x.past) x) (b : Bool) :
    D.Invariant (D.replay root
      (Control.advance (History.memory S) (D.schedule root) x b).past)
      (Control.advance (History.memory S) (D.schedule root) x b) := by
  classical
  have hs := D.schedule_eq_request root x hi
  change D.Invariant (D.replay root (x.past ++ [b])) _
  rw [D.replay_append]
  cases he : D.replay root x.past with
  | leaf r =>
    have hnone : D.schedule root x = none := by simpa only [he, request] using hs
    simp [he, step, Invariant, DecisionTree.NoRepeats, DecisionTree.used]
  | query q next =>
    have hi' : D.Invariant (.query q next) x := he ▸ hi
    refine ⟨hi'.1.1 _, ?_⟩
    intro c u hu r hr
    have hold (hmem : u ∈ (x.history c).positive ∨ u ∈ (x.history c).negative) :
        D.shape r ≠ .inr (c, u) :=
      hi'.2 c u hmem r (branch_used_subset q next _ hr)
    cases hq : D.shape q with
    | inl a =>
      have hnone : D.schedule root x = none := by
        simpa only [he, request, hq, Sum.getRight?] using hs
      simp only [Control.advance, hnone] at hu
      exact hold hu
    | inr cu =>
      rcases cu with ⟨c', u'⟩
      have hsome : D.schedule root x = some (c', u') := by
        simpa only [he, request, hq, Sum.getRight?] using hs
      simp only [Control.advance, hsome] at hu
      by_cases hc : c = c'
      · subst c
        rw [Function.update_self, mem_history_update] at hu
        rcases hu with hu | hu
        · subst u
          intro heq
          have hrq : r = q := D.contact_unique r q c' u' heq hq
          subst r
          exact hi'.1.2 _ hr
        · exact hold hu
      · simp only [Function.update_of_ne hc] at hu
        exact hold hu

def contacts (D : Decoder Q A C S) (h : List Q) : List (C × S) :=
  h.filterMap (fun q => (D.shape q).getRight?)

@[simp]
theorem contacts_append (D : Decoder Q A C S) (h : List Q) (q : Q) :
    D.contacts (h ++ [q]) =
      D.contacts h ++ ((D.shape q).getRight?).toList := by
  simp only [contacts, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases D.shape q <;> rfl

def publicAnswer (D : Decoder Q A C S)
    (oracle : List (C × S) → C × S → Bool) (h : List Q) (q : Q) : A :=
  match D.shape q with
  | .inl a => a
  | .inr cu => D.respond (oracle (D.contacts h) cu)

noncomputable def binaryRun (D : Decoder Q A C S)
    (oracle : List (C × S) → C × S → Bool) (root : DecisionTree Q A Z) :
    (n : ℕ) → Control C (History S) → List (C × S) → Answers n
  | 0, _, _ => ()
  | n + 1, x, h =>
    let b := match D.schedule root x with
      | none => false
      | some cu => oracle h cu
    let h' := h ++ (D.schedule root x).toList
    (b, D.binaryRun oracle root n
      (Control.advance (History.memory S) (D.schedule root) x b) h')

abbrev Report (Q A Z : Type*) (n : ℕ) :=
  (Fin n → Option (Q × A)) × Option Z

def emptyReport (r : Z) (n : ℕ) : Report Q A Z n := (fun _ => none, some r)

def prependReport (q : Q) (a : A) {n : ℕ} (r : Report Q A Z n) : Report Q A Z (n + 1) :=
  (Fin.cases (some (q, a)) r.1, r.2)

noncomputable def decodeReport (D : Decoder Q A C S) :
    (n : ℕ) → DecisionTree Q A Z → Answers n → Report Q A Z n
  | _, .leaf r, _ => emptyReport r _
  | 0, .query _ _, _ => (Fin.elim0, none)
  | n + 1, .query q next, a =>
      prependReport q (D.reply q a.1) (D.decodeReport n (next (D.reply q a.1)) a.2)

noncomputable def execute (D : Decoder Q A C S)
    (oracle : List (C × S) → C × S → Bool) :
    (n : ℕ) → DecisionTree Q A Z → List Q → Report Q A Z n
  | _, .leaf r, _ => emptyReport r _
  | 0, .query _ _, _ => (Fin.elim0, none)
  | n + 1, .query q next, h =>
      let a := D.publicAnswer oracle h q
      prependReport q a (D.execute oracle n (next a) (h ++ [q]))

theorem execute_eq_projection (D : Decoder Q A C S)
    (oracle : List (C × S) → C × S → Bool) (root : DecisionTree Q A Z)
    (n : ℕ) (x : Control C (History S)) (h : List Q)
    (hi : D.Invariant (D.replay root x.past) x) :
    D.decodeReport n (D.replay root x.past)
      (D.binaryRun oracle root n x (D.contacts h)) =
        D.execute oracle n (D.replay root x.past) h := by
  induction n generalizing x h with
  | zero =>
    cases D.replay root x.past <;> rfl
  | succ n ih =>
    have hs := D.schedule_eq_request root x hi
    cases he : D.replay root x.past with
    | leaf r => simp only [he, decodeReport, execute]
    | query q next =>
      cases hq : D.shape q with
      | inl a =>
        have hnone : D.schedule root x = none := by
          simpa only [he, request, hq, Sum.getRight?] using hs
        have hn := ih (Control.advance (History.memory S) (D.schedule root) x false)
          (h ++ [q]) (D.invariant_advance root x hi false)
        have hreplay :
            D.replay root (Control.advance (History.memory S) (D.schedule root) x false).past =
              next a := by
          change D.replay root (x.past ++ [false]) = _
          rw [D.replay_append, he]
          simp only [step, reply, hq, Sum.elim_inl, id_eq]
        simp only [hreplay, contacts_append, hq, Sum.getRight?, Option.toList_none,
          List.append_nil] at hn
        simp only [he, binaryRun, hnone, Option.toList_none, List.append_nil,
          decodeReport, reply, hq, Sum.elim_inl, id_eq, execute, publicAnswer]
        exact congrArg (prependReport q a) hn
      | inr cu =>
        rcases cu with ⟨c, u⟩
        have hsome : D.schedule root x = some (c, u) := by
          simpa only [he, request, hq, Sum.getRight?] using hs
        let b := oracle (D.contacts h) (c, u)
        have hn := ih (Control.advance (History.memory S) (D.schedule root) x b)
          (h ++ [q]) (D.invariant_advance root x hi b)
        have hreplay :
            D.replay root (Control.advance (History.memory S) (D.schedule root) x b).past =
              next (D.respond b) := by
          change D.replay root (x.past ++ [b]) = _
          rw [D.replay_append, he]
          simp only [step, reply, hq, Sum.elim_inr]
        simp only [hreplay, contacts_append, hq, Sum.getRight?, Option.toList_some] at hn
        simp only [he, binaryRun, hsome, Option.toList_some,
          decodeReport, reply, hq, Sum.elim_inr, execute, publicAnswer]
        exact congrArg (prependReport q (D.respond b)) hn

end Decoder

end SteinerLowerBound.MetricComparison.Compiler
