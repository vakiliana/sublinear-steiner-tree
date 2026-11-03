module

public import SteinerUpperBound.Matching.Padded.Sort

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E}

structure Entry (S : Slots G) (Q : ℕ) where
  source : Slot S.length
  reverse : Slot S.length
  edge : E
  rank : Fin Q

structure Cache (S : Slots G) (Q : ℕ) where
  level : V → ℕ
  assigned : E → Option (Fin Q)
  stored : Slot S.length → Option (Fin Q)
  known : V → List (Entry S Q)
  ready : V → Array (Entry S Q)
  prepared : V → Bool
  requests : V → ℕ

namespace Cache

variable (S : Slots G) (Q : ℕ)

def empty : Cache S Q :=
  ⟨fun _ => 0, fun _ => none, fun _ => none, fun _ => [], fun _ => #[], fun _ => false,
    fun _ => 0⟩

def boundary (s : Cache S Q) (v : V) : ℕ := Buckets.bound (s.level v)

def lower (s : Cache S Q) (e : E) : ℕ :=
  max (boundary S Q s (G.left e)) (boundary S Q s (G.right e))

noncomputable def assign (s : Cache S Q) (source reverse : Slot S.length) (e : E) (r : Fin Q) :
    Cache S Q :=
  { s with
    assigned := Function.update s.assigned e (some r)
    stored := Function.update (Function.update s.stored source (some r)) reverse (some r)
    known := Function.update
      (Function.update s.known source.1 (⟨source, reverse, e, r⟩ :: s.known source.1))
      reverse.1 (⟨reverse, source, e, r⟩ :: s.known reverse.1) }

def Compatible (s : Cache S Q) : Prop :=
  ∀ d : Directed E, s.stored (S.place d) = s.assigned d.1

theorem empty_compatible : Compatible S Q (empty S Q) := fun _ => rfl

theorem equal_or_reverse {d d' : Directed E} (h : d.1 = d'.1) :
    d = d' ∨ d = Padded.reverse d' := by
  cases d with
  | mk e b =>
    cases d' with
    | mk e' b' =>
      dsimp only at h
      subst e'
      cases b <;> cases b' <;> simp [Padded.reverse]

theorem assign_compatible (s : Cache S Q) (hs : Compatible S Q s)
    (source reverse : Slot S.length) (e : E) (r : Fin Q)
    (ht : S.test source = some (e, reverse)) :
    Compatible S Q (assign S Q s source reverse e r) := by
  classical
  obtain ⟨d0, hplace, hedge, hreverse⟩ := S.test_complete source e reverse ht
  have hne : source ≠ reverse := by
    intro heq
    exact (S.test_incident ht).2.2 (congrArg Sigma.fst heq)
  intro d
  by_cases he : d.1 = e
  · have hd : S.place d = source ∨ S.place d = reverse := by
      rcases equal_or_reverse (he.trans hedge.symm) with h | h
      · exact Or.inl (h ▸ hplace)
      · exact Or.inr (h ▸ hreverse)
    rcases hd with hd | hd <;>
      simp [assign, he, hd, Function.update_of_ne hne]
  · have hd0 : S.place d ≠ source := by
      intro hp
      have hdd := S.place_injective (hp.trans hplace.symm)
      exact he ((congrArg Prod.fst hdd).trans hedge)
    have hdr : S.place d ≠ reverse := by
      intro hp
      have hdd := S.place_injective (hp.trans hreverse.symm)
      exact he ((congrArg Prod.fst hdd).trans hedge)
    simpa [assign, Function.update_of_ne hd0, Function.update_of_ne hdr,
      Function.update_of_ne he] using hs d

theorem reverse_stored (s : Cache S Q) (hs : Compatible S Q s)
    {source reverse : Slot S.length} {e : E} (ht : S.test source = some (e, reverse)) :
    s.stored source = s.stored reverse := by
  obtain ⟨d, hd, he, hr⟩ := S.test_complete source e reverse ht
  rw [← hd, ← hr, hs d, hs (Padded.reverse d)]
  rfl

theorem assign_extends (s : Cache S Q) (source reverse : Slot S.length) (e : E) (r : Fin Q)
    (hn : s.assigned e = none) (f : E) (a : Fin Q) (ha : s.assigned f = some a) :
    (assign S Q s source reverse e r).assigned f = some a := by
  have hfe : f ≠ e := by
    intro h
    subst f
    rw [hn] at ha
    cases ha
  simpa only [assign, Function.update_of_ne hfe] using ha

theorem assign_levels (s : Cache S Q) (source reverse : Slot S.length) (e : E) (r : Fin Q) :
    (assign S Q s source reverse e r).level = s.level := rfl

variable (hQ : 0 < Q)

noncomputable def completion [Fintype E] (s : Cache S Q) : Law (E → Fin Q) :=
  Law.pi fun e =>
    match s.assigned e with
    | some r => Law.pure r
    | none => Range.law Q hQ (lower S Q s e) Q

def Consistent (s : Cache S Q) (ranks : E → Fin Q) : Prop :=
  (∀ e r, s.assigned e = some r → ranks e = r) ∧
    ∀ e v, G.Incident e v → (ranks e).val < boundary S Q s v →
      s.assigned e = some (ranks e)

def Legal (s : Cache S Q) : Prop :=
  (∀ v, boundary S Q s v ≤ Q) ∧
    ∀ e, s.assigned e = none → lower S Q s e < Q

theorem empty_legal (hQ : 0 < Q) : Legal S Q (empty S Q) := by
  simp [Legal, empty, boundary, lower, hQ.le, hQ]

/-- Only selected indices are tested. Assignments are buffered until the bucket commits. -/
noncomputable def selectedStep (a b : ℕ) (v : V) (i : ℕ) (s : Cache S Q) :
    Program (Command S) (Option (Entry S Q)) :=
  if hi : i < S.length v then
    let source : Slot S.length := ⟨v, ⟨i, hi⟩⟩
    (Command.testSlot S source).bind fun hit =>
      match hit with
      | none => .ret none
      | some (e, reverse) =>
        .tick (.arithmetic 12)
          (if s.assigned e = none ∧ boundary S Q s reverse.1 ≤ a then
            (Command.liftArithmetic (S := S) (Range.sample Q hQ a b)).bind fun r =>
              .ret (some ⟨source, reverse, e, r⟩)
          else .ret none)
  else .ret none

noncomputable def commit (s : Cache S Q) (entries : List (Entry S Q)) : Cache S Q :=
  entries.foldl (fun t x => assign S Q t x.source x.reverse x.edge x.rank) s

def addEntry {A : Type*} (entries : List A) : Option A → List A
  | none => entries
  | some x => x :: entries

noncomputable def collectStep (a b : ℕ) (v : V) (s : Cache S Q)
    (i : ℕ) (entries : List (Entry S Q)) : Program (Command S) (List (Entry S Q)) :=
  (selectedStep S Q hQ a b v i s).bind fun hit =>
    .tick (.arithmetic 2) (.ret (addEntry entries hit))

noncomputable def collect (a b : ℕ) (v : V) (s : Cache S Q) :
    Program (Command S) (List (Entry S Q)) :=
  let p := Range.probability Q a b
  (Command.liftArithmetic (S := S) (Sparse.sample (1 - p) (S.length v) 0)).bind fun selected =>
    Program.forEach (collectStep S Q hQ a b v s) selected []

noncomputable def finish (sortHeight : ℕ) (v : V) (s : Cache S Q)
    (entries : List (Entry S Q)) : Arithmetic (Cache S Q) :=
  let s' := commit S Q s entries
  let sorted := Sort.array (fun x y : Entry S Q => decide (x.rank.val ≤ y.rank.val))
    sortHeight (s'.known v)
  ⟨{ s' with level := Function.update s'.level v (s.level v + 1),
              ready := Function.update s'.ready v sorted.value },
    32 * entries.length + sorted.operations + 4⟩

noncomputable def extend (sortHeight : ℕ) (v : V) (s : Cache S Q) :
    Program (Command S) (Cache S Q) :=
  let a := boundary S Q s v
  let b := Buckets.bound (s.level v + 1)
  if b ≤ Q then
    (collect S Q hQ a b v s).bind fun entries =>
      let r := finish S Q sortHeight v s entries
      .tick (.arithmetic r.operations) (.ret r.value)
  else .ret s

end Cache

end SteinerUpperBound.Matching.Padded
