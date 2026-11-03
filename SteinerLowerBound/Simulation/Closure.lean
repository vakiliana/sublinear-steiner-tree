module

public import SteinerLowerBound.Simulation.Tree

@[expose] public section

namespace SteinerLowerBound.Simulation

open scoped Classical

variable {T X : Type*}

inductive Halt
  | notices | closure
  deriving DecidableEq

structure State (T X : Type*) where
  noticed : Finset T
  exposed : Finset T
  requested : Finset T
  cache : Cache X
  stop : Option Halt

def State.initial : State T X := ⟨∅, ∅, ∅, .empty, none⟩

noncomputable def vertices (support : X → Finset T) (K : Finset X) : Finset T :=
  K.biUnion support

theorem vertices_mono (support : X → Finset T) {K L : Finset X} (h : K ⊆ L) :
    vertices support K ⊆ vertices support L := by
  classical
  intro u hu
  obtain ⟨x, hx, hu⟩ := Finset.mem_biUnion.mp hu
  exact Finset.mem_biUnion.mpr ⟨x, h hx, hu⟩

structure Safe (D : Finset T → Finset X) (support : X → Finset T)
    (cap : ℕ) (s : State T X) : Prop where
  requested_cap : s.requested.card ≤ cap
  requested_subset : s.requested ⊆ s.exposed
  read_subset : s.cache.read ⊆ D s.requested
  kept_subset : s.cache.kept ⊆ s.cache.read
  cover : s.exposed ⊆ s.noticed ∪ vertices support s.cache.kept

def Ready (D : Finset T → Finset X) (support : X → Finset T) (s : State T X) : Prop :=
  s.stop = none → D s.exposed ⊆ s.cache.read ∧ vertices support s.cache.kept ⊆ s.exposed

theorem initial_safe (D : Finset T → Finset X) (support : X → Finset T) (cap : ℕ) :
    Safe D support cap (State.initial : State T X) := by
  constructor <;> simp [State.initial, Cache.empty, vertices]

theorem initial_ready (D : Finset T → Finset X) (support : X → Finset T)
    (hD : D ∅ = ∅) : Ready D support (State.initial : State T X) := by
  simp [Ready, State.initial, hD, Cache.empty, vertices]

noncomputable def readList : List X → Cache X → DecisionTree X Bool (Cache X)
  | [], s => .leaf s
  | x :: l, s =>
      if x ∈ s.read then readList l s
      else .query x (fun b => readList l (s.record x b))

theorem record_kept_subset (s : Cache X) (x : X) (b : Bool)
    (hs : s.kept ⊆ s.read) : (s.record x b).kept ⊆ (s.record x b).read := by
  classical
  cases b
  · exact fun _ h => Finset.mem_insert_of_mem (hs h)
  · exact Finset.insert_subset_insert x hs

theorem readList_spec (l : List X) (s : Cache X) (hs : s.kept ⊆ s.read) :
    Spec id (fun r => r.read = s.read ∪ l.toFinset ∧ s.kept ⊆ r.kept ∧ r.kept ⊆ r.read)
      s (readList l s) := by
  classical
  induction l generalizing s with
  | nil => exact ⟨rfl, by simp [hs]⟩
  | cons x l ih =>
      by_cases hx : x ∈ s.read
      · simp only [readList, hx, ↓reduceIte]
        apply (ih s hs).mono
        intro r hr
        refine ⟨?_, hr.2⟩
        rw [hr.1]
        ext y
        simp only [Finset.mem_union, List.toFinset_cons, Finset.mem_insert]
        aesop
      · simp only [readList, hx, ↓reduceIte, Spec]
        refine ⟨by trivial, fun b => ?_⟩
        apply (ih (s.record x b) (record_kept_subset s x b hs)).mono
        intro r hr
        refine ⟨?_, (s.kept_subset_record x b).trans hr.2.1, hr.2.2⟩
        rw [hr.1]
        simp only [Cache.record, List.toFinset_cons]
        ext y
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto

theorem readList_protected (support : X → Finset T) (B : Finset T)
    (l : List X) (s : Cache X) (o : X → Bool)
    (hs : vertices support s.kept ⊆ B)
    (hl : ∀ x ∈ l, o x = true → support x ⊆ B) :
    vertices support ((readList l s).output o).kept ⊆ B := by
  classical
  induction l generalizing s with
  | nil => exact hs
  | cons x l ih =>
      simp only [readList]
      split_ifs with hx
      · exact ih s hs (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      · simp only [DecisionTree.output]
        apply ih _ _ (fun y hy => hl y (List.mem_cons_of_mem _ hy))
        cases hb : o x with
        | false => simpa [Cache.record, hb] using hs
        | true =>
            intro u hu
            obtain ⟨y, hy, hu⟩ := Finset.mem_biUnion.mp hu
            simp only [Cache.record, hb, ↓reduceIte, Finset.mem_insert] at hy
            rcases hy with hxy | hy
            · subst y
              exact hl x (by simp) hb hu
            · exact hs (Finset.mem_biUnion.mpr ⟨y, hy, hu⟩)

noncomputable def close (D : Finset T → Finset X) (support : X → Finset T) (cap : ℕ) :
    ℕ → State T X → DecisionTree X Bool (State T X)
  | fuel, s =>
      if s.stop ≠ none then .leaf s
      else if cap < s.exposed.card then .leaf {s with stop := some .closure}
      else match fuel with
      | 0 => .leaf s
      | fuel + 1 =>
          bind (readList (D s.exposed).toList s.cache) fun cache =>
            let r := {s with requested := s.exposed, cache := cache}
            let Q := s.exposed ∪ vertices support cache.kept
            if Q = s.exposed then .leaf r
            else close D support cap fuel {r with exposed := Q}

def ClosePost (D : Finset T → Finset X) (support : X → Finset T) (cap : ℕ)
    (s r : State T X) : Prop :=
  Safe D support cap r ∧ Ready D support r ∧ r.noticed = s.noticed ∧
    s.exposed ⊆ r.exposed ∧ (r.stop = s.stop ∨ r.stop = some .closure) ∧
      (r.stop = some .closure → s.stop = some .closure ∨ cap < r.exposed.card) ∧
      (r.stop = none → r.exposed.card ≤ cap)

theorem close_spec (D : Finset T → Finset X) (support : X → Finset T)
    (hD : Monotone D) (cap fuel : ℕ) (s : State T X)
    (hs : Safe D support cap s) (hfuel : cap < fuel + s.exposed.card) :
    Spec State.cache (ClosePost D support cap s) s.cache (close D support cap fuel s) := by
  classical
  induction fuel generalizing s with
  | zero =>
      have hcap : cap < s.exposed.card := by omega
      rw [close]
      split_ifs with hstop
      · change s.cache = s.cache ∧ ClosePost D support cap s s
        exact ⟨rfl, hs, fun hn => False.elim (hstop hn), rfl, Finset.Subset.rfl,
          Or.inl rfl, (fun hn => Or.inl hn), fun hn => False.elim (hstop hn)⟩
      · change s.cache = s.cache ∧ ClosePost D support cap s {s with stop := some .closure}
        refine ⟨rfl, ?_, ?_, rfl, Finset.Subset.rfl, Or.inr rfl,
          (fun _ => Or.inr hcap), ?_⟩
        · exact ⟨hs.requested_cap, hs.requested_subset, hs.read_subset, hs.kept_subset, hs.cover⟩
        · simp [Ready]
        · simp
  | succ fuel ih =>
      rw [close]
      split_ifs with hstop hcap
      · change s.cache = s.cache ∧ ClosePost D support cap s s
        exact ⟨rfl, hs, fun hn => False.elim (hstop hn), rfl, Finset.Subset.rfl,
          Or.inl rfl, (fun hn => Or.inl hn), fun hn => False.elim (hstop hn)⟩
      · change s.cache = s.cache ∧ ClosePost D support cap s {s with stop := some .closure}
        refine ⟨rfl, ?_, ?_, rfl, Finset.Subset.rfl, Or.inr rfl,
          (fun _ => Or.inr hcap), ?_⟩
        · exact ⟨hs.requested_cap, hs.requested_subset, hs.read_subset, hs.kept_subset, hs.cover⟩
        · simp [Ready]
        · simp
      · apply (readList_spec (D s.exposed).toList s.cache hs.kept_subset).bind
        intro cache hc
        let r : State T X := {s with requested := s.exposed, cache := cache}
        let Q := s.exposed ∪ vertices support cache.kept
        have hr : Safe D support cap r := by
          refine ⟨Nat.le_of_not_gt hcap, Finset.Subset.rfl, ?_, hc.2.2, ?_⟩
          · change cache.read ⊆ D s.exposed
            rw [hc.1, Finset.toList_toFinset]
            exact Finset.union_subset (hs.read_subset.trans (hD hs.requested_subset))
              Finset.Subset.rfl
          · exact hs.cover.trans (Finset.union_subset_union_right
              (vertices_mono support hc.2.1))
        have hQR : s.exposed ⊆ Q := Finset.subset_union_left
        change Spec State.cache (ClosePost D support cap s) cache
          (if Q = s.exposed then .leaf r else close D support cap fuel {r with exposed := Q})
        by_cases he : Q = s.exposed
        · rw [if_pos he]
          change cache = cache ∧ ClosePost D support cap s r
          refine ⟨rfl, hr, ?_, rfl, Finset.Subset.rfl, Or.inl rfl,
            (fun hn => Or.inl hn), fun _ => Nat.le_of_not_gt hcap⟩
          intro _
          constructor
          · change D s.exposed ⊆ cache.read
            rw [hc.1, Finset.toList_toFinset]
            exact Finset.subset_union_right
          · change vertices support cache.kept ⊆ s.exposed
            rw [← he]
            exact Finset.subset_union_right
        · rw [if_neg he]
          have hQcard : s.exposed.card < Q.card := by
            exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hQR, Ne.symm he⟩)
          have hnew : Safe D support cap {r with exposed := Q} := by
            refine ⟨hr.requested_cap, hQR, hr.read_subset, hr.kept_subset, ?_⟩
            exact Finset.union_subset hr.cover (Finset.subset_union_right)
          apply (ih _ hnew (by change cap < fuel + Q.card; omega)).mono
          intro z hz
          exact ⟨hz.1, hz.2.1, hz.2.2.1,
            hQR.trans hz.2.2.2.1, hz.2.2.2.2⟩

theorem close_bounded (D : Finset T → Finset X) (support : X → Finset T)
    (cap fuel : ℕ) (s : State T X) (o : X → Bool) (B : Finset T)
    (hfuel : cap < fuel + s.exposed.card)
    (hstop : s.stop = none) (hQ : s.exposed ⊆ B)
    (hK : vertices support s.cache.kept ⊆ B) (hB : B.card ≤ cap)
    (hclosed : ∀ Q ⊆ B, ∀ x ∈ D Q, o x = true → support x ⊆ B) :
    ((close D support cap fuel s).output o).stop = none ∧
      ((close D support cap fuel s).output o).exposed ⊆ B := by
  classical
  induction fuel generalizing s with
  | zero =>
      have := Finset.card_le_card hQ
      omega
  | succ fuel ih =>
      have hcap : ¬cap < s.exposed.card :=
        Nat.not_lt.mpr ((Finset.card_le_card hQ).trans hB)
      simp only [close, hstop, ne_eq, not_true_eq_false, hcap, ↓reduceIte, output_bind]
      let cache := (readList (D s.exposed).toList s.cache).output o
      have hk : vertices support cache.kept ⊆ B :=
        readList_protected support B _ s.cache o hK
          (fun x hx hxtrue => hclosed s.exposed hQ x (Finset.mem_toList.mp hx) hxtrue)
      let Q := s.exposed ∪ vertices support cache.kept
      have hQB : Q ⊆ B := Finset.union_subset hQ hk
      let r : State T X := {s with requested := s.exposed, cache := cache, stop := none}
      change ((if Q = s.exposed then .leaf r else
          close D support cap fuel {r with exposed := Q}).output o).stop = none ∧
        ((if Q = s.exposed then .leaf r else
          close D support cap fuel {r with exposed := Q}).output o).exposed ⊆ B
      by_cases he : Q = s.exposed
      · rw [if_pos he]
        exact ⟨rfl, hQ⟩
      · rw [if_neg he]
        have hcard : s.exposed.card < Q.card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨Finset.subset_union_left, Ne.symm he⟩)
        exact ih _ (by change cap < fuel + Q.card; omega) rfl hQB hk

theorem close_protected (D : Finset T → Finset X) (support : X → Finset T)
    (cap fuel : ℕ) (s : State T X) (o : X → Bool) (B : Finset T)
    (hQ : s.exposed ⊆ B) (hK : vertices support s.cache.kept ⊆ B)
    (hclosed : ∀ Q ⊆ B, ∀ x ∈ D Q, o x = true → support x ⊆ B) :
    ((close D support cap fuel s).output o).exposed ⊆ B := by
  classical
  induction fuel generalizing s with
  | zero =>
      rw [close]
      split_ifs <;> exact hQ
  | succ fuel ih =>
      rw [close]
      split_ifs with hstop hcap
      · exact hQ
      · exact hQ
      · rw [output_bind]
        let cache := (readList (D s.exposed).toList s.cache).output o
        have hk : vertices support cache.kept ⊆ B :=
          readList_protected support B _ s.cache o hK
            (fun x hx hb => hclosed s.exposed hQ x (Finset.mem_toList.mp hx) hb)
        dsimp only
        split_ifs
        · exact hQ
        · exact ih _ (Finset.union_subset hQ hk) hk

end SteinerLowerBound.Simulation
