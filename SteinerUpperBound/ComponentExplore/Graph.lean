module

public import SteinerUpperBound.QueryProgram
public import SteinerUpperBound.NetworkLifting

@[expose] public section

namespace SteinerUpperBound.ComponentExplore

open scoped Classical

variable {V : Type*}

noncomputable def pending : List V → Finset V → Finset V → Option V
  | [], _, _ => none
  | x :: l, found, done =>
      if x ∈ found ∧ x ∉ done then some x else pending l found done

theorem pending_some (l : List V) (found done : Finset V) {x : V}
    (h : pending l found done = some x) :
    x ∈ l ∧ x ∈ found ∧ x ∉ done := by
  induction l with
  | nil => simp [pending] at h
  | cons y l ih =>
      by_cases hy : y ∈ found ∧ y ∉ done
      · simp [pending, hy] at h
        subst x
        exact ⟨List.mem_cons_self, hy⟩
      · simp only [pending, hy, ite_false] at h
        obtain ⟨hl, hf, hd⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ hl, hf, hd⟩

theorem pending_none (l : List V) (found done : Finset V)
    (h : pending l found done = none) :
    ∀ x ∈ l, x ∈ found → x ∈ done := by
  induction l with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons y l ih =>
      by_cases hy : y ∈ found ∧ y ∉ done
      · simp [pending, hy] at h
      · have ht : pending l found done = none := by
          simpa only [pending, hy, ite_false] using h
        intro x hx hfound
        rcases List.mem_cons.mp hx with rfl | hx
        · by_contra hd
          exact hy ⟨hfound, hd⟩
        · exact ih ht x hx hfound

noncomputable def scan (B : ℕ) (G : SimpleGraph V) (x : V) :
    List V → Finset V → Finset V
  | [], found => found
  | y :: l, found =>
      if B < found.card then found
      else scan B G x l (if G.Adj x y then insert y found else found)

theorem scan_mono (B : ℕ) (G : SimpleGraph V) (x : V) (l : List V) (found : Finset V) :
    found ⊆ scan B G x l found := by
  induction l generalizing found with
  | nil => rfl
  | cons y l ih =>
      by_cases hb : B < found.card
      · simp only [scan, hb, ite_true, Finset.Subset.refl]
      · rw [scan, if_neg hb]
        apply Finset.Subset.trans _ (ih _)
        split_ifs
        · exact Finset.subset_insert _ _
        · rfl

theorem scan_size (B : ℕ) (G : SimpleGraph V) (x : V) (l : List V) (found : Finset V)
    (h : found.card ≤ B + 1) : (scan B G x l found).card ≤ B + 1 := by
  induction l generalizing found with
  | nil => exact h
  | cons y l ih =>
      by_cases hb : B < found.card
      · simpa only [scan, hb, ite_true] using h
      · rw [scan, if_neg hb]
        apply ih
        split_ifs
        · exact (Finset.card_insert_le _ _).trans (by omega)
        · exact h

theorem scan_subset (B : ℕ) (G : SimpleGraph V) (x : V) (l : List V)
    (found T : Finset V) (hf : found ⊆ T) (hl : ∀ y ∈ l, y ∈ T) :
    scan B G x l found ⊆ T := by
  induction l generalizing found with
  | nil => exact hf
  | cons y l ih =>
      by_cases hb : B < found.card
      · simpa only [scan, hb, ite_true] using hf
      · rw [scan, if_neg hb]
        apply ih _ ?_ (fun z hz => hl z (List.mem_cons_of_mem _ hz))
        split_ifs
        · exact Finset.insert_subset_iff.mpr ⟨hl y List.mem_cons_self, hf⟩
        · exact hf

theorem scan_reachable (B : ℕ) (G : SimpleGraph V) (root x : V) (l : List V)
    (found : Finset V) (hx : G.Reachable root x)
    (hf : ∀ y ∈ found, G.Reachable root y) :
    ∀ y ∈ scan B G x l found, G.Reachable root y := by
  induction l generalizing found with
  | nil => exact hf
  | cons z l ih =>
      by_cases hb : B < found.card
      · simpa only [scan, hb, ite_true] using hf
      · rw [scan, if_neg hb]
        apply ih
        split_ifs with ha
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact hx.trans ha.reachable
          · exact hf _ hy
        · exact hf

theorem scan_closed (B : ℕ) (G : SimpleGraph V) (x : V) (l : List V) (found : Finset V)
    (h : (scan B G x l found).card ≤ B) :
    ∀ y ∈ l, G.Adj x y → y ∈ scan B G x l found := by
  induction l generalizing found with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons z l ih =>
      have hb : ¬B < found.card := by
        have hm := Finset.card_le_card (scan_mono B G x (z :: l) found)
        omega
      rw [scan, if_neg hb] at h ⊢
      intro y hy hxy
      rcases List.mem_cons.mp hy with heq | hy
      · subst y
        have hm := scan_mono B G x l (insert z found)
        simpa only [hxy, ite_true] using hm (Finset.mem_insert_self _ _)
      · exact ih _ h y hy hxy

structure State (V : Type*) where
  found : Finset V
  done : Finset V

structure Result (V : Type*) where
  state : State V
  complete : Bool

noncomputable def run (B : ℕ) (G : SimpleGraph V) (l : List V) :
    ℕ → State V → Result V
  | 0, s =>
      if B < s.found.card then ⟨s, false⟩
      else ⟨s, (pending l s.found s.done).isNone⟩
  | fuel + 1, s =>
      if B < s.found.card then ⟨s, false⟩
      else match pending l s.found s.done with
        | none => ⟨s, true⟩
        | some x => run B G l fuel ⟨scan B G x l s.found, insert x s.done⟩

structure Invariant (B : ℕ) (G : SimpleGraph V) (l : List V) (root : V)
    (s : State V) : Prop where
  root_mem : root ∈ s.found
  done_subset : s.done ⊆ s.found
  enum_subset : s.found ⊆ l.toFinset
  reachable : ∀ y ∈ s.found, G.Reachable root y
  size : s.found.card ≤ B + 1
  closed : s.found.card ≤ B → ∀ x ∈ s.done, ∀ y, G.Adj x y → y ∈ s.found

theorem advance_invariant (B : ℕ) (G : SimpleGraph V) (l : List V) (root : V)
    (s : State V) (hs : Invariant B G l root s) (x : V) (hx : x ∈ s.found)
    (hsupport : Network.TerminalOnly l.toFinset G) :
    Invariant B G l root ⟨scan B G x l s.found, insert x s.done⟩ := by
  have hm := scan_mono B G x l s.found
  refine ⟨hm hs.root_mem, ?_, ?_, ?_, scan_size B G x l s.found hs.size, ?_⟩
  · exact Finset.insert_subset_iff.mpr ⟨hm hx, hs.done_subset.trans hm⟩
  · exact scan_subset B G x l s.found l.toFinset hs.enum_subset
      (fun y hy => List.mem_toFinset.mpr hy)
  · exact scan_reachable B G root x l s.found (hs.reachable x hx) hs.reachable
  · intro hsize z hz y hzy
    rcases Finset.mem_insert.mp hz with heq | hz
    · subst z
      exact scan_closed B G x l s.found hsize y
        (List.mem_toFinset.mp (hsupport x y hzy).2) hzy
    · have hsmall : s.found.card ≤ B := (Finset.card_le_card hm).trans hsize
      exact hm (hs.closed hsmall z hz y hzy)

theorem reachable_closed (G : SimpleGraph V) (S : Finset V)
    (hS : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S) {x y : V}
    (hx : x ∈ S) (hxy : G.Reachable x y) : y ∈ S := by
  obtain ⟨p⟩ := hxy
  revert hx
  induction p with
  | nil => exact id
  | @cons x y z hxy p ih =>
      intro hx
      exact ih (hS x hx y hxy)

variable [Fintype V]

noncomputable def component (G : SimpleGraph V) (root : V) : Finset V :=
  Finset.univ.filter (G.Reachable root)

theorem component_eq_of_no_pending (B : ℕ) (G : SimpleGraph V) (l : List V) (root : V)
    (s : State V) (hs : Invariant B G l root s) (hsize : s.found.card ≤ B)
    (hp : pending l s.found s.done = none) : s.found = component G root := by
  have hfd : s.found ⊆ s.done := by
    intro x hx
    exact pending_none l s.found s.done hp x
      (List.mem_toFinset.mp (hs.enum_subset hx)) hx
  have hc : ∀ x ∈ s.found, ∀ y, G.Adj x y → y ∈ s.found :=
    fun x hx y hxy => hs.closed hsize x (hfd hx) y hxy
  ext y
  simp only [component, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hs.reachable y, fun hy => reachable_closed G s.found hc hs.root_mem hy⟩

def CorrectResult (B : ℕ) (G : SimpleGraph V) (root : V) (r : Result V) : Prop :=
  (∀ y ∈ r.state.found, G.Reachable root y) ∧
    if r.complete then r.state.found = component G root ∧ r.state.found.card ≤ B
    else r.state.found.card = B + 1

theorem run_correct (B : ℕ) (G : SimpleGraph V) (l : List V) (root : V)
    (hsupport : Network.TerminalOnly l.toFinset G)
    (fuel : ℕ) (s : State V) (hs : Invariant B G l root s)
    (hbudget : s.done.card + fuel = B + 1) :
    CorrectResult B G root (run B G l fuel s) := by
  induction fuel generalizing s with
  | zero =>
      by_cases hb : B < s.found.card
      · simp only [run, hb, ite_true, CorrectResult, Bool.false_eq_true, ite_false]
        exact ⟨hs.reachable, by have h := hs.size; omega⟩
      · have hd := Finset.card_le_card hs.done_subset
        omega
  | succ fuel ih =>
      by_cases hb : B < s.found.card
      · simp only [run, hb, ite_true, CorrectResult, Bool.false_eq_true, ite_false]
        exact ⟨hs.reachable, by have h := hs.size; omega⟩
      · cases hp : pending l s.found s.done with
        | none =>
            simp only [run, hb, ite_false, hp, CorrectResult, ite_true]
            exact ⟨hs.reachable,
              component_eq_of_no_pending B G l root s hs (by omega) hp, by omega⟩
        | some x =>
            obtain ⟨_, hx, hd⟩ := pending_some l s.found s.done hp
            have hn := advance_invariant B G l root s hs x hx hsupport
            have hb' : (insert x s.done).card + fuel = B + 1 := by
              rw [Finset.card_insert_of_notMem hd]
              omega
            simpa only [run, hb, ite_false, hp] using ih _ hn hb'

theorem initial_correct (B : ℕ) (G : SimpleGraph V) (l : List V) (root : V)
    (hroot : root ∈ l) (hsupport : Network.TerminalOnly l.toFinset G) :
    CorrectResult B G root (run B G l (B + 1) ⟨{root}, ∅⟩) := by
  apply run_correct B G l root hsupport
  · refine ⟨by simp, by simp, ?_, ?_, by simp, ?_⟩
    · exact Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr hroot)
    · intro y hy
      have he : y = root := Finset.mem_singleton.mp hy
      subst y
      exact SimpleGraph.Reachable.refl _
    · simp
  · simp

end SteinerUpperBound.ComponentExplore
