module

public import SteinerUpperBound.SmallCoverProgram.Ram
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace SteinerUpperBound.SmallCoverProgram.Closure

open scoped Classical

abbrev Dense (α : Type*) (g : ℕ) := Vector α (g * g)

def entry {α : Type*} {g : ℕ} (a : Dense α g) (x y : Fin g) : α :=
  a.get (finProdFinEquiv (x, y))

def rounds (g : ℕ) : ℕ := Nat.log2 (g + 1) + 1

def Bounded {g : ℕ} (a : Dense Bool g) : ℕ → Fin g → Fin g → Prop
  | 0, x, y => x = y ∨ entry a x y = true
  | r + 1, x, y => Bounded a r x y ∨ ∃ z, Bounded a r x z ∧ Bounded a r z y

theorem bounded_sound {g : ℕ} (a : Dense Bool g) (G : SimpleGraph (Fin g))
    (hAdj : ∀ x y, entry a x y = true ↔ G.Adj x y) :
    ∀ r x y, Bounded a r x y → G.Reachable x y := by
  intro r
  induction r with
  | zero =>
      intro x y h
      rcases h with rfl | h
      · exact SimpleGraph.Reachable.refl _
      · exact ((hAdj x y).mp h).reachable
  | succ r ih =>
      intro x y h
      rcases h with h | ⟨z, hx, hy⟩
      · exact ih x y h
      · exact (ih x z hx).trans (ih z y hy)

theorem bounded_complete {g : ℕ} (a : Dense Bool g) (G : SimpleGraph (Fin g))
    (hAdj : ∀ x y, entry a x y = true ↔ G.Adj x y) :
    ∀ r {x y : Fin g} (p : G.Walk x y), p.length ≤ 2 ^ r → Bounded a r x y := by
  intro r
  induction r with
  | zero =>
      intro x y p hp
      cases p with
      | nil => exact Or.inl rfl
      | @cons x y z hxy p =>
          cases p with
          | nil => exact Or.inr ((hAdj x y).mpr hxy)
          | cons h p =>
              simp only [SimpleGraph.Walk.length_cons, pow_zero] at hp
              omega
  | succ r ih =>
      intro x y p hp
      refine Or.inr ⟨p.getVert (2 ^ r), ih (p.take (2 ^ r)) ?_, ih (p.drop (2 ^ r)) ?_⟩
      · rw [SimpleGraph.Walk.take_length]
        exact Nat.min_le_left _ _
      · rw [SimpleGraph.Walk.drop_length]
        simp only [pow_succ] at hp
        omega

theorem bounded_iff_reachable {g : ℕ} (a : Dense Bool g) (G : SimpleGraph (Fin g))
    (hAdj : ∀ x y, entry a x y = true ↔ G.Adj x y) (x y : Fin g) :
    Bounded a (rounds g) x y ↔ G.Reachable x y := by
  refine ⟨bounded_sound a G hAdj _ _ _, ?_⟩
  intro h
  obtain ⟨p, hp⟩ := h.exists_isPath
  have hlen : p.length < g := by simpa only [Fintype.card_fin] using hp.length_lt
  have hpow : g + 1 < 2 ^ rounds g := by
    simpa only [rounds, Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) (g + 1)
  exact bounded_complete a G hAdj _ p (by omega)

theorem fold_or_true {α : Type*} (p : α → Bool) (l : List α) (init : Bool) :
    l.foldl (fun b x => b || p x) init = true ↔
      init = true ∨ ∃ x ∈ l, p x = true := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih =>
      simp only [List.foldl_cons, ih, Bool.or_eq_true, List.mem_cons]
      aesop

end SteinerUpperBound.SmallCoverProgram.Closure
