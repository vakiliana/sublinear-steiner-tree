module

public import SteinerUpperBound.Matching.Requests

@[expose] public section

/-!
# Padded incidence lists

Only `Slots.test` is used to inspect an index. `Slots.place` is a specification
of where each directed copy occurs, not an operation available to the access
algorithm. A successful test supplies the reverse index.

A cost account has a fixed arithmetic/memory-operation rate. The slot bound
includes that rate, so sparse-sampling and cache maintenance can be charged to
selected indices. Ordinary work uses rate one; a disclosure-only account can
use rate zero. This is a primitive-cost contract, not an access-cost bound.
-/

namespace SteinerUpperBound.Matching.Padded

open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical BigOperators

variable {V E : Type*}

def reverse (d : Directed E) : Directed E := (d.1, !d.2)

@[simp] theorem reverse_edge (d : Directed E) : (reverse d).1 = d.1 := rfl

@[simp] theorem reverse_reverse (d : Directed E) : reverse (reverse d) = d := by
  cases d with | mk e b => cases b <;> rfl

@[simp] theorem head_reverse (G : Graph V E) (d : Directed E) :
    G.head (reverse d) = G.tail d := by
  cases d with | mk e b => cases b <;> rfl

@[simp] theorem tail_reverse (G : Graph V E) (d : Directed E) :
    G.tail (reverse d) = G.head d := by
  cases d with | mk e b => cases b <;> rfl

abbrev Slot (length : V → ℕ) := (v : V) × Fin (length v)

structure Slots (G : Graph V E) where
  length : V → ℕ
  test : Slot length → Option (E × Slot length)
  place : Directed E → Slot length
  place_vertex : ∀ d, (place d).1 = G.tail d
  test_place : ∀ d, test (place d) = some (d.1, place (reverse d))
  test_complete : ∀ s e r, test s = some (e, r) →
    ∃ d, place d = s ∧ d.1 = e ∧ place (reverse d) = r

namespace Slots

variable {G : Graph V E} (S : Slots G)

theorem place_injective : Function.Injective S.place := by
  intro d d' h
  have ht : G.tail d = G.tail d' := by
    rw [← S.place_vertex d, ← S.place_vertex d', h]
  have he := congrArg S.test h
  rw [S.test_place, S.test_place, Option.some.injEq, Prod.mk.injEq] at he
  exact G.directed_eq_of_tail he.1 ht

theorem test_reverse {s r : Slot S.length} {e : E} (h : S.test s = some (e, r)) :
    S.test r = some (e, s) := by
  obtain ⟨d, hd, he, hr⟩ := S.test_complete s e r h
  rw [← hr, S.test_place, reverse_edge, reverse_reverse, he, hd]

theorem test_incident {s r : Slot S.length} {e : E} (h : S.test s = some (e, r)) :
    G.Incident e s.1 ∧ G.Incident e r.1 ∧ s.1 ≠ r.1 := by
  obtain ⟨d, hd, he, hr⟩ := S.test_complete s e r h
  rw [← hd, ← hr, S.place_vertex, S.place_vertex, tail_reverse, ← he]
  exact ⟨G.tail_incident d, G.head_incident d, (G.head_ne_tail d).symm⟩

theorem test_unique {s t r r' : Slot S.length} {e : E}
    (hs : S.test s = some (e, r)) (ht : S.test t = some (e, r'))
    (hv : s.1 = t.1) : s = t := by
  obtain ⟨d, hd, hed, _⟩ := S.test_complete s e r hs
  obtain ⟨d', hd', hed', _⟩ := S.test_complete t e r' ht
  have hh : G.tail d = G.tail d' := by
    rw [← S.place_vertex d, ← S.place_vertex d', hd, hd', hv]
  have hdd := G.directed_eq_of_tail (hed.trans hed'.symm) hh
  exact hd.symm.trans (hdd ▸ hd')

def atVertex (v : V) : {s : Slot S.length // s.1 = v} ≃ Fin (S.length v) where
  toFun s := by
    obtain ⟨⟨u, i⟩, h⟩ := s
    cases h
    exact i
  invFun i := ⟨⟨v, i⟩, rfl⟩
  left_inv s := by
    obtain ⟨⟨u, i⟩, h⟩ := s
    cases h
    rfl
  right_inv _ := rfl

variable [Fintype V]

def totalSlots : ℕ := ∑ v, S.length v

theorem card_slot : Fintype.card (Slot S.length) = S.totalSlots := by
  simp [Slot, totalSlots, Fintype.card_sigma]

theorem length_le_total (v : V) : S.length v ≤ S.totalSlots :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)

variable [Fintype E]

theorem copies_le_slots : 2 * Fintype.card E ≤ S.totalSlots := by
  have h := Fintype.card_le_of_injective S.place S.place_injective
  simpa only [Fintype.card_prod, Fintype.card_bool, S.card_slot, Nat.mul_comm] using h

theorem degree_le_length (v : V) : G.degree v ≤ S.length v := by
  let f : {e : E // G.Incident e v} → {s : Slot S.length // s.1 = v} := fun e =>
    ⟨S.place (G.away v e.val), (S.place_vertex _).trans (G.tail_away e.property)⟩
  have hf : Function.Injective f := by
    intro e e' h
    apply Subtype.ext
    have hp := S.place_injective (congrArg Subtype.val h)
    exact congrArg Prod.fst hp
  have h := Fintype.card_le_of_injective f hf
  have hc := Fintype.card_congr (S.atVertex v)
  rw [hc, Fintype.card_fin] at h
  simpa [Graph.degree, Fintype.card_subtype] using h

end Slots

structure Account {G : Graph V E} (S : Slots G) where
  Cstar : ℝ
  rate : ℝ
  slot : Slot S.length → ℝ
  preparation : V → ℝ
  rate_nonneg : 0 ≤ rate
  rate_le_Cstar : rate ≤ Cstar
  rate_le_slot : ∀ s, rate ≤ slot s
  slot_le : ∀ s, slot s ≤ Cstar
  preparation_nonneg : ∀ v, 0 ≤ preparation v
  preparation_le : ∀ v, preparation v ≤ Cstar
  Cstar_nonneg : 0 ≤ Cstar

namespace Account

variable {G : Graph V E} {S : Slots G} (A : Account S)

theorem slot_nonneg (s : Slot S.length) : 0 ≤ A.slot s :=
  A.rate_nonneg.trans (A.rate_le_slot s)

def W (v : V) : ℝ := ∑ i : Fin (S.length v), A.slot ⟨v, i⟩

theorem W_nonneg (v : V) : 0 ≤ A.W v :=
  Finset.sum_nonneg fun _ _ => A.slot_nonneg _

theorem W_le (v : V) : A.W v ≤ S.length v * A.Cstar := by
  calc
    _ ≤ ∑ _i : Fin (S.length v), A.Cstar :=
      Finset.sum_le_sum fun i _ => A.slot_le _
    _ = _ := by simp

noncomputable def cost [Fintype V] (prepared : Finset V)
    (tested : List (Slot S.length)) (operations : ℕ) : ℝ :=
  (∑ v ∈ prepared, A.preparation v) + (tested.map A.slot).sum + A.rate * operations

theorem cost_nonneg [Fintype V] (prepared : Finset V)
    (tested : List (Slot S.length)) (operations : ℕ) :
    0 ≤ A.cost prepared tested operations := by
  apply add_nonneg
  · apply add_nonneg
    · exact Finset.sum_nonneg fun v _ => A.preparation_nonneg v
    · exact List.sum_nonneg (fun _ h => by
        obtain ⟨s, _, rfl⟩ := List.mem_map.mp h
        exact A.slot_nonneg s)
  · exact mul_nonneg A.rate_nonneg (Nat.cast_nonneg _)

end Account

end SteinerUpperBound.Matching.Padded
