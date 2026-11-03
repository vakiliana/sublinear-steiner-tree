module

public import SteinerUpperBound.Matching.Padded.Cache
public import SteinerUpperBound.Matching.Padded.Disintegration

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical BigOperators

namespace Program

variable {C D A S : Type*}

theorem supported_relabel (f : C → D) (p : Program C A) (P : A → Prop)
    (h : p.Supported P) : (p.relabel f).Supported P := by
  induction p with
  | ret a => exact h
  | tick c p ih => exact ih h
  | draw n hn next ih => exact fun x => ih x.1 (fun y => h ⟨x.1, y⟩) x.2

theorem forEach_supported (step : A → S → Program C S) (xs : List A) (I : S → Prop)
    (hstep : ∀ a ∈ xs, ∀ s, I s → (step a s).Supported I)
    (s : S) (hs : I s) : (forEach step xs s).Supported I := by
  induction xs generalizing s with
  | nil => exact supported_ret _ _ hs
  | cons a xs ih =>
    exact supported_bind (step a s) _ I I (hstep a (by simp) s hs)
      (fun s' hs' => ih (fun b hb => hstep b (by simp [hb])) s' hs')

end Program

namespace Cache

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ) (hQ : 0 < Q)

theorem lower_at_endpoint (s : Cache S Q) (e : E) (v : V) (hi : G.Incident e v) :
    boundary S Q s v ≤ lower S Q s e := by
  rcases hi with h | h
  · rw [← h]
    exact Nat.le_max_left _ _
  · rw [← h]
    exact Nat.le_max_right _ _

theorem completion_consistent [Fintype E] (s : Cache S Q) (hs : Legal S Q s)
    (ranks : E → Fin Q) (hm : 0 < (completion S Q hQ s).mass ranks) :
    Consistent S Q s ranks := by
  have hcoord (e : E) : 0 <
      (match s.assigned e with
       | some r => Law.pure r
       | none => Range.law Q hQ (lower S Q s e) Q).mass (ranks e) :=
    Law.pi_mass_positive _ ranks hm e
  have hknown (e : E) (r : Fin Q) (hr : s.assigned e = some r) : ranks e = r := by
    have hc := hcoord e
    by_contra hn
    simp [hr, Law.pure, hn] at hc
  refine ⟨hknown, ?_⟩
  intro e v hi hlt
  cases he : s.assigned e with
  | some r => simp only [hknown e r he]
  | none =>
    have hc := hcoord e
    simp only [he] at hc
    rw [Range.mass Q hQ _ Q ⟨hs.2 e he, le_refl _⟩] at hc
    split_ifs at hc with hr
    · have hbound := lower_at_endpoint S Q s e v hi
      omega
    · linarith

def EntryValid (x : Entry S Q) : Prop :=
  S.test x.source = some (x.edge, x.reverse)

theorem selectedStep_valid (a b : ℕ) (v : V) (i : ℕ) (s : Cache S Q) :
    (selectedStep S Q hQ a b v i s).Supported
      (fun hit => ∀ x, hit = some x → EntryValid S Q x) := by
  unfold selectedStep
  split_ifs with hi
  · simp only [Command.testSlot, Program.bind]
    cases ht : S.test ⟨v, ⟨i, hi⟩⟩ with
    | none => exact fun _ _ h => by cases h
    | some hit =>
      obtain ⟨e, reverse⟩ := hit
      apply Program.supported_tick
      dsimp only
      apply Program.supported_tick
      split_ifs
      · refine Program.supported_bind _ _ (fun _ => True) _ (fun _ => trivial) ?_
        intro r _
        exact Program.supported_ret _ _ (fun x hx => by cases hx; exact ht)
      · exact Program.supported_ret _ _ (fun _ h => by cases h)
  · exact Program.supported_ret _ _ (fun _ h => by cases h)

theorem commit_compatible (s : Cache S Q) (hs : Compatible S Q s)
    (xs : List (Entry S Q)) (hx : ∀ x ∈ xs, EntryValid S Q x) :
    Compatible S Q (commit S Q s xs) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih =>
    exact ih (assign S Q s x.source x.reverse x.edge x.rank)
      (assign_compatible S Q s hs _ _ _ _ (hx x (by simp)))
      (fun y hy => hx y (by simp [hy]))

theorem collect_valid (a b : ℕ) (v : V) (s : Cache S Q) :
    (collect S Q hQ a b v s).Supported (fun xs => ∀ x ∈ xs, EntryValid S Q x) := by
  unfold collect
  dsimp only
  refine Program.supported_bind _ _ (fun _ => True) _ (fun _ => trivial) ?_
  intro selected _
  exact Program.forEach_supported
      (collectStep S Q hQ a b v s)
      selected (fun xs => ∀ x ∈ xs, EntryValid S Q x)
      (fun i _ entries he => by
        unfold collectStep
        refine Program.supported_bind _ _ _ _ (selectedStep_valid S Q hQ _ _ v i s) ?_
        intro hit hh
        apply Program.supported_tick
        apply Program.supported_ret
        cases hit with
        | none => exact he
        | some x =>
          intro y hy
          rcases List.mem_cons.mp hy with hyx | hy
          · subst y
            exact hh x rfl
          · exact he y hy) [] (by simp)

theorem extend_compatible (sortHeight : ℕ) (v : V) (s : Cache S Q)
    (hs : Compatible S Q s) :
    (extend S Q hQ sortHeight v s).Supported (Compatible S Q) := by
  unfold extend
  dsimp only
  split_ifs
  · refine Program.supported_bind _ _ _ _ (collect_valid S Q hQ _ _ v s) ?_
    intro entries he
    apply Program.supported_tick
    apply Program.supported_ret
    exact commit_compatible S Q s hs entries he
  · exact Program.supported_ret _ _ hs

noncomputable def slotCost (A : Account S) (v : V) (i : ℕ) : ℝ :=
  if hi : i < S.length v then A.slot ⟨v, ⟨i, hi⟩⟩ else A.rate

theorem selectedStep_cost (A : Account S) (a b : ℕ) (v : V) (i : ℕ) (s : Cache S Q) :
    (selectedStep S Q hQ a b v i s).expectedCost (Command.charge A) A.rate ≤
      15 * slotCost S A v i := by
  unfold selectedStep slotCost
  split_ifs with hi
  · have hslot := A.rate_le_slot (⟨v, ⟨i, hi⟩⟩ : Slot S.length)
    have hnon := A.slot_nonneg (⟨v, ⟨i, hi⟩⟩ : Slot S.length)
    simp only [Command.testSlot, Program.bind, Program.expectedCost_tick, Command.charge]
    cases ht : S.test ⟨v, ⟨i, hi⟩⟩ with
    | none => simp only [Program.expectedCost_ret]; nlinarith
    | some hit =>
      obtain ⟨e, reverse⟩ := hit
      rw [Program.expectedCost_tick]
      split_ifs
      · rw [Program.expectedCost_bind, Command.cost_arithmetic]
        simp only [Program.expectedCost_ret, Program.expect_const, add_zero, Command.charge]
        have hr := Program.expected_bound (Range.sample Q hQ a b)
          (fun n : ℕ => (n : ℝ)) 1 (fun _ => 0) 2 (Range.sample_cost_le Q hQ a b)
        simp only [Program.expect_const, add_zero] at hr
        have hm := mul_le_mul_of_nonneg_left hr A.rate_nonneg
        norm_num only [Nat.cast_ofNat]
        nlinarith
      · simp only [Program.expectedCost_ret, Command.charge]
        norm_num only [Nat.cast_ofNat]
        nlinarith
  · simp only [Program.expectedCost_ret]
    nlinarith [A.rate_nonneg]

end Cache

end SteinerUpperBound.Matching.Padded
