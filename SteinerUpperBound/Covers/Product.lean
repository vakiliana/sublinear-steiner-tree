module

public import SteinerUpperBound.Covers.Factory

@[expose] public section

namespace SteinerUpperBound.Covers.FiniteSampling

open SteinerLowerBound
open scoped Classical BigOperators

variable {U A : Type*} [Fintype U] [Fintype A]

noncomputable def reveal : List U → (U → A) → DecisionTree U A (U → A)
  | [], cache => .leaf cache
  | x :: l, cache => .query x (fun a => reveal l (Function.update cache x a))

theorem output_reveal (l : List U) (cache o : U → A) (q : U) :
    (reveal l cache).output o q = if q ∈ l then o q else cache q := by
  classical
  induction l generalizing cache with
  | nil => simp [reveal, DecisionTree.output]
  | cons x l ih =>
    simp only [reveal, DecisionTree.output, ih, List.mem_cons]
    by_cases hq : q = x
    · subst q
      simp
    · simp [hq, Function.update_of_ne hq]

theorem used_reveal (l : List U) (cache : U → A) :
    (reveal l cache).used ⊆ l.toFinset := by
  classical
  induction l generalizing cache with
  | nil => simp [reveal, DecisionTree.used]
  | cons x l ih =>
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · simp
    · obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hq
      simp only [List.toFinset_cons]
      exact Finset.mem_insert_of_mem (ih _ ha)

theorem reveal_noRepeats (l : List U) (hl : l.Nodup) (cache : U → A) :
    (reveal l cache).NoRepeats := by
  classical
  induction l generalizing cache with
  | nil => trivial
  | cons x l ih =>
    refine ⟨fun a => ih (List.nodup_cons.mp hl).2 _, fun a hx => ?_⟩
    exact (List.nodup_cons.mp hl).1 (List.mem_toFinset.mp (used_reveal l _ hx))

theorem reveal_height (l : List U) (cache : U → A) :
    Protocol.height (reveal l cache) ≤ l.length := by
  classical
  induction l generalizing cache with
  | nil => simp [reveal, Protocol.height]
  | cons x l ih =>
    have hs : Finset.univ.sup
        (fun a : A => Protocol.height (reveal l (Function.update cache x a))) ≤ l.length :=
      Finset.sup_le (fun a _ => ih _)
    simp only [reveal, Protocol.height, List.length_cons]
    omega

theorem product_close [Nonempty A] (μ ν : U → Law A) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ x, Law.Close (μ x) (ν x) δ) :
    Law.Close (Law.pi μ) (Law.pi ν) ((Fintype.card U : ℝ) * δ) := by
  classical
  let t := reveal (Finset.univ.toList : List U) (fun _ => Classical.choice ‹Nonempty A›)
  have hnr : t.NoRepeats := reveal_noRepeats _ (Finset.nodup_toList _) _
  have hh : Protocol.height t ≤ Fintype.card U := by
    simpa [t] using reveal_height (Finset.univ.toList : List U)
      (fun _ => Classical.choice ‹Nonempty A›)
  have hout (o : U → A) : t.output o = o := by
    funext q
    simp [t, output_reveal]
  have hμ (E : Set (U → A)) : (Law.pi μ).prob E = (t.runLaw μ).prob E := by
    simpa only [hout, Set.setOf_mem_eq] using DecisionTree.deferred_sampling μ t hnr E
  have hν (E : Set (U → A)) : (Law.pi ν).prob E = (t.runLaw ν).prob E := by
    simpa only [hout, Set.setOf_mem_eq] using DecisionTree.deferred_sampling ν t hnr E
  intro E
  rw [hμ, hν]
  exact Protocol.lazy_close μ ν δ hδ h t (Fintype.card U) hh E

theorem bernoulli_one :
    CategoricalCoupling.bernoulli (⟨1, by norm_num⟩ : Rate) = Law.pure true := by
  apply bool_ext
  simp [CategoricalCoupling.bernoulli, Law.pure]

end SteinerUpperBound.Covers.FiniteSampling

namespace SteinerUpperBound.Covers.Factory

open SteinerLowerBound
open ClosedRelation
open scoped Classical BigOperators

variable {U : Type*} [Fintype U] [Nonempty U]

noncomputable def forcedBitLaw (R : U → U → Prop) (root : U) (B ψ : ℕ) (x : U) :
    Law Bool :=
  if x = root then Law.pure true else bitLaw R x B ψ

noncomputable def privateBits (R : U → U → Prop) (root : U) (B ψ : ℕ) :
    Law (U → Bool) :=
  Law.pi (forcedBitLaw R root B ψ)

theorem privateBits_close (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (root : U) (B ψ : ℕ) :
    Law.Close (privateBits R root B ψ) (independentBits R hrefl root ψ)
      ((Fintype.card U : ℝ) * Real.exp (-(B : ℝ) / Fintype.card U)) := by
  classical
  apply FiniteSampling.product_close _ _ _ (Real.exp_pos _).le
  intro x
  by_cases hx : x = root
  · simp only [forcedBitLaw, forcedRate, hx, ↓reduceIte, FiniteSampling.bernoulli_one]
    exact (Law.close_refl _).mono (Real.exp_pos _).le
  · simpa only [forcedBitLaw, forcedRate, hx, ↓reduceIte] using
      bitLaw_close_exp R hrefl x B ψ

theorem private_tapes (R : U → U → Prop) (root : U) (B ψ : ℕ) :
    ((FiniteSampling.tape (Law.uniform U) B).iid U).map
      (fun tapes x => if x = root then true else (scan R x B ψ (tapes x)).getD false) =
        privateBits R root B ψ := by
  classical
  calc
    _ = Law.pi (fun x : U => (FiniteSampling.tape (Law.uniform U) B).map
        (fun w => if x = root then true else (scan R x B ψ w).getD false)) :=
      LawOperations.pi_map (fun _ : U => FiniteSampling.tape (Law.uniform U) B)
        (fun x w => if x = root then true else (scan R x B ψ w).getD false)
    _ = privateBits R root B ψ := by
      congr 1
      funext x
      by_cases hx : x = root
      · simp only [hx, ↓reduceIte, forcedBitLaw]
        exact FiniteSampling.map_const _ _
      · simp only [hx, ↓reduceIte, forcedBitLaw, bitLaw]
        rw [← scan_law R x B ψ, LawOperations.map_comp]

end SteinerUpperBound.Covers.Factory
