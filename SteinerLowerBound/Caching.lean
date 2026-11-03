module

public import SteinerLowerBound.ProposalProtocol

@[expose] public section

namespace SteinerLowerBound

open scoped Classical

namespace Caching

variable {Q A C W R S : Type*}

noncomputable def compile (center : Q → C) (answer : Q → W → A) :
    DecisionTree Q A R → (C → Option W) → DecisionTree C W R
  | .leaf r, _ => .leaf r
  | .query q next, cache =>
      match cache (center q) with
      | some w => compile center answer (next (answer q w)) cache
      | none => .query (center q) (fun w =>
          compile center answer (next (answer q w)) (Function.update cache (center q) (some w)))

def Consistent (cache : C → Option W) (o : C → W) : Prop :=
  ∀ c w, cache c = some w → o c = w

theorem output_compile (center : Q → C) (answer : Q → W → A)
    (t : DecisionTree Q A R) (cache : C → Option W) (o : C → W) (hc : Consistent cache o) :
    (compile center answer t cache).output o =
      t.output (fun q => answer q (o (center q))) := by
  classical
  induction t generalizing cache with
  | leaf => rfl
  | query q next ih =>
      cases he : cache (center q) with
      | some w =>
          have ho := hc (center q) w he
          simpa only [compile, he, DecisionTree.output, ho] using ih (answer q w) cache hc
      | none =>
          simp only [compile, he, DecisionTree.output]
          apply ih
          intro c w hw
          by_cases h : c = center q
          · subst c
            simpa only [Function.update_self, Option.some.injEq] using hw
          · exact hc c w (by simpa only [Function.update_of_ne h] using hw)

def Known (cache : C → Option W) (J : Finset C) : Prop :=
  ∀ c, c ∈ J ↔ cache c ≠ none

theorem known_update (cache : C → Option W) (J : Finset C) (hJ : Known cache J) (c : C) (w : W) :
    Known (Function.update cache c (some w)) (insert c J) := by
  classical
  intro c'
  by_cases h : c' = c
  · subst c'
    simp
  · simpa only [Finset.mem_insert, h, false_or, Function.update_of_ne h] using hJ c'

variable [Fintype A] [Fintype W]

omit [Fintype A] in
theorem used_avoids_cache (center : Q → C) (answer : Q → W → A)
    (t : DecisionTree Q A R) (cache : C → Option W) :
    ∀ c, cache c ≠ none → c ∉ (compile center answer t cache).used := by
  classical
  induction t generalizing cache with
  | leaf => simp [compile, DecisionTree.used]
  | query q next ih =>
      intro c hc
      cases he : cache (center q) with
      | some w =>
          simpa only [compile, he] using ih (answer q w) cache c hc
      | none =>
          simp only [compile, he, DecisionTree.used, Finset.mem_insert, Finset.mem_biUnion,
            Finset.mem_univ, true_and, not_or, not_exists]
          have hne : c ≠ center q := by intro h; subst c; exact hc he
          refine ⟨hne, fun w => ?_⟩
          apply ih (answer q w) (Function.update cache (center q) (some w)) c
          simpa only [Function.update_of_ne hne] using hc

omit [Fintype A] in
theorem compile_no_repeats (center : Q → C) (answer : Q → W → A)
    (t : DecisionTree Q A R) (cache : C → Option W) :
    (compile center answer t cache).NoRepeats := by
  classical
  induction t generalizing cache with
  | leaf => trivial
  | query q next ih =>
      cases he : cache (center q) with
      | some w => simpa only [compile, he] using ih (answer q w) cache
      | none =>
          simp only [compile, he, DecisionTree.NoRepeats]
          exact ⟨fun w => ih (answer q w) _, fun w =>
            used_avoids_cache center answer (next (answer q w))
              (Function.update cache (center q) (some w)) (center q) (by simp)⟩

omit [Fintype A] [Fintype W] in
theorem queries_compile (center : Q → C) (answer : Q → W → A)
    (t : DecisionTree Q A R) (cache : C → Option W) (o : C → W) (hc : Consistent cache o) :
    (compile center answer t cache).queries o ≤
      t.queries (fun q => answer q (o (center q))) := by
  classical
  induction t generalizing cache with
  | leaf => simp [compile, DecisionTree.queries, DecisionTree.transcript]
  | query q next ih =>
      cases he : cache (center q) with
      | some w =>
          have ho := hc (center q) w he
          have hh := ih (answer q w) cache hc
          simp only [compile, he, DecisionTree.queries, DecisionTree.transcript, List.length_cons, ho]
          exact hh.trans (Nat.le_succ _)
      | none =>
          have hcache : Consistent (Function.update cache (center q) (some (o (center q)))) o := by
            intro c w hw
            by_cases h : c = center q
            · subst c
              simpa only [Function.update_self, Option.some.injEq] using hw
            · exact hc c w (by simpa only [Function.update_of_ne h] using hw)
          have hh := ih (answer q (o (center q))) _ hcache
          simpa only [compile, he, DecisionTree.queries, DecisionTree.transcript, List.length_cons] using
            Nat.add_le_add_right hh 1

omit [Fintype A] [Fintype W] in
theorem compile_valid (center : Q → C) (answer : Q → W → A)
    (D : Finset S → Finset Q) (O : Finset S → Finset C) (cap : Finset S → Prop)
    (hD : ∀ E, cap E → ∀ q ∈ D E, center q ∈ O E)
    (t : DecisionTree Q A R) (I : Finset Q) (J : Finset C) (cache : C → Option W)
    (ht : Protocol.Valid D cap I t) (hcache : Known cache J) (hJI : J ⊆ I.image center) :
    Protocol.Valid O cap J (compile center answer t cache) := by
  classical
  induction t generalizing I J cache with
  | leaf r =>
      obtain ⟨E, hE, hIE⟩ := ht
      refine ⟨E, hE, ?_⟩
      intro c hc
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (hJI hc)
      exact hD E hE q (hIE hq)
  | query q next ih =>
      cases he : cache (center q) with
      | some w =>
          simp only [compile, he]
          exact ih (answer q w) (insert q I) J cache (ht.2 _) hcache
            (hJI.trans (Finset.image_subset_image (Finset.subset_insert _ _)))
      | none =>
          simp only [compile, he]
          refine ⟨?_, ?_⟩
          · intro hc
            exact (hcache (center q)).mp hc he
          · intro w
            apply ih (answer q w) (insert q I) (insert (center q) J)
              (Function.update cache (center q) (some w)) (ht.2 _) (known_update cache J hcache _ w)
            apply Finset.insert_subset_iff.mpr
            exact ⟨Finset.mem_image.mpr ⟨q, Finset.mem_insert_self _ _, rfl⟩,
              hJI.trans (Finset.image_subset_image (Finset.subset_insert _ _))⟩

theorem adaptive_cached_close [Fintype C] [Fintype R] [Nonempty W]
    (center : Q → C) (answer : Q → W → A)
    (D : Finset S → Finset Q) (O : Finset S → Finset C) (cap : Finset S → Prop)
    (hD : ∀ E, cap E → ∀ q ∈ D E, center q ∈ O E)
    (N : ℕ) (hN : ∀ E, cap E → (O E).card ≤ N)
    (t : DecisionTree Q A R) (ht : Protocol.Valid D cap ∅ t)
    (μ ν : C → Law W) (δ : ℝ) (hδ : 0 ≤ δ)
    (hμν : ∀ c, Law.Close (μ c) (ν c) δ) :
    Law.Close
      ((Law.pi μ).map (fun o => t.output (fun q => answer q (o (center q)))))
      ((Law.pi ν).map (fun o => t.output (fun q => answer q (o (center q)))))
      ((N : ℝ) * δ) := by
  classical
  let cached := compile center answer t (fun _ => none)
  have hv : Protocol.Valid O cap ∅ cached := compile_valid center answer D O cap hD
    t ∅ ∅ (fun _ => none) ht (by intro c; simp) (by simp)
  have hnr := Protocol.valid_no_repeats O cap cached ∅ hv
  have hh : Protocol.height cached ≤ N := by
    simpa using Protocol.valid_height O cap N hN cached ∅ hv
  have hclose := Protocol.lazy_close μ ν δ hδ hμν cached N hh
  have hout (o : C → W) : cached.output o = t.output (fun q => answer q (o (center q))) :=
    output_compile center answer t _ o (fun c w h => by cases h)
  intro E
  rw [Law.prob_map, Law.prob_map]
  have he : (fun o : C → W => t.output (fun q => answer q (o (center q)))) ⁻¹' E =
      {o | cached.output o ∈ E} := by
    ext o
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hout]
  rw [he, DecisionTree.deferred_sampling μ cached hnr E,
    DecisionTree.deferred_sampling ν cached hnr E]
  exact hclose E

end Caching

end SteinerLowerBound
