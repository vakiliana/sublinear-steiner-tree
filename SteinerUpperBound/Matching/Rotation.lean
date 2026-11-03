module

public import SteinerUpperBound.Matching.SimplePaths

@[expose] public section

namespace SteinerUpperBound.Matching

open scoped Classical BigOperators

variable {E : Type*} [Fintype E]

namespace Rank

def SameBelow (k : ℕ) (ρ σ : Rank E) : Prop :=
  ∀ i < k, ρ.edgeAt i = σ.edgeAt i

theorem SameBelow.refl (k : ℕ) (ρ : Rank E) : SameBelow k ρ ρ := fun _ _ => rfl

theorem SameBelow.symm {k : ℕ} {ρ σ : Rank E} (h : SameBelow k ρ σ) :
    SameBelow k σ ρ := fun i hi => (h i hi).symm

theorem SameBelow.trans {k : ℕ} {ρ σ τ : Rank E}
    (h : SameBelow k ρ σ) (h' : SameBelow k σ τ) : SameBelow k ρ τ :=
  fun i hi => (h i hi).trans (h' i hi)

theorem SameBelow.mono {i k : ℕ} {ρ σ : Rank E}
    (h : SameBelow k ρ σ) (hi : i ≤ k) : SameBelow i ρ σ :=
  fun j hj => h j (hj.trans_le hi)

theorem SameBelow.index_eq {k : ℕ} {ρ σ : Rank E} (h : SameBelow k ρ σ)
    (e : E) (he : ρ.index e < k) : σ.index e = ρ.index e := by
  apply (σ.edgeAt_eq_some_iff (ρ.index e) e).mp
  rw [← h (ρ.index e) he]
  exact (ρ.edgeAt_eq_some_iff (ρ.index e) e).mpr rfl

noncomputable def swapCopies (ρ : Rank E) (a b : E) : Rank E :=
  (Equiv.swap a b).trans ρ

@[simp] theorem swapCopies_apply (ρ : Rank E) (a b e : E) :
    ρ.swapCopies a b e = ρ (Equiv.swap a b e) := rfl

@[simp] theorem swapCopies_twice (ρ : Rank E) (a b : E) :
    (ρ.swapCopies a b).swapCopies a b = ρ := by
  ext e
  simp [swapCopies]

theorem swapCopies_edgeAt (ρ : Rank E) (a b : E) (i : ℕ) :
    (ρ.swapCopies a b).edgeAt i = (ρ.edgeAt i).map (Equiv.swap a b) := by
  by_cases hi : i < Fintype.card E
  · rw [(ρ.swapCopies a b).edgeAt_eq_some i hi, ρ.edgeAt_eq_some i hi]
    rfl
  · rw [(ρ.swapCopies a b).edgeAt_eq_none i (Nat.le_of_not_gt hi),
      ρ.edgeAt_eq_none i (Nat.le_of_not_gt hi)]
    rfl

theorem SameBelow.swapCopies {k : ℕ} {ρ σ : Rank E} (h : SameBelow k ρ σ) (a b : E) :
    SameBelow k (ρ.swapCopies a b) (σ.swapCopies a b) := by
  intro i hi
  rw [swapCopies_edgeAt, swapCopies_edgeAt, h i hi]

theorem sameBelow_swapCopies_iff (k : ℕ) (ρ σ : Rank E) (a b : E) :
    SameBelow k (ρ.swapCopies a b) (σ.swapCopies a b) ↔ SameBelow k ρ σ := by
  constructor
  · intro h
    simpa using h.swapCopies a b
  · exact fun h => h.swapCopies a b

theorem sameBelow_swapCopies_high (k : ℕ) (ρ : Rank E) (a b : E)
    (ha : k ≤ ρ.index a) (hb : k ≤ ρ.index b) :
    SameBelow k (ρ.swapCopies a b) ρ := by
  intro i hi
  have hip : i < Fintype.card E := hi.trans_le (ha.trans (ρ.index_lt a).le)
  rw [swapCopies_edgeAt, ρ.edgeAt_eq_some i hip]
  simp only [Option.map_some, Option.some.injEq]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have he := congrArg ρ.index h
    simp only [index_at] at he
    omega
  · intro h
    have he := congrArg ρ.index h
    simp only [index_at] at he
    omega

/-- Rotate along a reverse stack by successively swapping its end with its parents. -/
noncomputable def bubble (ρ : Rank E) (anchor : E) (xs : List E) : Rank E :=
  xs.foldl (fun σ x => σ.swapCopies anchor x) ρ

@[simp] theorem bubble_nil (ρ : Rank E) (a : E) : ρ.bubble a [] = ρ := rfl

theorem bubble_cons (ρ : Rank E) (a x : E) (xs : List E) :
    ρ.bubble a (x :: xs) = (ρ.swapCopies a x).bubble a xs := rfl

theorem bubble_append (ρ : Rank E) (a : E) (xs ys : List E) :
    ρ.bubble a (xs ++ ys) = (ρ.bubble a xs).bubble a ys := by
  exact List.foldl_append

theorem bubble_apply_of_notMem (ρ : Rank E) (a e : E) (xs : List E)
    (he : e ≠ a) (hx : e ∉ xs) : ρ.bubble a xs e = ρ e := by
  induction xs generalizing ρ with
  | nil => rfl
  | cons x xs ih =>
    have hex : e ≠ x := fun h => hx (by simp [h])
    rw [bubble_cons, ih _ (fun h => hx (by simp [h]))]
    simp [Equiv.swap_apply_of_ne_of_ne he hex]

theorem bubble_sameBelow_iff (k : ℕ) (ρ σ : Rank E) (a : E) (xs : List E) :
    SameBelow k (ρ.bubble a xs) (σ.bubble a xs) ↔ SameBelow k ρ σ := by
  induction xs generalizing ρ σ with
  | nil => rfl
  | cons x xs ih =>
    rw [bubble_cons, bubble_cons, ih, sameBelow_swapCopies_iff]

theorem bubble_high (k : ℕ) (ρ : Rank E) (a : E) (xs : List E)
    (h : ∀ e ∈ a :: xs, k ≤ ρ.index e) :
    SameBelow k (ρ.bubble a xs) ρ := by
  induction xs generalizing ρ with
  | nil => exact SameBelow.refl _ _
  | cons x xs ih =>
    rw [bubble_cons]
    have hs := sameBelow_swapCopies_high k ρ a x (h a (by simp)) (h x (by simp))
    have hh : ∀ e ∈ a :: xs, k ≤ (ρ.swapCopies a x).index e := by
      intro e he
      unfold index
      rw [swapCopies_apply]
      by_cases hea : e = a
      · subst e
        simpa [index] using h x (by simp)
      · by_cases hex : e = x
        · subst e
          simpa [index] using h a (by simp)
        · simpa [index, Equiv.swap_apply_of_ne_of_ne hea hex] using h e (by simp_all)
    exact (ih _ hh).trans hs

theorem bubble_anchor_last (ρ : Rank E) (a : E) (xs : List E)
    (hn : (a :: xs).Nodup) :
    ρ.bubble a xs a = ρ ((a :: xs).getLast (by simp)) := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    have hx : x ∉ a :: xs := by
      have hnd : ((a :: xs) ++ [x]).Nodup := by simpa using hn
      intro hx
      exact (List.nodup_append.mp hnd).2.2 x hx x (by simp) rfl
    have hxa : x ≠ a := fun h => hx (by simp [h])
    rw [bubble_append]
    change (ρ.bubble a xs).swapCopies a x a = _
    simp only [swapCopies_apply, Equiv.swap_apply_left]
    rw [bubble_apply_of_notMem ρ a x xs hxa (fun h => hx (by simp [h]))]
    simp

theorem bubble_first_after (ρ : Rank E) (a : E) (pre : List E) (f : E) (post : List E)
    (hn : (a :: (pre ++ f :: post)).Nodup) :
    ρ.bubble a (pre ++ f :: post) f = ρ.bubble a pre a := by
  have hf : f ≠ a := by
    intro h
    subst f
    exact (List.nodup_cons.mp hn).1 (by simp)
  have hfp : f ∉ post := by
    have hnd := List.nodup_append.mp (List.nodup_cons.mp hn).2
    exact (List.nodup_cons.mp hnd.2.1).1
  rw [bubble_append, bubble_cons,
    bubble_apply_of_notMem _ a f post hf hfp]
  simp only [swapCopies_apply, Equiv.swap_apply_right]

theorem bubble_injective (a : E) (xs : List E) :
    Function.Injective (fun ρ : Rank E => ρ.bubble a xs) := by
  induction xs with
  | nil => exact Function.injective_id
  | cons x xs ih =>
    intro ρ σ h
    change ρ.bubble a (x :: xs) = σ.bubble a (x :: xs) at h
    rw [bubble_cons, bubble_cons] at h
    have hs := ih h
    have he := congrArg (fun τ : Rank E => τ.swapCopies a x) hs
    simpa using he

end Rank

namespace Graph

variable {V : Type*} (G : Graph V E)

/-- The permutation constructed from an invocation stack, not a certificate. -/
noncomputable def rotated (_G : Graph V E) (ρ : Rank E) (d : Directed E)
    (parents : List (Directed E)) :
    Rank E := ρ.bubble d.1 (parents.map Prod.fst)

theorem rotation_prefix_facts (ρ : Rank E) (d : Directed E)
    (pre post : List (Directed E)) (h : G.ValidStack ρ ((d :: pre) ++ post)) :
    let c := (d :: pre).getLast (by simp)
    let τ := ρ.bubble d.1 (pre.map Prod.fst)
    τ.index d.1 = ρ.index c.1 ∧
      (∀ f ∈ post, τ f.1 = ρ f.1) ∧
      Rank.SameBelow (ρ.index c.1) (G.rotated ρ d (pre ++ post)) τ := by
  classical
  let c := (d :: pre).getLast (by simp)
  let τ := ρ.bubble d.1 (pre.map Prod.fst)
  have hn := G.validStack_copies_nodup ρ h
  rw [List.map_append, List.nodup_append] at hn
  have hc : c ∈ d :: pre := List.getLast_mem (by simp)
  have har : τ d.1 = ρ c.1 := by
    dsimp only [τ, c]
    rw [Rank.bubble_anchor_last _ _ _ (by simpa using hn.1)]
    congr 1
    exact List.getLast_map (f := Prod.fst) (l := d :: pre) (by simp)
  have hfix (f : Directed E) (hf : f ∈ post) : τ f.1 = ρ f.1 := by
    have hnot : f.1 ∉ (d :: pre).map Prod.fst := by
      intro hm
      exact hn.2.2 _ hm _ (List.mem_map.mpr ⟨f, hf, rfl⟩) rfl
    apply Rank.bubble_apply_of_notMem
    · intro heq
      exact hnot (by simp [heq])
    · intro hm
      exact hnot (by simp [hm])
  have hpair := G.validStack_pairwise ρ h
  rw [List.pairwise_append] at hpair
  have hcut : Rank.SameBelow (ρ.index c.1) (G.rotated ρ d (pre ++ post)) τ := by
    simp only [rotated, List.map_append, Rank.bubble_append]
    apply Rank.bubble_high
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst e
      exact (congrArg Fin.val har).symm.le
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
      have hlt := hpair.2.2 c hc f hf
      change ρ.index c.1 ≤ τ.index f.1
      simpa only [Rank.index, hfix f hf] using hlt.le
  exact ⟨congrArg Fin.val har, hfix, hcut⟩

theorem rotation_no_branch_le (ρ σ : Rank E) (d : Directed E)
    (pre : List (Directed E)) (a b : Directed E) (xs ys : List (Directed E))
    (hρ : G.ValidStack ρ ((d :: pre) ++ a :: xs))
    (hσ : G.ValidStack σ ((d :: pre) ++ b :: ys))
    (himage : G.rotated ρ d (pre ++ a :: xs) = G.rotated σ d (pre ++ b :: ys))
    (hle : ρ.index ((d :: pre).getLast (by simp)).1 ≤
      σ.index ((d :: pre).getLast (by simp)).1) : a = b := by
  classical
  let c := (d :: pre).getLast (by simp)
  let α := ρ.index c.1
  let β := σ.index c.1
  let τ := ρ.bubble d.1 (pre.map Prod.fst)
  let υ := σ.bubble d.1 (pre.map Prod.fst)
  let η := G.rotated ρ d (pre ++ a :: xs)
  have hstepρ : G.StackStep ρ c a :=
    hρ.2.rel_getLast_head_of_append (by simp) (by simp)
  have hstepσ : G.StackStep σ c b :=
    hσ.2.rel_getLast_head_of_append (by simp) (by simp)
  have hfρ := G.rotation_prefix_facts ρ d pre (a :: xs) hρ
  have hfσ := G.rotation_prefix_facts σ d pre (b :: ys) hσ
  have hnρ := G.validStack_copies_nodup ρ hρ
  have hnσ := G.validStack_copies_nodup σ hσ
  have hfirstρ : η a.1 = τ d.1 := by
    dsimp only [η, τ, rotated]
    simp only [List.map_append, List.map_cons]
    apply Rank.bubble_first_after
    simpa only [List.map_append, List.map_cons, List.cons_append] using hnρ
  have hfirstσ : η b.1 = υ d.1 := by
    rw [show η = G.rotated σ d (pre ++ b :: ys) from himage]
    dsimp only [υ, rotated]
    simp only [List.map_append, List.map_cons]
    apply Rank.bubble_first_after
    simpa only [List.map_append, List.map_cons, List.cons_append] using hnσ
  by_contra hab
  have habcopy : a.1 ≠ b.1 := by
    intro heq
    exact hab (G.directed_eq_of_head heq (hstepρ.2.symm.trans hstepσ.2))
  have hαβ : α < β := by
    have hne : α ≠ β := by
      intro heq
      have haα : η.index a.1 = α := (congrArg Fin.val hfirstρ).trans hfρ.1
      have hbβ : η.index b.1 = β := (congrArg Fin.val hfirstσ).trans hfσ.1
      exact habcopy (η.index_injective (haα.trans (heq.trans hbβ.symm)))
    exact lt_of_le_of_ne hle hne
  have hcutρ : Rank.SameBelow α η τ := hfρ.2.2
  have hcutσ : Rank.SameBelow β η υ := by
    simpa only [η, himage] using hfσ.2.2
  have hcutτυ : Rank.SameBelow α τ υ :=
    hcutρ.symm.trans (hcutσ.mono hαβ.le)
  have hcut : Rank.SameBelow α ρ σ :=
    (Rank.bubble_sameBelow_iff α ρ σ d.1 (pre.map Prod.fst)).mp hcutτυ
  have haη : η.index a.1 = α := (congrArg Fin.val hfirstρ).trans hfρ.1
  have haυ : υ.index a.1 = α := by
    simpa only [haη] using hcutσ.index_eq a.1 (by simpa only [haη] using hαβ)
  have hnota : a.1 ∉ (d :: pre).map Prod.fst := by
    rw [List.map_append, List.nodup_append] at hnρ
    intro hm
    exact hnρ.2.2 _ hm _ (by simp) rfl
  have hfixσ : υ a.1 = σ a.1 :=
    Rank.bubble_apply_of_notMem σ d.1 a.1 (pre.map Prod.fst)
      (fun heq => hnota (by simp [heq])) (fun hm => hnota (by simp [hm]))
  have haσ : σ.index a.1 = α := by simpa only [Rank.index, hfixσ] using haυ
  have hpref : G.greedyPrefix ρ α = G.greedyPrefix σ α := G.greedyPrefix_congr α hcut
  have hca : c ∈ (d :: pre) ++ a :: xs := by
    exact List.mem_append_left _ (List.getLast_mem (by simp))
  have hcb : c ∈ (d :: pre) ++ b :: ys := by
    exact List.mem_append_left _ (List.getLast_mem (by simp))
  have hfreecρ := hρ.1 c hca
  have hfreeaρ := hρ.1 a (by simp)
  have hfreecσ := hσ.1 c hcb
  have htail : G.Free (G.greedyPrefix σ α) (G.tail a) := by
    rw [← hpref]
    exact G.free_mono (G.greedyPrefix_mono ρ hstepρ.1.le) hfreeaρ
  have hhead : G.Free (G.greedyPrefix σ α) (G.head a) := by
    rw [← hpref, ← hstepρ.2]
    exact hfreecρ
  have haa : G.Accepted σ a.1 := by
    change G.Admissible (G.greedyPrefix σ (σ.index a.1)) a.1
    rw [haσ]
    cases a with | mk e orient => cases orient <;> first | exact ⟨hhead, htail⟩ | exact ⟨htail, hhead⟩
  have hamem : a.1 ∈ G.greedyPrefix σ β :=
    (G.mem_greedyPrefix σ β a.1).mpr ⟨haσ.trans_lt hαβ, haa⟩
  exact hfreecσ a.1 hamem (by rw [hstepρ.2]; exact G.head_incident a)

theorem rotation_no_branch (ρ σ : Rank E) (d : Directed E)
    (pre : List (Directed E)) (a b : Directed E) (xs ys : List (Directed E))
    (hρ : G.ValidStack ρ ((d :: pre) ++ a :: xs))
    (hσ : G.ValidStack σ ((d :: pre) ++ b :: ys))
    (himage : G.rotated ρ d (pre ++ a :: xs) = G.rotated σ d (pre ++ b :: ys)) : a = b := by
  rcases le_total (ρ.index ((d :: pre).getLast (by simp)).1)
    (σ.index ((d :: pre).getLast (by simp)).1) with hle | hle
  · exact G.rotation_no_branch_le ρ σ d pre a b xs ys hρ hσ himage hle
  · exact (G.rotation_no_branch_le σ ρ d pre b a ys xs hσ hρ himage.symm hle).symm

theorem rotation_suffix_unique (ρ σ : Rank E) (d : Directed E)
    (pre xs ys : List (Directed E))
    (hρ : G.ValidStack ρ ((d :: pre) ++ xs))
    (hσ : G.ValidStack σ ((d :: pre) ++ ys))
    (himage : G.rotated ρ d (pre ++ xs) = G.rotated σ d (pre ++ ys))
    (hlen : xs.length = ys.length) : xs = ys := by
  induction xs generalizing pre ys with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    exact hy.symm
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      have hab := G.rotation_no_branch ρ σ d pre a b xs ys hρ hσ himage
      subst b
      have hρ' : G.ValidStack ρ ((d :: (pre ++ [a])) ++ xs) := by
        simpa [List.append_assoc] using hρ
      have hσ' : G.ValidStack σ ((d :: (pre ++ [a])) ++ ys) := by
        simpa [List.append_assoc] using hσ
      have hi' : G.rotated ρ d ((pre ++ [a]) ++ xs) =
          G.rotated σ d ((pre ++ [a]) ++ ys) := by
        simpa [List.append_assoc] using himage
      have ht := ih (pre ++ [a]) ys hρ' hσ' hi' (Nat.succ.inj hlen)
      exact congrArg (List.cons a) ht

/-- Fixed image and stack length determine both the original order and the stack. -/
theorem rotation_preimage_unique (ρ σ : Rank E) (d : Directed E)
    (xs ys : List (Directed E))
    (hρ : G.ValidStack ρ (d :: xs)) (hσ : G.ValidStack σ (d :: ys))
    (himage : G.rotated ρ d xs = G.rotated σ d ys)
    (hlen : xs.length = ys.length) : ρ = σ ∧ xs = ys := by
  have hxy := G.rotation_suffix_unique ρ σ d [] xs ys
    (by simpa using hρ) (by simpa using hσ) (by simpa using himage) hlen
  subst ys
  exact ⟨Rank.bubble_injective d.1 (xs.map Prod.fst) himage, rfl⟩

end Graph

end SteinerUpperBound.Matching
