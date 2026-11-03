module

public import SteinerLowerBound.Screening.Budgets

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

inductive StopKind
  | cluster | starCounter | lucky | notices | closure
  deriving DecidableEq

structure Book (T : Type*) where
  noticed : Finset T
  exposed : Finset T
  stop : Option StopKind

def Book.initial {T : Type*} : Book T := ⟨∅, ∅, none⟩

variable {T C : Type*} [Fintype T]

noncomputable def noticeOrder (s : Finset T) : List T :=
  Finset.univ.toList.filter (fun u => decide (u ∈ s))

@[simp]
theorem mem_noticeOrder (s : Finset T) (u : T) : u ∈ noticeOrder s ↔ u ∈ s := by
  classical
  simp [noticeOrder]

@[simp]
theorem noticeOrder_toFinset (s : Finset T) : (noticeOrder s).toFinset = s := by
  classical
  ext u
  simp

noncomputable def addNotice (F H : C → Finset T) (s : Book T) (u : T) : Book T :=
  if u ∈ s.exposed then s else
    ⟨insert u s.noticed, TwoAnchor.closure F H (insert u s.exposed), s.stop⟩

noncomputable def addNotices (F H : C → Finset T) (s : Book T) (l : List T) : Book T :=
  l.foldl (addNotice F H) s

theorem addNotice_mono (F H : C → Finset T) (s : Book T) (u : T) :
    s.exposed ⊆ (addNotice F H s u).exposed := by
  classical
  by_cases hu : u ∈ s.exposed
  · simp [addNotice, hu]
  · simp only [addNotice, hu, ↓reduceIte]
    exact Finset.Subset.trans (Finset.subset_insert _ _)
      (TwoAnchor.subset_closure F H _)

theorem mem_addNotice (F H : C → Finset T) (s : Book T) (u : T) :
    u ∈ (addNotice F H s u).exposed := by
  classical
  by_cases hu : u ∈ s.exposed
  · simpa [addNotice, hu] using hu
  · simp only [addNotice, hu, ↓reduceIte]
    exact TwoAnchor.subset_closure F H _ (Finset.mem_insert_self _ _)

theorem addNotices_mono (F H : C → Finset T) (s : Book T) (l : List T) :
    s.exposed ⊆ (addNotices F H s l).exposed := by
  induction l generalizing s with
  | nil => exact Finset.Subset.rfl
  | cons u l ih => exact (addNotice_mono F H s u).trans (ih _)

theorem mem_addNotices (F H : C → Finset T) (s : Book T) (l : List T)
    {u : T} (hu : u ∈ l) : u ∈ (addNotices F H s l).exposed := by
  induction l generalizing s with
  | nil => simp at hu
  | cons v l ih =>
      rcases List.mem_cons.mp hu with rfl | hu
      · exact addNotices_mono F H _ l (mem_addNotice F H s u)
      · exact ih _ hu

theorem addNotices_closed (F H : C → Finset T) (s : Book T) (l : List T)
    (hs : TwoAnchor.Closed F H s.exposed) :
    TwoAnchor.Closed F H (addNotices F H s l).exposed := by
  induction l generalizing s with
  | nil => exact hs
  | cons u l ih =>
      apply ih
      by_cases hu : u ∈ s.exposed
      · simpa [addNotice, hu] using hs
      · simp only [addNotice, hu, ↓reduceIte]
        exact TwoAnchor.closure_closed F H _

theorem addNotices_noticed_subset (F H : C → Finset T) (s : Book T) (l : List T)
    (hs : s.noticed ⊆ s.exposed) :
    (addNotices F H s l).noticed ⊆ (addNotices F H s l).exposed := by
  classical
  induction l generalizing s with
  | nil => exact hs
  | cons u l ih =>
      apply ih
      by_cases hu : u ∈ s.exposed
      · simpa [addNotice, hu] using hs
      · simp only [addNotice, hu, ↓reduceIte]
        exact (Finset.insert_subset_insert u hs).trans (TwoAnchor.subset_closure F H _)

theorem addNotices_stop (F H : C → Finset T) (s : Book T) (l : List T) :
    (addNotices F H s l).stop = s.stop := by
  induction l generalizing s with
  | nil => rfl
  | cons u l ih =>
      rw [show addNotices F H s (u :: l) = addNotices F H (addNotice F H s u) l from rfl, ih]
      simp only [addNotice]
      split_ifs <;> rfl

variable {S G I : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

def UnitAt (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (q : Query (Terminal S G I) C) (u : Terminal S G I) : Prop :=
  ∃ c, q = .ct c u ∧ queryAnswer π F H h q = .unit

def Lucky (π : Equiv.Perm (Terminal S G I))
    (H : C → Finset (Terminal S G I)) (Q : Finset (Terminal S G I))
    (q : Query (Terminal S G I) C) : Prop :=
  ∃ c u, q = .ct c u ∧ specialPosition (π u) ∧ u ∉ Q ∧ π u ∈ H c

noncomputable def noticeCandidates (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C)
    (Q : Finset (Terminal S G I)) : Finset (Terminal S G I) :=
  Finset.univ.filter fun u => specialPosition (π u) ∧ u ∉ Q ∧
    (UnitAt π F H h q u ∨ D ≤ degree (h ++ [q]) u ∨
      t ≤ (counterLabels π F (h ++ [q]) u).card)

noncomputable def advance (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (s : Book (Terminal S G I))
    (q : Query (Terminal S G I) C) : Book (Terminal S G I) :=
  if s.stop ≠ none then s else
  if Lucky π H s.exposed q then {s with stop := some .lucky} else
  let s' := addNotices (relabel π F) (relabel π H) s
    (noticeOrder (noticeCandidates π F H D t h q s.exposed))
  let stop :=
    if t ≤ (marked π (h ++ [q])).card then some StopKind.cluster else
    if ∃ u, specialPosition (π u) ∧ u ∉ s'.exposed ∧
        t ≤ (counterLabels π H (h ++ [q]) u).card then some StopKind.starCounter else
    if R < s'.noticed.card then some StopKind.notices else
    if 2 * R < s'.exposed.card then some StopKind.closure else none
  {s' with stop := stop}

noncomputable def analyze (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) : Book (Terminal S G I) :=
  h.reverseRecOn Book.initial (fun h q s => advance π F H D t R h s q)

@[simp]
theorem analyze_nil (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ) :
    analyze π F H D t R [] = Book.initial := by simp [analyze]

@[simp]
theorem analyze_append (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    analyze π F H D t R (h ++ [q]) =
      advance π F H D t R h (analyze π F H D t R h) q := by simp [analyze]

def ContactsExposed (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (Q : Finset (Terminal S G I)) : Prop :=
  ∀ c u, Query.ct c u ∈ h → π u ∈ F c ∨ π u ∈ H c → u ∈ Q

theorem advance_none (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (s : Book (Terminal S G I))
    (q : Query (Terminal S G I) C)
    (hn : (advance π F H D t R h s q).stop = none) :
    s.stop = none ∧ ¬Lucky π H s.exposed q ∧
      (advance π F H D t R h s q).exposed =
        (addNotices (relabel π F) (relabel π H) s
          (noticeOrder (noticeCandidates π F H D t h q s.exposed))).exposed ∧
      ¬t ≤ (marked π (h ++ [q])).card := by
  classical
  unfold advance at hn ⊢
  split_ifs at hn ⊢ <;> simp_all

theorem advance_contacts (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (s : Book (Terminal S G I))
    (q : Query (Terminal S G I) C)
    (hF : Supported F) (hH : Supported H)
    (hs : ContactsExposed π F H h s.exposed)
    (hn : (advance π F H D t R h s q).stop = none) :
    ContactsExposed π F H (h ++ [q]) (advance π F H D t R h s q).exposed := by
  classical
  obtain ⟨_, hl, he, _⟩ := advance_none π F H D t R h s q hn
  rw [he]
  intro c u hu hmem
  rcases List.mem_append.mp hu with hu | hu
  · exact addNotices_mono _ _ _ _ (hs c u hu hmem)
  · have hq : q = .ct c u := (List.mem_singleton.mp hu).symm
    by_cases huQ : u ∈ s.exposed
    · exact addNotices_mono _ _ _ _ huQ
    have huF : π u ∈ F c := by
      rcases hmem with hm | hm
      · exact hm
      · exact False.elim (hl ⟨c, u, hq, hH c _ hm, huQ, hm⟩)
    apply mem_addNotices
    apply (mem_noticeOrder _ _).mpr
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF c _ huF, huQ, Or.inl ?_⟩
    refine ⟨c, hq, ?_⟩
    simp only [hq, queryAnswer]
    rw [TwoAnchor.anchor_positive _ _ _ _ _ ((mem_relabel _ _ _ _).mpr huF)]
    rfl

theorem analyze_contacts (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (hF : Supported F) (hH : Supported H)
    (h : List (Query (Terminal S G I) C))
    (hn : (analyze π F H D t R h).stop = none) :
    ContactsExposed π F H h (analyze π F H D t R h).exposed := by
  induction h using List.reverseRecOn with
  | nil => simp [ContactsExposed]
  | append_singleton h q ih =>
      rw [analyze_append] at hn ⊢
      exact advance_contacts π F H D t R h _ q hF hH
        (ih (advance_none π F H D t R h _ q hn).1) hn

theorem quiet_before_stop (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (hF : Supported F) (hH : Supported H)
    (h : List (Query (Terminal S G I) C))
    (hn : (analyze π F H D t R h).stop = none)
    (u : Terminal S G I) (hu : u ∉ (analyze π F H D t R h).exposed) :
    Quiet π F H h u := by
  intro c hc
  have hh := analyze_contacts π F H D t R hF hH h hn c u hc
  exact ⟨fun hm => hu (hh (Or.inl hm)), fun hm => hu (hh (Or.inr hm))⟩

theorem active_anchors_exposed (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (Q : Finset (Terminal S G I)) (hc : ContactsExposed π F H h Q) (c : C)
    (ha : TwoAnchor.active (relabel π F) (centerHistory h) c) :
    relabel π F c ⊆ Q := by
  intro u hu
  have hquery : (c, u) ∈ centerHistory h := (Finset.mem_filter.mp (ha.2 hu)).2
  exact hc c u ((mem_centerHistory h c u).mp hquery) (Or.inl ((mem_relabel _ _ _ _).mp hu))

theorem advance_exposed_cases (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (s : Book (Terminal S G I))
    (q : Query (Terminal S G I) C) :
    (advance π F H D t R h s q).exposed = s.exposed ∨
      (advance π F H D t R h s q).exposed =
        (addNotices (relabel π F) (relabel π H) s
          (noticeOrder (noticeCandidates π F H D t h q s.exposed))).exposed := by
  classical
  unfold advance
  split_ifs <;> simp

theorem analyze_closed (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) :
    TwoAnchor.Closed (relabel π F) (relabel π H) (analyze π F H D t R h).exposed := by
  induction h using List.reverseRecOn with
  | nil =>
      simp only [analyze_nil, Book.initial]
      intro c hc
      have hh := Finset.card_le_card hc.2.1
      have hf := hc.1
      simp only [Finset.card_empty] at hh
      omega
  | append_singleton h q ih =>
      rw [analyze_append]
      rcases advance_exposed_cases π F H D t R h (analyze π F H D t R h) q with he | he
      · rw [he]
        exact ih
      · rw [he]
        exact addNotices_closed _ _ _ _ ih

theorem advance_none_star (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (s : Book (Terminal S G I))
    (q : Query (Terminal S G I) C)
    (hn : (advance π F H D t R h s q).stop = none)
    (u : Terminal S G I) (hs : specialPosition (π u))
    (hu : u ∉ (advance π F H D t R h s q).exposed) :
    (counterLabels π H (h ++ [q]) u).card < t := by
  classical
  obtain ⟨hstop, hl, he, hm⟩ := advance_none π F H D t R h s q hn
  by_contra hb
  have hex : ∃ v, specialPosition (π v) ∧ v ∉
      (addNotices (relabel π F) (relabel π H) s
        (noticeOrder (noticeCandidates π F H D t h q s.exposed))).exposed ∧
      t ≤ (counterLabels π H (h ++ [q]) v).card :=
    ⟨u, hs, he ▸ hu, Nat.le_of_not_gt hb⟩
  have hres : (advance π F H D t R h s q).stop = some .starCounter := by
    simp only [advance, hstop, ne_eq, not_true_eq_false, ↓reduceIte, hl, hm, hex]
  rw [hres] at hn
  contradiction

theorem advance_none_thresholds (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (s : Book (Terminal S G I))
    (q : Query (Terminal S G I) C)
    (hn : (advance π F H D t R h s q).stop = none)
    (u : Terminal S G I) (hs : specialPosition (π u))
    (hu : u ∉ (advance π F H D t R h s q).exposed) :
    (marked π (h ++ [q])).card < t ∧ degree (h ++ [q]) u < D ∧
      (counterLabels π F (h ++ [q]) u).card < t ∧
        (counterLabels π H (h ++ [q]) u).card < t := by
  classical
  obtain ⟨_, _, he, hm⟩ := advance_none π F H D t R h s q hn
  have hnot : u ∉ noticeCandidates π F H D t h q s.exposed := by
    intro hc
    apply hu
    rw [he]
    exact mem_addNotices _ _ _ _ ((mem_noticeOrder _ _).mpr hc)
  have hout : u ∉ s.exposed := by
    intro hc
    apply hu
    rw [he]
    exact addNotices_mono _ _ _ _ hc
  have hd : ¬D ≤ degree (h ++ [q]) u := by
    intro hd
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hout, Or.inr (Or.inl hd)⟩)
  have hb : ¬t ≤ (counterLabels π F (h ++ [q]) u).card := by
    intro hb
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hout, Or.inr (Or.inr hb)⟩)
  exact ⟨Nat.lt_of_not_ge hm, Nat.lt_of_not_ge hd, Nat.lt_of_not_ge hb,
    advance_none_star π F H D t R h s q hn u hs hu⟩

theorem thresholds_before_stop (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ) (hD : 0 < D) (ht : 0 < t)
    (h : List (Query (Terminal S G I) C))
    (hn : (analyze π F H D t R h).stop = none)
    (u : Terminal S G I) (hs : specialPosition (π u))
    (hu : u ∉ (analyze π F H D t R h).exposed) :
    (marked π h).card < t ∧ degree h u < D ∧
      (counterLabels π F h u).card < t ∧ (counterLabels π H h u).card < t := by
  induction h using List.reverseRecOn with
  | nil =>
      simpa [marked, degree, counterLabels] using
        (show 0 < t ∧ 0 < D ∧ 0 < t ∧ 0 < t from ⟨ht, hD, ht, ht⟩)
  | append_singleton h q _ =>
      rw [analyze_append] at hn hu
      exact advance_none_thresholds π F H D t R h _ q hn u hs hu

theorem screenable_before_stop (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ) (hD : 0 < D) (ht : 0 < t)
    (hF : Supported F) (hH : Supported H)
    (h : List (Query (Terminal S G I) C))
    (hn : (analyze π F H D t R h).stop = none)
    (u : Terminal S G I) (hs : specialPosition (π u))
    (hu : u ∉ (analyze π F H D t R h).exposed) :
    Screenable π F H h u (3 * t + D * Fintype.card I) := by
  have hh := thresholds_before_stop π F H D t R hD ht h hn u hs hu
  refine ⟨hs, quiet_before_stop π F H D t R hF hH h hn u hu, ?_⟩
  have h1 : ((marked π h).card : ℝ) ≤ t := by exact_mod_cast hh.1.le
  have h2 : (degree h u : ℝ) ≤ D := by exact_mod_cast hh.2.1.le
  have h3 : ((counterLabels π F h u).card : ℝ) ≤ t := by exact_mod_cast hh.2.2.1.le
  have h4 : ((counterLabels π H h u).card : ℝ) ≤ t := by exact_mod_cast hh.2.2.2.le
  have hI : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  nlinarith

theorem third_positive_star_exposed (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (Q : Finset (Terminal S G I)) (hc : ContactsExposed π F H h Q)
    (hclosed : TwoAnchor.Closed (relabel π F) (relabel π H) Q)
    (hF : ∀ c, (F c).card ≤ 2)
    (hFH : ∀ c, (H c).Nonempty → F c ⊆ H c)
    (c : C)
    (hp : 3 ≤ (TwoAnchor.positives (relabel π F) (relabel π H) (centerHistory h) c).card) :
    relabel π H c ⊆ Q := by
  classical
  have hnot : ¬TwoAnchor.positives (relabel π F) (relabel π H) (centerHistory h) c ⊆
      relabel π F c := by
    intro hh
    have hcard := Finset.card_le_card hh
    rw [card_relabel] at hcard
    have hf := hF c
    omega
  obtain ⟨u, hup, huF⟩ := Finset.not_subset.mp hnot
  obtain ⟨i, hi, hai⟩ := (TwoAnchor.mem_positives_iff _ _ _ _ _).mp hup
  have ha : TwoAnchor.active (relabel π F) ((centerHistory h).take i.val) c ∧
      Disjoint (relabel π H c)
        (TwoAnchor.blocked (relabel π F) ((centerHistory h).take i.val) c) ∧
          u ∈ relabel π H c := by
    simpa [TwoAnchor.answer, huF] using hai
  have ha' : TwoAnchor.active (relabel π F) (centerHistory h) c :=
    ⟨ha.1.1, fun v hv => TwoAnchor.queried_take_subset _ _ _ (ha.1.2 hv)⟩
  have hFuQ := active_anchors_exposed π F H h Q hc c ha'
  have hmem : (c, u) ∈ centerHistory h := hi ▸ List.get_mem _ i
  have huQ := hc c u ((mem_centerHistory h c u).mp hmem)
    (Or.inr ((mem_relabel _ _ _ _).mp ha.2.2))
  have hFHu : relabel π F c ⊆ relabel π H c := by
    intro v hv
    apply (mem_relabel _ _ _ _).mpr
    exact hFH c ⟨π u, (mem_relabel _ _ _ _).mp ha.2.2⟩
      ((mem_relabel _ _ _ _).mp hv)
  exact hclosed c (TwoAnchor.visible_of_third _ _ Q c ha.1.1 hFuQ hFHu
    u ha.2.2 huQ huF)

end Screening

end SteinerLowerBound
