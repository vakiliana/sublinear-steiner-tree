module

public import SteinerUpperBound.Matching.Padded.NextCoupling

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open scoped Classical

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ)

namespace Parameters

variable [Fintype V] (P : Parameters S)

theorem Nstar_lt_pow : P.Nstar < 2 ^ P.sortHeight :=
  Nat.lt_pow_succ_log_self (by decide) _

theorem copies_le_sortCapacity [Fintype E] : Fintype.card E ≤ 2 ^ P.sortHeight := by
  have hs := S.copies_le_slots
  have hn := P.size_le
  have hh := Nstar_lt_pow S P
  omega

theorem length_lt_Nstar (v : V) : S.length v < P.Nstar := by
  have hs := S.length_le_total v
  have hn := P.size_le
  omega

end Parameters

namespace Cache

theorem administrative_invariant (s : Cache S Q) (hs : Invariant S Q s)
    (prepared : V → Bool) (requests : V → ℕ) :
    Invariant S Q { s with prepared := prepared, requests := requests } :=
  ⟨hs.legal, ⟨hs.records.unique, hs.records.valid, hs.records.complete⟩,
    ⟨hs.ready.unique, hs.ready.valid, hs.ready.ordered, hs.ready.covers⟩⟩

theorem next_bound_le (H : ℕ) (s : Cache S (2 ^ H)) (v : V)
    (hb : boundary S (2 ^ H) s v < 2 ^ H) :
    Buckets.bound (s.level v + 1) ≤ 2 ^ H := by
  have hQ : Buckets.bound (H + 1) = 2 ^ H := rfl
  have hl : s.level v < H + 1 := by
    by_contra hn
    have hh := Buckets.bound_mono (Nat.le_of_not_gt hn)
    change Buckets.bound (H + 1) ≤ boundary S (2 ^ H) s v at hh
    omega
  exact (Buckets.bound_mono (Nat.succ_le_of_lt hl)).trans_eq hQ

theorem idealExtend_invariant [Fintype E] (height : ℕ) (v : V) (s : Cache S Q)
    (ranks : E → Fin Q) (hs : Invariant S Q s) (hc : Consistent S Q s ranks)
    (hlen : Fintype.card E ≤ 2 ^ height) :
    Invariant S Q (idealExtend S Q height v s ranks) ∧
      Consistent S Q (idealExtend S Q height v s ranks) ranks := by
  classical
  unfold idealExtend
  split_ifs with hb
  · have hr := Posterior.ideal_records_ready S Q height s v ranks hc hs.records hs.ready hlen
    exact ⟨⟨Posterior.ideal_legal S Q height s v ranks hs.legal hc hb, hr.1, hr.2⟩,
      Posterior.ideal_consistent S Q height s v ranks hc⟩
  · exact ⟨hs, hc⟩

theorem idealExtend_levels (height : ℕ) (v : V) (s : Cache S Q) (ranks : E → Fin Q)
    (hb : Buckets.bound (s.level v + 1) ≤ Q) :
    (idealExtend S Q height v s ranks).level =
      Function.update s.level v (s.level v + 1) := by
  simp only [idealExtend, hb, ↓reduceIte, Posterior.ideal, Kernel.final, finish,
    Kernel.commit_levels]

theorem available_probe (s : Cache S Q) (v : V) (cursor : ℕ) :
    (available S Q v cursor s).map Entry.edge = probe S Q s v cursor := by
  unfold available probe
  rw [Array.getElem?_toList]
  cases hg : (s.ready v)[cursor]? with
  | none => rfl
  | some x => by_cases hx : x.rank.val < boundary S Q s v <;> simp [hx]

theorem available_spec (s : Cache S Q) (hs : Ready S Q s) (v : V) (cursor : ℕ)
    (x : Entry S Q) (hx : available S Q v cursor s = some x) :
    x.source.1 = v ∧ EntryValid S Q x ∧ s.assigned x.edge = some x.rank := by
  unfold available at hx
  cases hg : (s.ready v)[cursor]? with
  | none => simp only [hg, Option.bind_none] at hx; cases hx
  | some y =>
    simp only [hg, Option.bind_some] at hx
    split_ifs at hx with hy
    · have hxy := Option.some.inj hx
      subst x
      apply hs.valid v y
      apply List.mem_of_getElem?
      simpa only [Array.getElem?_toList] using hg

theorem incident_rank_ordered [Fintype E] (ranks : E → Fin Q)
    (hn : Function.Injective ranks) (v : V) :
    (G.candidates (UniformOrder.order ranks) (Fintype.card E) v).Pairwise
      (fun e f => (ranks e).val ≤ (ranks f).val) :=
  (G.candidates_pairwise (UniformOrder.order ranks) (Fintype.card E) v).imp fun {e f} h => by
    have hh := (UniformOrder.order_lt ranks hn e f).mp h
    exact Nat.le_of_lt hh

theorem available_prefix [Fintype E] (s : Cache S Q) (hs : Invariant S Q s)
    (ranks : E → Fin Q) (hc : Consistent S Q s ranks) (hn : Function.Injective ranks)
    (v : V) (cursor : ℕ) :
    (available S Q v cursor s).map Entry.edge =
      ((G.candidates (UniformOrder.order ranks) (Fintype.card E) v)[cursor]?).bind
        (fun e => if (ranks e).val < boundary S Q s v then some e else none) := by
  rw [available_probe, probe_lowEntries S Q s hs.ready, lowEntries_eq S Q s hs ranks hc hn]
  exact filter_threshold_lookup _ _ _ _ (incident_rank_ordered Q ranks hn v)

theorem available_at_full [Fintype E] (s : Cache S Q) (hs : Invariant S Q s)
    (ranks : E → Fin Q) (hc : Consistent S Q s ranks) (hn : Function.Injective ranks)
    (v : V) (cursor : ℕ) (hfull : boundary S Q s v = Q) :
    (available S Q v cursor s).map Entry.edge =
      (G.candidates (UniformOrder.order ranks) (Fintype.card E) v)[cursor]? := by
  rw [available_prefix S Q s hs ranks hc hn, hfull]
  cases hg : (G.candidates (UniformOrder.order ranks) (Fintype.card E) v)[cursor]? with
  | none => rfl
  | some e => simp only [Option.bind_some, (ranks e).isLt, ↓reduceIte]

theorem available_some_correct [Fintype E] (s : Cache S Q) (hs : Invariant S Q s)
    (ranks : E → Fin Q) (hc : Consistent S Q s ranks) (hn : Function.Injective ranks)
    (v : V) (cursor : ℕ) (x : Entry S Q) (hx : available S Q v cursor s = some x) :
    (G.candidates (UniformOrder.order ranks) (Fintype.card E) v)[cursor]? = some x.edge ∧
      ranks x.edge = x.rank := by
  have hp := available_prefix S Q s hs ranks hc hn v cursor
  rw [hx] at hp
  simp only [Option.map_some] at hp
  have hr := hc.1 x.edge x.rank (available_spec S Q s hs.ready v cursor x hx).2.2
  refine ⟨?_, hr⟩
  cases hg : (G.candidates (UniformOrder.order ranks) (Fintype.card E) v)[cursor]? with
  | none => simp only [hg, Option.bind_none] at hp; cases hp
  | some e =>
    simp only [hg, Option.bind_some] at hp
    split_ifs at hp with he
    · exact congrArg some (Option.some.inj hp).symm

end Cache

end SteinerUpperBound.Matching.Padded
