module

public import SteinerUpperBound.Matching.Padded.Opening

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ)

namespace Cache

def PreparedBound (s : Cache S Q) : Prop := ∀ v, s.prepared v = true → 0 < s.requests v

theorem empty_preparedBound : PreparedBound S Q (empty S Q) := by
  intro v hv
  cases hv

theorem idealNext_requests_mono (height maxLevel : ℕ) (v : V) (cursor : ℕ)
    (s : Cache S Q) (ranks : E → Fin Q) (u : V) :
    s.requests u ≤ (idealNext S Q height maxLevel v cursor s ranks).2.requests u := by
  classical
  rw [idealNext_requests]
  by_cases hu : u = v
  · subst u; simp
  · simp [Function.update_of_ne hu]

theorem idealNext_preparedBound (height maxLevel : ℕ) (v : V) (cursor : ℕ)
    (s : Cache S Q) (ranks : E → Fin Q) (hs : PreparedBound S Q s) :
    PreparedBound S Q (idealNext S Q height maxLevel v cursor s ranks).2 := by
  classical
  unfold idealNext
  cases hp : s.prepared v with
  | true =>
    simp only [↓reduceIte]
    have hh := idealNextLoop_administration S Q height v cursor (maxLevel + 1)
      { s with requests := Function.update s.requests v (s.requests v + 1) } ranks
    intro u hu
    rw [hh.2]
    have hold : s.prepared u = true := by simpa only [hh.1] using hu
    by_cases huv : u = v
    · subst u; simp
    · simpa only [Function.update_of_ne huv] using hs u hold
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hh := idealNextLoop_administration S Q height v cursor (maxLevel + 1)
      { s with requests := Function.update s.requests v (s.requests v + 1),
               prepared := Function.update s.prepared v true } ranks
    intro u hu
    rw [hh.2]
    by_cases huv : u = v
    · subst u; simp
    · have hold : s.prepared u = true := by
        simpa only [hh.1, Function.update_of_ne huv] using hu
      simpa only [Function.update_of_ne huv] using hs u hold

end Cache

structure Accounted {A : Type*} [Fintype E] (ranks : E → Fin Q)
    (before : Cache S Q) (r : LocalRun S Q A) : Prop where
  safe : RunSafe S Q ranks r
  prior : Cache.PriorCountBound S Q r.cache ranks
  prepared : Cache.PreparedBound S Q r.cache
  monotone : ∀ v, before.requests v ≤ r.cache.requests v

namespace Oracle

variable [Fintype V] [Fintype E] (P : Parameters S)

theorem idealScan_accounted
    (call : Entry S P.rankCard → Cache S P.rankCard → Memo E →
      (E → Fin P.rankCard) → LocalRun S P.rankCard Bool)
    (ranks : E → Fin P.rankCard) (hn : Function.Injective ranks)
    (v : V) (cutoff : ℕ)
    (hcall : ∀ x t μ, Cache.Invariant S P.rankCard t → Cache.Consistent S P.rankCard t ranks →
      Cache.PriorCountBound S P.rankCard t ranks → Cache.PreparedBound S P.rankCard t →
      x.rank.val < cutoff → Accounted S P.rankCard ranks t (call x t μ ranks))
    (cursor fuel : ℕ) (s : Cache S P.rankCard) (μ : Memo E)
    (hs : Cache.Invariant S P.rankCard s) (hc : Cache.Consistent S P.rankCard s ranks)
    (hp : Cache.PriorCountBound S P.rankCard s ranks) (hb : Cache.PreparedBound S P.rankCard s)
    (hcursor : cursor ≤ s.requests v) :
    Accounted S P.rankCard ranks s (idealScan S P call v cutoff cursor fuel s μ ranks) := by
  induction fuel generalizing cursor s μ with
  | zero => exact ⟨⟨hs, hc⟩, hp, hb, fun _ => le_refl _⟩
  | succ fuel ih =>
    rw [idealScan]
    let answer := Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks
    have ha := Cache.idealNext_safe S P v cursor s ranks hs hc
    have hpa := Cache.idealNext_priorCountBound S P v cursor s ranks hs hc hn hp hcursor
    have hba := Cache.idealNext_preparedBound S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks hb
    have hma := Cache.idealNext_requests_mono S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks
    cases hhit : (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks).1 with
    | none => exact ⟨⟨ha.invariant, ha.consistent⟩, hpa, hba, hma⟩
    | some x =>
      dsimp only
      by_cases hk : x.rank.val < cutoff
      · simp only [hk, ↓reduceIte]
        have hr := hcall x answer.2 μ ha.invariant ha.consistent hpa hba hk
        cases hv : (call x answer.2 μ ranks).value with
        | true =>
          simp only [↓reduceIte]
          exact ⟨⟨hr.safe.invariant, hr.safe.consistent⟩, hr.prior, hr.prepared,
            fun u => (hma u).trans (hr.monotone u)⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hnext : answer.2.requests v = s.requests v + 1 := by
            dsimp only [answer]
            rw [Cache.idealNext_requests, Function.update_self]
          have hpos : cursor + 1 ≤ (call x answer.2 μ ranks).cache.requests v := by
            have hm := hr.monotone v
            omega
          have ht := ih (cursor + 1) (call x answer.2 μ ranks).cache (call x answer.2 μ ranks).memo
            hr.safe.invariant hr.safe.consistent hr.prior hr.prepared hpos
          exact ⟨⟨ht.safe.invariant, ht.safe.consistent⟩, ht.prior, ht.prepared,
            fun u => (hma u).trans ((hr.monotone u).trans (ht.monotone u))⟩
      · simp only [hk, ↓reduceIte]
        exact ⟨⟨ha.invariant, ha.consistent⟩, hpa, hba, hma⟩

theorem idealEdge_accounted (d : Directed E) (rank : Fin P.rankCard) (ancestors : List (Directed E))
    (s : Cache S P.rankCard) (μ : Memo E) (ranks : E → Fin P.rankCard)
    (hn : Function.Injective ranks) (hs : Cache.Invariant S P.rankCard s)
    (hc : Cache.Consistent S P.rankCard s ranks) (hp : Cache.PriorCountBound S P.rankCard s ranks)
    (hb : Cache.PreparedBound S P.rankCard s) :
    Accounted S P.rankCard ranks s (idealEdge S P d rank ancestors s μ ranks) := by
  rw [idealEdge]
  cases hm : μ d with
  | some b => exact ⟨⟨hs, hc⟩, hp, hb, fun _ => le_refl _⟩
  | none =>
    let call := fun (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E)
        (world : E → Fin P.rankCard) =>
      if _h : x.rank.val < rank.val then
        idealEdge S P (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν world
      else ⟨false, ν, t, []⟩
    have hcall (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E)
        (ht : Cache.Invariant S P.rankCard t) (hct : Cache.Consistent S P.rankCard t ranks)
        (hpt : Cache.PriorCountBound S P.rankCard t ranks) (hbt : Cache.PreparedBound S P.rankCard t)
        (hk : x.rank.val < rank.val) : Accounted S P.rankCard ranks t (call x t ν ranks) := by
      dsimp only [call]
      simp only [hk, ↓reduceDIte]
      exact idealEdge_accounted (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν ranks hn ht hct hpt hbt
    have hr := idealScan_accounted S P call ranks hn (G.head d) rank.val hcall
      0 (P.Nstar + 1) s μ hs hc hp hb (Nat.zero_le _)
    exact ⟨⟨hr.safe.invariant, hr.safe.consistent⟩, hr.prior, hr.prepared, hr.monotone⟩
termination_by rank.val
decreasing_by exact hk

theorem idealVertex_accounted (v : V) (ranks : E → Fin P.rankCard) (hn : Function.Injective ranks) :
    Cache.PriorCountBound S P.rankCard (idealVertex S P v ranks).cache ranks ∧
      Cache.PreparedBound S P.rankCard (idealVertex S P v ranks).cache := by
  have hr := idealScan_accounted S P (idealRootCall S P v) ranks hn v P.rankCard
    (fun x t μ ht hc hp hb _hk =>
      idealEdge_accounted S P (G.away v x.edge) x.rank [] t μ ranks hn ht hc hp hb)
    0 (P.Nstar + 1) (Cache.empty S P.rankCard) (fun _ => none)
    (Cache.empty_invariant S P.rankCard P.rankCard_pos) (Cache.empty_consistent S P.rankCard ranks)
    (Cache.empty_priorCountBound S P.rankCard ranks) (Cache.empty_preparedBound S P.rankCard)
    (Nat.zero_le _)
  rw [idealVertex_cache]
  exact ⟨hr.prior, hr.prepared⟩

end Oracle

end SteinerUpperBound.Matching.Padded
