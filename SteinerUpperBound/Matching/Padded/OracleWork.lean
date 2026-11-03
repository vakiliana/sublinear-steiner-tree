module

public import SteinerUpperBound.Matching.Padded.AgedTrace

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E] (P : Parameters S)

def requestWork (A : Account S) : ℝ := 6 * A.rate * (P.rankExponent + 2 : ℕ)

def oraclePost {A' : Type*} (A : Account S) (baseline : ℝ) (r : LocalRun S P.rankCard A') : ℝ :=
  -requestWork S P A * Cache.requestValue S P.rankCard (fun _ => 1) r.cache -
    32 * A.rate * agedTrace baseline r.calls

namespace Oracle

variable (A : Account S)

theorem scan_oracle_bound
    (call : Entry S P.rankCard → Cache S P.rankCard → Memo E →
      Program (Command S) (LocalRun S P.rankCard Bool))
    (baseline : ℝ) (v : V) (cutoff : ℕ)
    (hcall : ∀ x s μ, x.rank.val < cutoff →
      (call x s μ).Bound (Command.oracleCharge A) 0 (oraclePost S P A (baseline + 1))
          (-requestWork S P A * Cache.requestValue S P.rankCard (fun _ => 1) s) ∧
        (call x s μ).Supported (fun r => r.calls ≠ []))
    (cursor fuel : ℕ) (s : Cache S P.rankCard) (μ : Memo E) :
    (Oracle.scan S P call v cutoff cursor fuel s μ).Bound (Command.oracleCharge A) 0
      (oraclePost S P A baseline)
      (-requestWork S P A * Cache.requestValue S P.rankCard (fun _ => 1) s) := by
  have hrate := A.rate_nonneg
  induction fuel generalizing cursor s μ with
  | zero =>
    apply Program.bound_ret
    simp only [oraclePost, agedTrace_nil, mul_zero, sub_zero, le_refl]
  | succ fuel ih =>
    rw [Oracle.scan]
    apply Program.bound_bind _ _ _ _
      (fun answer => -requestWork S P A * Cache.requestValue S P.rankCard (fun _ => 1) answer.2) _ _
    · intro leaf
      have hc := Cache.next_oracle_bound S P.rankCard P.rankCard_pos A P.sortHeight
        (P.rankExponent + 1) v cursor s leaf
      have hreq := Cache.next_requestValue_supported S P v cursor s leaf
      simp only [add_zero] at hc
      dsimp only
      rw [hreq]
      change _ ≤ _ at hc
      dsimp only [requestWork]
      linarith
    · intro answer
      cases hh : answer.1 with
      | none =>
        apply Program.bound_ret
        simp only [oraclePost, agedTrace_nil, mul_zero, sub_zero, le_refl]
      | some x =>
        dsimp only
        by_cases hk : x.rank.val < cutoff
        · simp only [hk, ↓reduceIte]
          have hchild := hcall x answer.2 μ hk
          apply Program.bound_bind_supported _ _ _ _ (oraclePost S P A (baseline + 1)) _ _
            (fun r => r.calls ≠ []) hchild.1 hchild.2
          intro r hne
          cases hb : r.value with
          | true =>
            simp only [↓reduceIte]
            apply Program.bound_ret
            simp only [oraclePost]
            rw [agedTrace_shift baseline r.calls]
            nlinarith [Nat.cast_nonneg (α := ℝ) r.calls.length]
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            apply Program.bound_bind _ _ _ _
              (fun result => oraclePost S P A baseline result - 32 * A.rate * agedTrace (baseline + 1) r.calls) _ _
            · have ht := (ih (cursor + 1) r.cache r.memo).shift
                (-32 * A.rate * agedTrace (baseline + 1) r.calls)
              simpa only [oraclePost, sub_eq_add_neg, neg_mul] using ht
            · intro result
              apply Program.bound_tick
              apply Program.bound_ret
              have hlen : (1 : ℝ) ≤ r.calls.length := by
                exact_mod_cast (show 1 ≤ r.calls.length from List.length_pos_iff.mpr hne)
              simp only [oraclePost, Command.oracleCharge]
              rw [agedTrace_append, agedTrace_shift baseline r.calls]
              norm_num only [Nat.cast_add, Nat.cast_ofNat]
              nlinarith [mul_nonneg A.rate_nonneg (sub_nonneg.mpr hlen)]
        · simp only [hk, ↓reduceIte]
          apply Program.bound_ret
          simp only [oraclePost, agedTrace_nil, mul_zero, sub_zero, le_refl]

theorem edge_oracle_bound (d : Directed E) (rank : Fin P.rankCard)
    (ancestors : List (Directed E)) (s : Cache S P.rankCard) (μ : Memo E) :
    (Oracle.edge S P d rank ancestors s μ).Bound (Command.oracleCharge A) 0
      (oraclePost S P A (ancestors.length : ℝ))
      (-requestWork S P A * Cache.requestValue S P.rankCard (fun _ => 1) s) := by
  have hrate := A.rate_nonneg
  rw [Oracle.edge]
  apply Program.bound_tick
  cases hm : μ d with
  | some value =>
    apply Program.bound_ret
    simp only [oraclePost, agedTrace_cons, agedTrace_nil, Command.oracleCharge]
    norm_num only [Nat.cast_ofNat]
    linarith
  | none =>
    let call := fun (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E) =>
      if _h : x.rank.val < rank.val then
        Oracle.edge S P (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν
      else .ret ⟨false, ν, t, []⟩
    have hcall (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E)
        (hk : x.rank.val < rank.val) :
        (call x t ν).Bound (Command.oracleCharge A) 0
          (oraclePost S P A ((ancestors.length : ℝ) + 1))
          (-requestWork S P A * Cache.requestValue S P.rankCard (fun _ => 1) t) ∧
        (call x t ν).Supported (fun r => r.calls ≠ []) := by
      dsimp only [call]
      simp only [hk, ↓reduceDIte]
      exact ⟨by simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using
        edge_oracle_bound (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν,
        edge_calls_nonempty S P _ _ _ _ _⟩
    have hs := scan_oracle_bound S P A call (ancestors.length : ℝ) (G.head d) rank.val
      hcall 0 (P.Nstar + 1) s μ
    apply Program.bound_bind _ _ _ _
      (fun result => oraclePost S P A (ancestors.length : ℝ) result - A.rate * 3) _ _
    · have ht := hs.shift (-(A.rate * 3))
      simpa only [Command.oracleCharge, sub_eq_add_neg, Nat.cast_ofNat] using ht
    · intro result
      apply Program.bound_tick
      apply Program.bound_ret
      simp only [oraclePost, agedTrace_cons, Command.oracleCharge]
      norm_num only [Nat.cast_ofNat]
      linarith
termination_by rank.val
decreasing_by exact hk

theorem vertex_oracle_bound (v : V) :
    (Oracle.vertex S P v).Bound (Command.oracleCharge A) 0 (oraclePost S P A (-1))
      (A.rate * (P.rankExponent + P.sortHeight + 12 : ℕ)) := by
  rw [Oracle.vertex]
  apply Program.bound_tick
  have hcall (x : Entry S P.rankCard) (s : Cache S P.rankCard) (μ : Memo E)
      (_h : x.rank.val < P.rankCard) :
      (rootCall S P v x s μ).Bound (Command.oracleCharge A) 0
        (oraclePost S P A ((-1 : ℝ) + 1))
        (-requestWork S P A * Cache.requestValue S P.rankCard (fun _ => 1) s) ∧
      (rootCall S P v x s μ).Supported (fun r => r.calls ≠ []) := by
    exact ⟨by simpa only [rootCall, List.length_nil, Nat.cast_zero, neg_add_cancel] using
      edge_oracle_bound S P A (G.away v x.edge) x.rank [] s μ,
      edge_calls_nonempty S P _ _ _ _ _⟩
  have hs := scan_oracle_bound S P A (rootCall S P v) (-1) v P.rankCard hcall
    0 (P.Nstar + 1) (Cache.empty S P.rankCard) (fun _ => none)
  have hz : -requestWork S P A * Cache.requestValue S P.rankCard (fun _ => 1)
      (Cache.empty S P.rankCard) = 0 := by rw [Cache.empty_requestValue, mul_zero]
  simp only [Command.oracleCharge, sub_self]
  apply Program.bound_bind _ _ _ _ (oraclePost S P A (-1)) _ _ (by simpa only [hz] using hs)
  intro result
  exact Program.bound_ret _ _ _ _ _ (le_refl _)

end Oracle

end SteinerUpperBound.Matching.Padded
