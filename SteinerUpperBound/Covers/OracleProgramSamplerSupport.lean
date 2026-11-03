module

public import SteinerUpperBound.Covers.OracleProgramSamplerIntegration

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {V M Q R S : Type*} {k : ℕ}

/-- Uniform draws have full support. This predicate excludes only potentially
zero-mass coin branches, not metric or retained-oracle decisions. -/
def UniformRandomness : Code M Q R → Prop
  | .pure _ => True
  | .metric _ next => ∀ a, UniformRandomness (next a)
  | .retained _ next => ∀ a, UniformRandomness (next a)
  | .uniform _ next => ∀ a, UniformRandomness (next a)
  | .coin _ _ => False
  | .tick _ next => UniformRandomness next

theorem uniformRandomness_bind (p : Code M Q R) (hp : UniformRandomness p)
    (next : R → Code M Q S) (hn : ∀ r, UniformRandomness (next r)) :
    UniformRandomness (p.bind next) := by
  induction p with
  | pure r => exact hn r
  | metric q cont ih => exact fun a => ih a (hp a)
  | retained q cont ih => exact fun a => ih a (hp a)
  | uniform n cont ih => exact fun a => ih a (hp a)
  | coin rate cont ih => exact hp.elim
  | tick n cont ih => exact ih hp

theorem uniformRandomness_map (p : Code M Q R) (hp : UniformRandomness p) (f : R → S) :
    UniformRandomness (p.map f) := by
  induction p with
  | pure r => trivial
  | metric q cont ih => exact fun a => ih a (hp a)
  | retained q cont ih => exact fun a => ih a (hp a)
  | uniform n cont ih => exact fun a => ih a (hp a)
  | coin rate cont ih => exact hp.elim
  | tick n cont ih => exact ih hp

theorem uniformRandomness_cap (p : Code M Q R) (hp : UniformRandomness p) (W : ℕ) :
    UniformRandomness (p.cap W) := by
  induction p generalizing W with
  | pure r => trivial
  | metric q cont ih =>
    simp only [Code.cap]
    split_ifs
    · exact fun a => ih a (hp a) _
    · trivial
  | retained q cont ih =>
    simp only [Code.cap]
    split_ifs
    · exact fun a => ih a (hp a) _
    · trivial
  | uniform n cont ih =>
    simp only [Code.cap]
    split_ifs
    · exact fun a => ih a (hp a) _
    · trivial
  | coin rate cont ih => exact hp.elim
  | tick n cont ih =>
    simp only [Code.cap]
    split_ifs
    · exact ih hp _
    · trivial

theorem uniformRandomness_mass_pos (m : M → ℝ) (p : Code M Q R)
    (hp : UniformRandomness p) :
    ∀ seed : (p.compile m).Seed, 0 < (p.compile m).law.mass seed := by
  induction p with
  | pure r =>
    intro seed
    cases seed
    change (0 : ℝ) < (Law.pure ()).mass ()
    norm_num [Law.pure]
  | metric q cont ih => exact ih (m q) (hp (m q))
  | retained q cont ih =>
    intro seed
    exact mul_pos (ih false (hp false) seed.1) (ih true (hp true) seed.2)
  | uniform n cont ih =>
    intro seed
    have hu : 0 < (Law.uniform (Fin (n + 1))).mass seed.1 := by
      simp [Law.uniform]
      positivity
    exact mul_pos hu (ih seed.1 (hp seed.1) seed.2)
  | coin rate cont ih => exact hp.elim
  | tick n cont ih => exact ih hp

theorem uniformRandomness_scan (cfg : Config V Q k) (q : Q) (B ψ : ℕ) (s : State Q)
    (next : Bool → State Q → Code (Sym2 V) Q R)
    (abort : State Q → Code (Sym2 V) Q R)
    (hn : ∀ v t, UniformRandomness (next v t)) (ha : ∀ t, UniformRandomness (abort t)) :
    UniformRandomness (scan cfg q B ψ s next abort) := by
  induction B generalizing ψ s with
  | zero => exact hn false s
  | succ B ih =>
    cases ψ with
    | zero => exact hn false s
    | succ ψ =>
      simp only [scan, UniformRandomness]
      split_ifs
      · exact ha s
      · intro y
        simp only [UniformRandomness]
        split_ifs
        · exact hn true s.draw
        · intro d
          exact ih _ _

theorem uniformRandomness_resolve (cfg : Config V Q k)
    (p : Code (Sym2 V) Q R) (hp : UniformRandomness p) (s : State Q) :
    UniformRandomness (resolve cfg p s) := by
  induction p generalizing s with
  | pure r => trivial
  | metric q cont ih => exact fun a => ih a (hp a) s
  | retained q cont ih =>
    simp only [resolve, UniformRandomness]
    cases he : s.cache q with
    | some v => exact ih v (hp v) _
    | none =>
      apply uniformRandomness_scan
      · exact fun v t => ih v (hp v) _
      · exact fun _ => True.intro
  | uniform n cont ih => exact fun a => ih a (hp a) s
  | coin rate cont ih => exact hp.elim
  | tick n cont ih => exact ih hp s

namespace Sampler

theorem uniformRandomness_member (q : Q) (u : Store Q)
    (next : Bool → Store Q → Code M Q R) (hn : ∀ v t, UniformRandomness (next v t)) :
    UniformRandomness (member q u next) := by
  unfold member
  apply uniformRandomness_bind
  · cases he : u.cache q <;> simp [Cache.resolve, he, UniformRandomness]
  · intro reply
    exact hn reply.1 _

theorem uniformRandomness_row (query : Fin (k + 1) → Q) (C used : ℕ) (u : Store Q)
    (next : Option (Fin (k + 1)) → ℕ → Store Q → Code M Q R)
    (abort : Store Q → Code M Q R)
    (hn : ∀ label used t, UniformRandomness (next label used t))
    (ha : ∀ t, UniformRandomness (abort t)) :
    UniformRandomness (row query C used u next abort) := by
  induction C generalizing used u with
  | zero => exact hn none used u
  | succ C ih =>
    simp only [row, UniformRandomness]
    split_ifs
    · exact ha u
    · intro y
      simp only [UniformRandomness]
      apply uniformRandomness_member
      intro v t
      cases v with
      | true => exact hn (some y) (used + 1) t
      | false => exact ih _ _

theorem uniformRandomness_program (query : Fin (k + 1) → Q) (root : Fin (k + 1))
    (C s B : ℕ) (cache : Q → Option Bool) :
    UniformRandomness (program query root C s B cache : Code M Q (Records Q k s)) := by
  suffices ∀ u, UniformRandomness (pool query root C s u : Code M Q (Records Q k s)) from
    this _
  induction s with
  | zero => intro u; trivial
  | succ s ih =>
    intro u
    apply uniformRandomness_row
    · intro label used t
      exact uniformRandomness_map _ (ih t) _
    · exact fun _ => True.intro

/-- The sampler has no zero-mass coin branches, so its zero excess-probability
bound strengthens to a bound on every actual compiled execution. -/
theorem factory_sampler_new_positive [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (b : Q → Bool) (cache : Q → Option Bool) (query : Fin (k + 1) → Q) (root : Fin (k + 1))
    (C s B W D : ℕ)
    (seed : ((factory cfg cache W D (program query root C s B cache)).compile m).Seed) :
    ((((factory cfg cache W D (program query root C s B cache)).compile m).tree seed).output b).value.state.newPositive ≤ s := by
  classical
  let p := factory cfg cache W D (program query root C s B cache)
  have hp : UniformRandomness p := uniformRandomness_resolve cfg _
    (uniformRandomness_cap _ (uniformRandomness_program query root C s B cache) W) _
  have hm := uniformRandomness_mass_pos m p hp seed
  have hz := factory_sampler_new_positive_zero cfg m b cache query root C s B W D
  rw [← Code.compile_expect] at hz
  change (p.compile m).law.expect
    (fun seed => threshold (s : ℝ) (((p.compile m).tree seed).output b).value.state.newPositive) = 0 at hz
  by_contra hn
  have ht : threshold (s : ℝ) (((p.compile m).tree seed).output b).value.state.newPositive = 1 := by
    have hr : (s : ℝ) < (((((p.compile m).tree seed).output b).value.state.newPositive) : ℝ) := by
      exact_mod_cast Nat.lt_of_not_ge hn
    simp only [threshold, hr, ite_true]
  have hterm :
      (p.compile m).law.mass seed *
        threshold (s : ℝ) (((p.compile m).tree seed).output b).value.state.newPositive ≤ 0 := by
    rw [← hz]
    apply Finset.single_le_sum _ (Finset.mem_univ seed)
    intro a _
    apply mul_nonneg ((p.compile m).law.nonneg a)
    unfold threshold
    split_ifs <;> norm_num
  rw [ht, mul_one] at hterm
  exact (not_lt_of_ge hterm) hm

theorem factory_sampler_resources [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (b : Q → Bool) (cache : Q → Option Bool) (query : Fin (k + 1) → Q) (root : Fin (k + 1))
    (C s B W D : ℕ)
    (seed : ((factory cfg cache W D (program query root C s B cache)).compile m).Seed) :
    let o := (((factory cfg cache W D (program query root C s B cache)).compile m).tree seed).output b
    o.metricQueries ≤ W + D ∧ o.work ≤ 32 * (W + D + 1) ∧
      o.retentionQueries = 0 ∧ o.value.state.newPositive ≤ s ∧ o.value.state.draws ≤ D := by
  have hr := factory_resources cfg m b cache W D (program query root C s B cache) seed
  have hp := factory_sampler_new_positive cfg m b cache query root C s B W D seed
  obtain ⟨d, _, hd⟩ := factory_draw_balance cfg m b cache W D
    (program query root C s B cache) seed
  exact ⟨hr.1, hr.2.1, hr.2.2, hp, by omega⟩

end Sampler

end SteinerUpperBound.Covers.OracleProgram
