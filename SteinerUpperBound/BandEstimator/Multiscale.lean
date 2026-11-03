module

public import SteinerUpperBound.BandEstimator.Stage

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.BandEstimator

open SteinerLowerBound QueryProgram MSTApproximation Covers.OracleProgram
open scoped Classical BigOperators

variable {Q : Type*} {n k : ℕ}

noncomputable def loss (b : Q → Bool) (g : Grid) (key : Index g → Fin n → Q)
    (terminals : List (Fin n)) (d : Data) (i : Index g) : ℝ :=
  9 * accuracy d * g.scale i.val * (retained b g key terminals i).card

def GoodRounds (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (key : Index g → Fin n → Q) (terminals : List (Fin n)) (d : Data)
    (indices : List (Index g)) (initial : ℝ) (r : Option ℝ × Cache Q) : Prop :=
  Cache.Correct b r.2 ∧ ∃ t, r.1 = some t ∧ initial ≤ t ∧
    t ≤ initial + (indices.map (target I b g key terminals d)).sum ∧
    initial + (indices.map (target I b g key terminals d)).sum - t ≤
      (indices.map (loss b g key terminals d)).sum

theorem valueProbability_mono {M R : Type*} (m : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (P T : R → Prop) (h : ∀ r, P r → T r) :
    Code.valueProbability m b p P ≤ Code.valueProbability m b p T := by
  unfold Code.valueProbability
  apply Code.evaluate_mono
  intro o
  by_cases hp : P o.value
  · simp [hp, h o.value hp]
  · by_cases ht : T o.value <;> simp [hp, ht]

theorem valueProbability_tick {M R : Type*} (m : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (P : R → Prop) (j : ℕ) :
    Code.valueProbability m b (.tick j p) P = Code.valueProbability m b p P := rfl

private theorem goodRounds_cons (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (key : Index g → Fin n → Q) (terminals : List (Fin n)) (d : Data)
    (i : Index g) (l : List (Index g)) (initial z : ℝ)
    (hz₀ : 0 ≤ z) (hz₁ : z ≤ target I b g key terminals d i)
    (hzloss : target I b g key terminals d i - z ≤ loss b g key terminals d i)
    (r : Option ℝ × Cache Q) (hr : GoodRounds I b g key terminals d l (initial + z) r) :
    GoodRounds I b g key terminals d (i :: l) initial r := by
  obtain ⟨hc, t, hv, h₀, h₁, hl⟩ := hr
  refine ⟨hc, t, hv, by linarith, ?_, ?_⟩ <;>
    simp only [List.map_cons, List.sum_cons] <;> linarith

theorem rounds_success_public (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (henum : FiniteMST.labels label = terminals.toFinset)
    (hb : ∀ i, (Covers.Rejection.retained (fun u => b (key i (label u)))).Nonempty)
    (indices : List (Index g)) (initial : ℝ) (c : Cache Q) (hc : Cache.Correct b c) :
    1 - 3 * EstimatorParameters.beta n * indices.length ≤
      Code.valueProbability I.weight b
        (rounds g label key root terminals (publicData n (k + 1)) indices (some initial) c)
        (GoodRounds I b g key terminals (publicData n (k + 1)) indices initial) := by
  let d := publicData n (k + 1)
  let β := EstimatorParameters.beta n
  have hβ : 0 ≤ β := (EstimatorParameters.beta_bounds n).1.le
  induction indices generalizing initial c with
  | nil =>
    simp [rounds, Code.valueProbability, Code.evaluate, Outcome.add, Outcome.pure, GoodRounds, hc]
  | cons i l ih =>
    let next : (Option ℝ × Cache Q) → Code (Sym2 (Fin n)) Q (Option ℝ × Cache Q) :=
      fun r => .tick 3 (rounds g label key root terminals d l (add (some initial) r.1) r.2)
    have hn (r : Option ℝ × Cache Q) (hr : GoodStage I b g key terminals d i r) :
        1 - 3 * β * l.length ≤ Code.valueProbability I.weight b (next r)
          (GoodRounds I b g key terminals d (i :: l) initial) := by
      obtain ⟨hcache, z, hv, hz₀, hz₁, hzloss⟩ := hr
      have ht := ih (initial + z) r.2 hcache
      have hm := valueProbability_mono I.weight b
        (rounds g label key root terminals d l (some (initial + z)) r.2)
        (GoodRounds I b g key terminals d l (initial + z))
        (GoodRounds I b g key terminals d (i :: l) initial)
        (goodRounds_cons I b g key terminals d i l initial z hz₀ hz₁ hzloss)
      have hu : 1 - 3 * EstimatorParameters.beta n * l.length ≤
          Code.valueProbability I.weight b
            (rounds g label key root terminals d l (some (initial + z)) r.2)
            (GoodRounds I b g key terminals d (i :: l) initial) := by
        linarith [ht, hm]
      have he : add (some initial) r.1 = some (initial + z) := by
        simp only [add, hv, Option.bind_some, Option.map_some]
      change 1 - 3 * β * l.length ≤ Code.valueProbability I.weight b
        (.tick 3 (rounds g label key root terminals d l (add (some initial) r.1) r.2)) _
      rw [he, valueProbability_tick]
      exact hu
    have hh := Code.bind_success I.weight b (stage g label key root terminals d i c) next
      (GoodStage I b g key terminals d i)
      (GoodRounds I b g key terminals d (i :: l) initial)
      (3 * β) (3 * β * l.length) (by positivity) (by positivity)
      (stage_success_public I b g label hlabel key root terminals henum i c hc (hb i)) hn
    change 1 - 3 * β * ((i :: l).length : ℝ) ≤ _
    have he : 1 - 3 * β * ((i :: l).length : ℝ) = 1 - 3 * β - 3 * β * l.length := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
    rw [he]
    exact hh

theorem all_targets (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (key : Index g → Fin n → Q) (terminals : List (Fin n)) (d : Data) :
    ((List.finRange (g.intervals + 1)).map (target I b g key terminals d)).sum =
      totalSmallScore I b g key terminals d := by
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  rfl

theorem all_losses (b : Q → Bool) (g : Grid) (key : Index g → Fin n → Q)
    (terminals : List (Fin n)) (d : Data) :
    ((List.finRange (g.intervals + 1)).map (loss b g key terminals d)).sum =
      9 * accuracy d * mass b g key terminals := by
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  unfold mass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold loss
  ring

theorem mass_loss (b : Q → Bool) (g : Grid) (key : Index g → Fin n → Q)
    (terminals : List (Fin n)) (L : ℝ) (hL : 0 ≤ L)
    (hmass : mass b g key terminals ≤ (EstimatorParameters.A n : ℝ) * L) :
    9 * accuracy (publicData n (k + 1)) * mass b g key terminals ≤ Structural.sigma0 * L / 1000 := by
  have hξ := (accuracy_bounds n (k + 1)).1
  have hA : (0 : ℝ) < EstimatorParameters.A n := by exact_mod_cast EstimatorParameters.A_pos n
  have hσ : 0 ≤ Structural.sigma0 * L := mul_nonneg (by norm_num [Structural.sigma0]) hL
  calc
    _ ≤ 9 * accuracy (publicData n (k + 1)) * ((EstimatorParameters.A n : ℝ) * L) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (9 / 100000 : ℝ) * (Structural.sigma0 * L) := by
      rw [accuracy_mass_budget]
      field_simp
    _ ≤ (1 / 1000 : ℝ) * (Structural.sigma0 * L) :=
      mul_le_mul_of_nonneg_right (by norm_num) hσ
    _ = _ := by ring

def GoodOutput (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (key : Index g → Fin n → Q) (terminals : List (Fin n)) (d : Data) (L : ℝ)
    (r : Option ℝ × Cache Q) : Prop :=
  Cache.Correct b r.2 ∧ ∃ t, r.1 = some t ∧ 0 ≤ t ∧
    t ≤ totalSmallScore I b g key terminals d ∧
    totalSmallScore I b g key terminals d - t ≤ Structural.sigma0 * L / 1000

theorem program_success (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (henum : FiniteMST.labels label = terminals.toFinset)
    (hb : ∀ i, (Covers.Rejection.retained (fun u => b (key i (label u)))).Nonempty)
    (L : ℝ) (hL : 0 ≤ L) (hmass : mass b g key terminals ≤ (EstimatorParameters.A n : ℝ) * L)
    (c : Cache Q) (hc : Cache.Correct b c) :
    1 - 3 * EstimatorParameters.beta n * (g.intervals + 1) ≤
      Code.valueProbability I.weight b
        (program g label key root terminals (publicData n (k + 1)) c)
        (GoodOutput I b g key terminals (publicData n (k + 1)) L) := by
  let d := publicData n (k + 1)
  let indices := List.finRange (g.intervals + 1)
  have hs := rounds_success_public I b g label hlabel key root terminals henum hb indices 0 c hc
  have hm := valueProbability_mono I.weight b
    (rounds g label key root terminals d indices (some 0) c)
    (GoodRounds I b g key terminals d indices 0)
    (GoodOutput I b g key terminals d L) (by
      intro r hr
      obtain ⟨hc', t, hv, ht₀, ht₁, hloss⟩ := hr
      rw [all_targets] at ht₁ hloss
      rw [all_losses] at hloss
      refine ⟨hc', t, hv, ht₀, ?_, ?_⟩
      · simpa only [zero_add] using ht₁
      · have ht : totalSmallScore I b g key terminals d - t ≤
            9 * accuracy d * mass b g key terminals := by
          simpa only [zero_add] using hloss
        exact ht.trans (mass_loss (k := k) b g key terminals L hL hmass))
  have ht : 1 - 3 * EstimatorParameters.beta n * indices.length ≤
      Code.valueProbability I.weight b
        (rounds g label key root terminals d indices (some 0) c)
        (GoodOutput I b g key terminals d L) := by
    linarith [hs, hm]
  have hcount : (indices.length : ℝ) = (g.intervals : ℝ) + 1 := by
    simp only [indices, List.length_finRange, Nat.cast_add, Nat.cast_one]
  rw [hcount] at ht
  rw [program, valueProbability_tick]
  exact ht

end SteinerUpperBound.BandEstimator
