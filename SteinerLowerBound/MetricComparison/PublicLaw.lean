module

public import SteinerLowerBound.MetricComparison.PublicOptimum
public import SteinerLowerBound.HardFamily

@[expose] public section

/-!
# The static hard law on actual shuffled public metrics

An input is a static center-neighbor assignment together with an independent
uniform permutation of the public terminal labels. This is the metric law,
not the auxiliary gated law. Its output law is exactly the static side of
`Public.public_outputs_close`. Its actual public-optimum events have exactly
the canonical `Setup.law` probabilities.
-/

namespace SteinerLowerBound.MetricComparison.PublicLaw

open scoped BigOperators Classical
open HardDistribution
open Screening (Terminal Reply)

abbrev Input (S G I C : Type*) (d : ℕ) :=
  (C → State S d) × Equiv.Perm (Terminal S G I)

variable {S G I C Ω Z : Type*}
variable [Fintype S] [Fintype G] [Fintype I] [Fintype C] [Fintype Ω]

noncomputable def law (k : Setup S Ω) (μ : Law Ω) : Law (Input S G I C k.d) :=
  Law.step (k.law (C := C) μ) (fun _ => Law.uniform (Equiv.Perm (Terminal S G I)))

theorem law_mass (k : Setup S Ω) (μ : Law Ω) (input : Input S G I C k.d) :
    (law k μ).mass input =
      (k.law μ).mass input.1 * (Law.uniform (Equiv.Perm (Terminal S G I))).mass input.2 := rfl

noncomputable def neighbors (k : Setup S Ω) (input : Input S G I C k.d) : C → Finset S :=
  fun c => HardDistribution.neighbors k.d (input.1 c)

noncomputable def oracle (k : Setup S Ω) (input : Input S G I C k.d) :
    Public.Queries S G I C → Reply :=
  Public.staticAnswer input.2 (neighbors k input)

noncomputable def realOracle (k : Setup S Ω) (ell : ℝ) (input : Input S G I C k.d) :
    Public.Queries S G I C → ℝ :=
  fun q => Public.replyValue ell (oracle k input q)

@[instance_reducible] noncomputable def metricSpace (k : Setup S Ω) {ell : ℝ}
    (hEll₀ : 0 < ell) (hEll₂ : ell ≤ 2) (input : Input S G I C k.d) :
    MetricSpace (Public.Points S G I C) :=
  Public.metricSpace input.2 hEll₀ hEll₂ (neighbors k input)

theorem oracle_distance (k : Setup S Ω) {ell : ℝ}
    (hEll₀ : 0 < ell) (hEll₂ : ell ≤ 2) (input : Input S G I C k.d)
    (x y : Public.Points S G I C) :
    realOracle k ell input (Sym2.mk x y) =
      @dist _ (metricSpace k hEll₀ hEll₂ input).toDist x y := by
  exact Public.staticAnswer_metric input.2 (neighbors k input) ell x y

theorem law_expect (k : Setup S Ω) (μ : Law Ω) (f : Input S G I C k.d → ℝ) :
    (law k μ).expect f =
      (k.law μ).expect (fun σ =>
        (Law.uniform (Equiv.Perm (Terminal S G I))).expect (fun π => f (σ, π))) :=
  by
    simp only [law, Law.step, Law.expect, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem law_probability (k : Setup S Ω) (μ : Law Ω) (E : Set (Input S G I C k.d)) :
    (law k μ).prob E =
      (k.law μ).expect (fun σ =>
        (Law.uniform (Equiv.Perm (Terminal S G I))).prob {π | (σ, π) ∈ E}) :=
  Law.prob_step (k.law μ) (fun _ => Law.uniform (Equiv.Perm (Terminal S G I))) E

theorem law_disintegrate (k : Setup S Ω) (μ : Law Ω) :
    law (G := G) (I := I) (C := C) k μ =
      (μ.iid S).bind (fun w => Law.step (k.centersLaw (C := C) w)
        (fun _ => Law.uniform (Equiv.Perm (Terminal S G I)))) := by
  apply Compiler.law_ext
  intro input
  simp only [law, Law.step, Setup.law, Law.bind, Law.expect_mul_const]

theorem prob_neighbors (k : Setup S Ω) (μ : Law Ω) (E : Set (C → State S k.d)) :
    (law (G := G) (I := I) k μ).prob {input | input.1 ∈ E} = (k.law μ).prob E := by
  classical
  rw [law_probability]
  simp only [Set.mem_ofPred_eq]
  have he (σ : C → State S k.d) :
      (Law.uniform (Equiv.Perm (Terminal S G I))).prob {π | (σ, π).1 ∈ E} =
        if σ ∈ E then 1 else 0 := by
    by_cases h : σ ∈ E <;> simp [h]
  simp_rw [he]
  exact (Law.prob_eq_expect _ _).symm

theorem permutation_independent (k : Setup S Ω) (μ : Law Ω)
    (E : Set (C → State S k.d)) (F : Set (Equiv.Perm (Terminal S G I))) :
    (law k μ).prob {input | input.1 ∈ E ∧ input.2 ∈ F} =
      (k.law μ).prob E * (Law.uniform (Equiv.Perm (Terminal S G I))).prob F := by
  classical
  rw [law_probability]
  simp only [Set.mem_ofPred_eq]
  have he (σ : C → State S k.d) :
      (Law.uniform (Equiv.Perm (Terminal S G I))).prob
          {π | (σ, π).1 ∈ E ∧ (σ, π).2 ∈ F} =
        (if σ ∈ E then 1 else 0) *
          (Law.uniform (Equiv.Perm (Terminal S G I))).prob F := by
    by_cases h : σ ∈ E <;> simp [h]
  simp_rw [he]
  rw [Law.expect_mul_const, ← Law.prob_eq_expect]

theorem expect_comm {A B : Type*} [Fintype A] [Fintype B]
    (μ : Law A) (ν : Law B) (f : A → B → ℝ) :
    μ.expect (fun a => ν.expect (f a)) = ν.expect (fun b => μ.expect (fun a => f a b)) := by
  simp only [Law.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem expect_step {A B : Type*} [Fintype A] [Fintype B]
    (μ : Law A) (k : A → Law B) (f : A × B → ℝ) :
    (Law.step μ k).expect f = μ.expect (fun a => (k a).expect (fun b => f (a, b))) := by
  simp only [Law.step, Law.expect, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem law_publicData (k : Setup S Ω) (μ : Law Ω) :
    law (G := G) (I := I) (C := C) k μ =
      (Public.publicDataLaw (G := G) (I := I) μ).bind (fun data =>
        (k.centersLaw (C := C) data.1).map (fun σ => (σ, data.2))) := by
  classical
  apply Compiler.law_ext_prob
  intro E
  rw [Law.prob_eq_expect, Law.prob_eq_expect]
  simp only [law_expect, Setup.law, Law.expect_bind, Public.publicDataLaw, expect_step,
    Law.expect_map]
  apply congrArg (Law.expect (μ.iid S))
  funext w
  exact expect_comm (k.centersLaw (C := C) w)
    (Law.uniform (Equiv.Perm (Terminal S G I))) (fun σ π => if (σ, π) ∈ E then 1 else 0)

theorem prob_publicData (k : Setup S Ω) (μ : Law Ω) (E : Set (Input S G I C k.d)) :
    (law k μ).prob E =
      (Public.publicDataLaw (G := G) (I := I) μ).expect (fun data =>
        (k.centersLaw (C := C) data.1).prob {σ | (σ, data.2) ∈ E}) := by
  rw [law_publicData, Law.prob_bind]
  apply congrArg (Law.expect (Public.publicDataLaw (G := G) (I := I) μ))
  funext data
  rw [Law.prob_map]
  rfl

noncomputable def outputLaw [Fintype Z] (k : Setup S Ω) (μ : Law Ω)
    (t : DecisionTree (Public.Queries S G I C) Reply Z) : Law Z :=
  (law k μ).map (fun input => t.output (oracle k input))

theorem outputLaw_eq_comparison [Fintype Z] (k : Setup S Ω) (μ : Law Ω)
    (t : DecisionTree (Public.Queries S G I C) Reply Z) :
    outputLaw k μ t = Public.metricOutputLaw k μ t := by
  classical
  apply Compiler.law_ext_prob
  intro E
  rw [Law.prob_eq_expect, Law.prob_eq_expect]
  simp only [outputLaw, Law.expect_map, law_expect, Setup.law, Law.expect_bind,
    Public.metricOutputLaw, Public.publicDataLaw, expect_step, oracle, neighbors]
  apply congrArg (Law.expect (μ.iid S))
  funext w
  exact expect_comm (k.centersLaw (C := C) w)
    (Law.uniform (Equiv.Perm (Terminal S G I)))
    (fun σ π => if t.output (Public.staticAnswer π (fun c =>
      HardDistribution.neighbors k.d (σ c))) ∈ E then 1 else 0)

variable [Nonempty G] [Nonempty I]

noncomputable def optimum (k : Setup S Ω) (ell : ℝ) (input : Input S G I C k.d) : ℝ :=
  Public.optimum input.2 ell (neighbors k input)

theorem optimum_eq_canonical (k : Setup S Ω) (ell : ℝ) (input : Input S G I C k.d) :
    optimum k ell input = k.instanceOpt (G := G) (I := I) ell input.1 :=
  Public.public_optimum_eq input.2 ell (neighbors k input)

theorem prob_optimum (k : Setup S Ω) (μ : Law Ω) (ell : ℝ) (P : ℝ → Prop) :
    (law (G := G) (I := I) (C := C) k μ).prob {input | P (optimum k ell input)} =
      (k.law (C := C) μ).prob {σ | P (k.instanceOpt (G := G) (I := I) ell σ)} := by
  have he : {input : Input S G I C k.d | P (optimum k ell input)} =
      {input | input.1 ∈ {σ | P (k.instanceOpt (G := G) (I := I) ell σ)}} := by
    ext input
    simp only [Set.mem_ofPred_eq, optimum_eq_canonical]
  rw [he, prob_neighbors]

theorem cost_separation {η : ℝ} {s : ℕ} (f : HardFamily.Family η s) (hη : 0 < η)
    (hm : f.d ≤ Fintype.card S)
    (hRmass : 2 * f.H0 * f.weights.bound ^ f.d ≤ (f.d : ℝ) * Fintype.card I)
    (hS : (Fintype.card S : ℝ) = (f.d : ℝ) * Fintype.card G)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * Fintype.card I)
    {ell : ℝ} (hEll₀ : 0 ≤ ell) (hEll₂ : ell ≤ 2) :
    let k := f.setup (S := S) (I := I) hm hRmass
    let offset := ell * Fintype.card G * ((Fintype.card I : ℝ) - 1)
    (law (G := G) (I := I) (C := C) k f.weights.yes).prob
        {input | Testing.yesCost η (Fintype.card S) offset < optimum k ell input} ≤ 1 / 100 ∧
      (law (G := G) (I := I) (C := C) k f.weights.no).prob
        {input | optimum k ell input < Testing.noCost η (Fintype.card S) offset} ≤ 1 / 100 := by
  dsimp only
  rw [prob_optimum _ _ ell (fun v =>
      Testing.yesCost η (Fintype.card S)
        (ell * Fintype.card G * ((Fintype.card I : ℝ) - 1)) < v),
    prob_optimum _ _ ell (fun v => v < Testing.noCost η (Fintype.card S)
      (ell * Fintype.card G * ((Fintype.card I : ℝ) - 1)))]
  exact f.cost_separation hη hm hRmass hS hC hEll₀ hEll₂

end SteinerLowerBound.MetricComparison.PublicLaw

namespace SteinerLowerBound.MetricComparison.PublicLaw

open Screening (Reply)

namespace RealAnswers

variable {Q A R R' : Type*}

def compile (ell : ℝ) : DecisionTree Q ℝ R → DecisionTree Q Reply R
  | .leaf r => .leaf r
  | .query q next => .query q (fun a => compile ell (next (Public.replyValue ell a)))

theorem output (ell : ℝ) (t : DecisionTree Q ℝ R) (o : Q → Reply) :
    (compile ell t).output o = t.output (fun q => Public.replyValue ell (o q)) := by
  induction t with
  | leaf => rfl
  | query q next ih => exact ih (Public.replyValue ell (o q))

theorem transcript (ell : ℝ) (t : DecisionTree Q ℝ R) (o : Q → Reply) :
    ((compile ell t).transcript o).map (fun qa => (qa.1, Public.replyValue ell qa.2)) =
      t.transcript (fun q => Public.replyValue ell (o q)) := by
  induction t with
  | leaf => rfl
  | query q next ih =>
    simp only [compile, DecisionTree.transcript, List.map_cons]
    rw [ih]

theorem queries (ell : ℝ) (t : DecisionTree Q ℝ R) (o : Q → Reply) :
    (compile ell t).queries o = t.queries (fun q => Public.replyValue ell (o q)) := by
  have hh := congrArg List.length (transcript ell t o)
  simpa only [List.length_map, DecisionTree.queries] using hh

theorem bounded (ell : ℝ) (t : DecisionTree Q ℝ R) (q : ℕ)
    (hq : Screening.DecisionTree.Bounded t q) :
    Screening.DecisionTree.Bounded (compile ell t) q := by
  induction t generalizing q with
  | leaf => trivial
  | query x next ih =>
    cases q with
    | zero => contradiction
    | succ q => exact fun a => ih (Public.replyValue ell a) q (hq _)

theorem map (ell : ℝ) (f : R → R') (t : DecisionTree Q ℝ R) :
    compile ell (t.map f) = (compile ell t).map f := by
  induction t with
  | leaf => rfl
  | query q next ih =>
    simp only [compile, DecisionTree.map]
    congr 1
    funext a
    exact ih (Public.replyValue ell a)

theorem truncate (ell : ℝ) (t : DecisionTree Q ℝ R) (q : ℕ) :
    compile ell (t.truncate q) = (compile ell t).truncate q := by
  induction q generalizing t with
  | zero => cases t <;> rfl
  | succ q ih =>
    cases t with
    | leaf => rfl
    | query x next =>
      simp only [compile, DecisionTree.truncate]
      congr 1
      funext a
      exact ih (next (Public.replyValue ell a))

theorem truncateWith (ell : ℝ) (t : DecisionTree Q ℝ R) (fallback : R) (q : ℕ) :
    compile ell (t.truncateWith fallback q) = (compile ell t).truncateWith fallback q := by
  rw [DecisionTree.truncateWith, map, truncate]
  rfl

theorem truncate_bounded (t : DecisionTree Q A R) (q : ℕ) :
    Screening.DecisionTree.Bounded (t.truncate q) q := by
  induction q generalizing t with
  | zero => cases t <;> trivial
  | succ q ih =>
    cases t with
    | leaf => trivial
    | query x next => exact fun a => ih (next a)

theorem compile_truncateWith_bounded (ell : ℝ) (t : DecisionTree Q ℝ R)
    (fallback : R) (q : ℕ) :
    Screening.DecisionTree.Bounded (compile ell (t.truncateWith fallback q)) q := by
  rw [truncateWith, DecisionTree.truncateWith]
  exact Padding.Reduction.bounded_map _ _ q (truncate_bounded _ q)

end RealAnswers

variable {S G I C Ω Z : Type*}
variable [Fintype S] [Fintype G] [Fintype I] [Fintype C] [Fintype Ω]

theorem real_output (k : HardDistribution.Setup S Ω) (ell : ℝ)
    (t : DecisionTree (Public.Queries S G I C) ℝ Z) (input : Input S G I C k.d) :
    (RealAnswers.compile ell t).output (oracle k input) = t.output (realOracle k ell input) :=
  RealAnswers.output ell t (oracle k input)

theorem real_queries (k : HardDistribution.Setup S Ω) (ell : ℝ)
    (t : DecisionTree (Public.Queries S G I C) ℝ Z) (input : Input S G I C k.d) :
    (RealAnswers.compile ell t).queries (oracle k input) = t.queries (realOracle k ell input) :=
  RealAnswers.queries ell t (oracle k input)

end SteinerLowerBound.MetricComparison.PublicLaw
