module

public import SteinerLowerBound.MetricComparison.Hellinger

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Law

noncomputable def bernoulli (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : Law Bool where
  mass b := if b then p else 1 - p
  nonneg b := by cases b <;> simp [hp₀, hp₁]
  total := by simp [Fintype.sum_bool]

@[simp]
theorem bernoulli_mass_true (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (bernoulli p hp₀ hp₁).mass true = p := rfl

@[simp]
theorem bernoulli_mass_false (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (bernoulli p hp₀ hp₁).mass false = 1 - p := rfl

theorem prob_partition {Ω : Type*} [Fintype Ω] (μ : Law Ω) (E : Set Ω) (f : Ω → Bool) :
    μ.prob {w | w ∈ E ∧ f w = true} +
      μ.prob {w | w ∈ E ∧ f w = false} = μ.prob E := by
  classical
  simp only [prob, Set.mem_ofPred_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases ht : f w = true
  · by_cases hw : w ∈ E <;> simp [hw, ht]
  · have hf : f w = false := Bool.eq_false_iff.mpr ht
    by_cases hw : w ∈ E <;> simp [hw, ht, hf]

end Law

namespace MetricComparison

structure Memory (S H : Type*) where
  initial : H
  update : H → S → Bool → H
  Valid : H → Prop
  Fresh : H → S → Prop
  initial_valid : Valid initial
  update_valid : ∀ h u b, Valid h → Fresh h u → Valid (update h u b)

structure Observer {S H : Type*} (memory : Memory S H) (W : Type*) [Fintype W] where
  law : Law W
  accepts : H → W → Prop
  answer : W → H → S → Bool
  initial_accepts : ∀ w, accepts memory.initial w
  transition : ∀ h u b, memory.Valid h → memory.Fresh h u →
    ∀ w, accepts (memory.update h u b) w ↔ accepts h w ∧ answer w h u = b

namespace Observer

variable {S H W : Type*} [Fintype W] {memory : Memory S H}

noncomputable def evidence (model : Observer memory W) (h : H) : ℝ :=
  model.law.prob {w | model.accepts h w}

theorem evidence_nonneg (model : Observer memory W) (h : H) :
    0 ≤ model.evidence h := model.law.prob_nonneg _

@[simp]
theorem evidence_initial (model : Observer memory W) :
    model.evidence memory.initial = 1 := by
  have he : {w | model.accepts memory.initial w} = Set.univ := by
    ext w
    simp [model.initial_accepts]
  simp [evidence, he]

theorem evidence_update_add (model : Observer memory W) (h : H) (u : S)
    (hv : memory.Valid h) (hf : memory.Fresh h u) :
    model.evidence (memory.update h u true) +
      model.evidence (memory.update h u false) = model.evidence h := by
  have ht : {w | model.accepts (memory.update h u true) w} =
      {w | model.accepts h w ∧ model.answer w h u = true} := by
    ext w
    exact model.transition h u true hv hf w
  have hff : {w | model.accepts (memory.update h u false) w} =
      {w | model.accepts h w ∧ model.answer w h u = false} := by
    ext w
    exact model.transition h u false hv hf w
  simpa only [evidence, ht, hff, Set.mem_ofPred_eq] using
    model.law.prob_partition {w | model.accepts h w} (fun w => model.answer w h u)

theorem evidence_update_le (model : Observer memory W) (h : H) (u : S) (b : Bool)
    (hv : memory.Valid h) (hf : memory.Fresh h u) :
    model.evidence (memory.update h u b) ≤ model.evidence h := by
  have he := model.evidence_update_add h u hv hf
  cases b <;> linarith [model.evidence_nonneg (memory.update h u true),
    model.evidence_nonneg (memory.update h u false)]

noncomputable def positiveRate (model : Observer memory W) (h : H) (u : S) : ℝ :=
  if memory.Valid h ∧ memory.Fresh h u ∧ 0 < model.evidence h then
    model.evidence (memory.update h u true) / model.evidence h else 0

theorem positiveRate_nonneg (model : Observer memory W) (h : H) (u : S) :
    0 ≤ model.positiveRate h u := by
  unfold positiveRate
  split_ifs with hc
  · exact div_nonneg (model.evidence_nonneg _) hc.2.2.le
  · rfl

theorem positiveRate_le_one (model : Observer memory W) (h : H) (u : S) :
    model.positiveRate h u ≤ 1 := by
  unfold positiveRate
  split_ifs with hc
  · exact (div_le_one hc.2.2).mpr (model.evidence_update_le h u true hc.1 hc.2.1)
  · norm_num

noncomputable def kernel (model : Observer memory W) (h : H) (u : S) : Law Bool :=
  Law.bernoulli (model.positiveRate h u) (model.positiveRate_nonneg h u)
    (model.positiveRate_le_one h u)

theorem evidence_kernel (model : Observer memory W) (h : H) (u : S) (b : Bool)
    (hv : memory.Valid h) (hf : memory.Fresh h u) :
    model.evidence h * (model.kernel h u).mass b =
      model.evidence (memory.update h u b) := by
  have hsum := model.evidence_update_add h u hv hf
  by_cases hp : 0 < model.evidence h
  · cases b <;> simp only [kernel, Law.bernoulli_mass_false, Law.bernoulli_mass_true,
      positiveRate, hv, hf, hp, and_self, ↓reduceIte] <;> field_simp <;> nlinarith
  · have hz : model.evidence h = 0 :=
      le_antisymm (le_of_not_gt hp) (model.evidence_nonneg h)
    have ht : model.evidence (memory.update h u true) = 0 :=
      le_antisymm (by linarith [model.evidence_nonneg (memory.update h u false)])
        (model.evidence_nonneg _)
    have hff : model.evidence (memory.update h u false) = 0 := by linarith
    cases b <;> simp [hz, ht, hff]

end Observer

structure Control (C H : Type*) where
  history : C → H
  past : List Bool
  live : Bool

namespace Control

variable {C S H : Type*} {memory : Memory S H}

def initial (memory : Memory S H) : Control C H := ⟨fun _ => memory.initial, [], true⟩

def Valid (memory : Memory S H) (x : Control C H) : Prop :=
  ∀ c, memory.Valid (x.history c)

noncomputable def advance (memory : Memory S H) (schedule : Control C H → Option (C × S))
    (x : Control C H) (b : Bool) : Control C H :=
  ⟨match schedule x with
    | none => x.history
    | some (c, u) => Function.update x.history c (memory.update (x.history c) u b),
    x.past ++ [b],
    match schedule x with
    | none => x.live && !b
    | some _ => x.live⟩

def Nonrepeating (memory : Memory S H) (schedule : Control C H → Option (C × S)) : Prop :=
  ∀ x, x.Valid memory → ∀ c u, schedule x = some (c, u) → memory.Fresh (x.history c) u

theorem advance_valid (memory : Memory S H) (schedule : Control C H → Option (C × S))
    (hs : Nonrepeating memory schedule) (x : Control C H) (hx : x.Valid memory) (b : Bool) :
    (advance memory schedule x b).Valid memory := by
  classical
  intro c
  cases he : schedule x with
  | none => simpa only [advance, he] using hx c
  | some cu =>
    rcases cu with ⟨c', u⟩
    simp only [advance, he]
    by_cases hc : c = c'
    · subst c
      simp only [Function.update_self]
      exact memory.update_valid _ _ b (hx c') (hs x hx c' u he)
    · simpa only [Function.update_of_ne hc] using hx c

noncomputable def final (memory : Memory S H) (schedule : Control C H → Option (C × S)) :
    (n : ℕ) → Control C H → Answers n → Control C H
  | 0, x, _ => x
  | n + 1, x, a => final memory schedule n (advance memory schedule x a.1) a.2

end Control

namespace Observer

variable {C S H W : Type*} [Fintype C] [Fintype W] {memory : Memory S H}

noncomputable def globalEvidence (model : Observer memory W) (x : Control C H) : ℝ :=
  if x.live then ∏ c, model.evidence (x.history c) else 0

def globalAccepts (model : Observer memory W) (x : Control C H) (w : C → W) : Prop :=
  x.live = true ∧ ∀ c, model.accepts (x.history c) (w c)

noncomputable def globalKernel (model : Observer memory W)
    (schedule : Control C H → Option (C × S)) (x : Control C H) : Law Bool :=
  match schedule x with
  | none => Law.pure false
  | some (c, u) => model.kernel (x.history c) u

noncomputable def globalAnswer (model : Observer memory W)
    (schedule : Control C H → Option (C × S)) (w : C → W) (x : Control C H) : Bool :=
  match schedule x with
  | none => false
  | some (c, u) => model.answer (w c) (x.history c) u

noncomputable def run (model : Observer memory W)
    (schedule : Control C H → Option (C × S)) (w : C → W) :
    (n : ℕ) → Control C H → Answers n
  | 0, _ => ()
  | n + 1, x =>
    let b := model.globalAnswer schedule w x
    (b, model.run schedule w n (Control.advance memory schedule x b))

noncomputable def observationLaw (model : Observer memory W)
    (schedule : Control C H → Option (C × S)) (n : ℕ) : Law (Answers n) :=
  (Law.pi (fun _ : C => model.law)).map
    (fun w => model.run schedule w n (Control.initial memory))

theorem globalEvidence_eq_prob (model : Observer memory W) (x : Control C H) :
    model.globalEvidence x =
      (Law.pi (fun _ : C => model.law)).prob {w | model.globalAccepts x w} := by
  by_cases hx : x.live = true
  · simp only [globalEvidence, hx, ↓reduceIte, globalAccepts, true_and]
    exact (Law.prob_pi_all (fun _ : C => model.law)
      (fun c w => model.accepts (x.history c) w)).symm
  · have he : {w | model.globalAccepts x w} = ∅ := by
      ext w
      simp [globalAccepts, hx]
    simp [globalEvidence, hx, he]

theorem globalEvidence_kernel (model : Observer memory W)
    (schedule : Control C H → Option (C × S)) (hs : Control.Nonrepeating memory schedule)
    (x : Control C H) (hx : x.Valid memory) (b : Bool) :
    model.globalEvidence x * (model.globalKernel schedule x).mass b =
      model.globalEvidence (Control.advance memory schedule x b) := by
  classical
  cases he : schedule x with
  | none =>
      cases b <;> simp [globalEvidence, globalKernel, he, Control.advance, Law.pure]
  | some cu =>
      rcases cu with ⟨c, u⟩
      by_cases hl : x.live = true
      · simp only [globalEvidence, Control.advance, globalKernel, he, hl, ↓reduceIte]
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c)]
        have hprod :
            (∏ i ∈ Finset.univ.erase c, model.evidence
              (Function.update x.history c (memory.update (x.history c) u b) i)) =
              ∏ i ∈ Finset.univ.erase c, model.evidence (x.history i) := by
          apply Finset.prod_congr rfl
          intro i hi
          simp only [Function.update_of_ne (Finset.mem_erase.mp hi).1]
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c), hprod,
          Function.update_self, mul_assoc,
          model.evidence_kernel _ _ _ (hx c) (hs x hx c u he)]
      · simp [globalEvidence, Control.advance, he, hl]

theorem globalAccepts_advance (model : Observer memory W)
    (schedule : Control C H → Option (C × S)) (hs : Control.Nonrepeating memory schedule)
    (x : Control C H) (hx : x.Valid memory) (w : C → W) (b : Bool) :
    model.globalAccepts (Control.advance memory schedule x b) w ↔
      model.globalAccepts x w ∧ model.globalAnswer schedule w x = b := by
  classical
  cases he : schedule x with
  | none =>
      cases b <;> simp [globalAccepts, Control.advance, he, globalAnswer]
  | some cu =>
      rcases cu with ⟨c, u⟩
      simp only [globalAccepts, Control.advance, globalAnswer, he]
      constructor
      · rintro ⟨hl, ha⟩
        have hc := ha c
        rw [Function.update_self] at hc
        obtain ⟨hc, hb⟩ := (model.transition _ _ _ (hx c) (hs x hx c u he) _).mp hc
        refine ⟨⟨hl, ?_⟩, hb⟩
        intro i
        by_cases hi : i = c
        · simpa only [hi] using hc
        · simpa only [Function.update_of_ne hi] using ha i
      · rintro ⟨⟨hl, ha⟩, hb⟩
        refine ⟨hl, ?_⟩
        intro i
        by_cases hi : i = c
        · subst i
          rw [Function.update_self]
          exact (model.transition _ _ _ (hx c) (hs x hx c u he) _).mpr ⟨ha c, hb⟩
        · simpa only [Function.update_of_ne hi] using ha i

theorem accepts_final_iff (model : Observer memory W)
    (schedule : Control C H → Option (C × S)) (hs : Control.Nonrepeating memory schedule)
    (n : ℕ) (x : Control C H) (hx : x.Valid memory) (w : C → W) (a : Answers n) :
    model.globalAccepts (Control.final memory schedule n x a) w ↔
      model.globalAccepts x w ∧ model.run schedule w n x = a := by
  induction n generalizing x with
  | zero =>
      change model.globalAccepts x w ↔ model.globalAccepts x w ∧ (() : Answers 0) = a
      exact (and_iff_left (Subsingleton.elim _ _)).symm
  | succ n ih =>
      rcases a with ⟨b, a⟩
      change model.globalAccepts
        (Control.final memory schedule n (Control.advance memory schedule x b) a) w ↔ _
      rw [ih _ (Control.advance_valid memory schedule hs x hx b),
        model.globalAccepts_advance schedule hs x hx w b]
      simp only [run, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨ha, hb⟩, hr⟩
        exact ⟨ha, hb, by simpa only [hb] using hr⟩
      · rintro ⟨ha, hb, hr⟩
        exact ⟨⟨ha, hb⟩, by simpa only [hb] using hr⟩

theorem evidence_final (model : Observer memory W)
    (schedule : Control C H → Option (C × S)) (hs : Control.Nonrepeating memory schedule)
    (n : ℕ) (x : Control C H) (hx : x.Valid memory) (a : Answers n) :
    model.globalEvidence (Control.final memory schedule n x a) =
      model.globalEvidence x *
        (sequential (model.globalKernel schedule) (Control.advance memory schedule) n x).mass a := by
  classical
  induction n generalizing x with
  | zero =>
      have ha : a = (() : Answers 0) := Subsingleton.elim _ _
      subst a
      simp [Control.final, sequential, Law.pure]
  | succ n ih =>
      rcases a with ⟨b, a⟩
      change model.globalEvidence
        (Control.final memory schedule n (Control.advance memory schedule x b) a) = _
      rw [ih _ (Control.advance_valid memory schedule hs x hx b),
        ← model.globalEvidence_kernel schedule hs x hx b]
      simp only [sequential, Law.step]
      ring

theorem observationLaw_eq_sequential (model : Observer memory W)
    (schedule : Control C H → Option (C × S)) (hs : Control.Nonrepeating memory schedule)
    (n : ℕ) :
    model.observationLaw schedule n =
      sequential (model.globalKernel schedule) (Control.advance memory schedule)
        n (Control.initial memory) := by
  classical
  have hi : (Control.initial memory : Control C H).Valid memory := fun _ => memory.initial_valid
  have hia (w : C → W) : model.globalAccepts (Control.initial memory) w :=
    ⟨rfl, fun c => model.initial_accepts (w c)⟩
  have hei : model.globalEvidence (Control.initial memory : Control C H) = 1 := by
    simp [globalEvidence, Control.initial]
  have hm (a : Answers n) :
      (model.observationLaw schedule n).mass a =
        (sequential (model.globalKernel schedule) (Control.advance memory schedule)
          n (Control.initial memory)).mass a := by
    change (∑ w, if model.run schedule w n (Control.initial memory) = a then
      (Law.pi (fun _ : C => model.law)).mass w else 0) = _
    have he : {w | model.run schedule w n (Control.initial memory) = a} =
        {w | model.globalAccepts (Control.final memory schedule n (Control.initial memory) a) w} := by
      ext w
      simp only [Set.mem_ofPred_eq]
      rw [model.accepts_final_iff schedule hs n _ hi w a]
      simp only [Set.mem_ofPred_eq, hia w, true_and]
    change (Law.pi (fun _ : C => model.law)).prob
      {w | model.run schedule w n (Control.initial memory) = a} = _
    rw [he, ← model.globalEvidence_eq_prob, model.evidence_final schedule hs n _ hi a, hei,
      one_mul]
  cases h₁ : model.observationLaw schedule n with
  | mk mass nonneg total =>
    cases h₂ : sequential (model.globalKernel schedule) (Control.advance memory schedule)
        n (Control.initial memory) with
    | mk mass' nonneg' total' =>
      have he : mass = mass' := funext (fun a => by simpa only [h₁, h₂] using hm a)
      cases he
      rfl

end Observer

end MetricComparison

end SteinerLowerBound
