module

public import SteinerUpperBound.LabelledFactory

@[expose] public section

namespace SteinerUpperBound.FactoryEquivariance

open SteinerLowerBound
open scoped Classical BigOperators

variable {U W : Type*} [Fintype U] [Fintype W] [Nonempty U] [Nonempty W]

theorem uniform_equiv (e : U ≃ W) : (Law.uniform U).map e = Law.uniform W := by
  apply LawOperations.ext_mass
  intro w
  rw [LawOperations.map_equiv_mass]
  simp only [Law.uniform, Fintype.card_congr e]

theorem map_bind {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (mu : Law A) (f : A → B) (k : B → Law C) :
    (mu.map f).bind k = mu.bind (fun a => k (f a)) := by
  apply LawOperations.ext_prob
  intro E
  simp only [Law.prob_bind, Law.expect_map]

theorem factory_law (e : U ≃ W) (R : U → U → Prop) (S : W → W → Prop)
    (hR : ∀ x y, S (e x) (e y) ↔ R x y) (x : U) (B psi : ℕ) :
    Covers.Factory.law S (e x) B psi = Covers.Factory.law R x B psi := by
  induction B generalizing psi with
  | zero => cases psi <;> rfl
  | succ B ih =>
      cases psi with
      | zero => rfl
      | succ psi =>
          rw [Covers.Factory.law, Covers.Factory.law, ← uniform_equiv e, map_bind]
          apply congrArg (Law.uniform U).bind
          funext y
          by_cases h : y = x
          · have he := congrArg e h
            simp only [h, he, ite_true]
          · have he : e y ≠ e x := fun h' => h (e.injective h')
            by_cases hr : R x y
            · have hs := (hR x y).mpr hr
              simpa only [he, h, hr, hs, ite_true, ite_false] using ih psi
            · have hs : ¬ S (e x) (e y) := fun hs => hr ((hR x y).mp hs)
              simpa only [he, h, hr, hs, ite_true, ite_false] using ih (psi + 1)

theorem bitLaw (e : U ≃ W) (R : U → U → Prop) (S : W → W → Prop)
    (hR : ∀ x y, S (e x) (e y) ↔ R x y) (x : U) (B psi : ℕ) :
    Covers.Factory.bitLaw S (e x) B psi = Covers.Factory.bitLaw R x B psi := by
  unfold Covers.Factory.bitLaw
  rw [factory_law e R S hR x B psi]

theorem forcedBitLaw (e : U ≃ W) (R : U → U → Prop) (S : W → W → Prop)
    (hR : ∀ x y, S (e x) (e y) ↔ R x y) (root x : U) (B psi : ℕ) :
    Covers.Factory.forcedBitLaw S (e root) B psi (e x) =
      Covers.Factory.forcedBitLaw R root B psi x := by
  by_cases hx : x = root
  · simp only [Covers.Factory.forcedBitLaw, hx, ite_true]
  · have he : e x ≠ e root := fun h => hx (e.injective h)
    simp only [Covers.Factory.forcedBitLaw, he, hx, ite_false, bitLaw e R S hR x B psi]

def masks (e : U ≃ W) : (W → Bool) ≃ (U → Bool) where
  toFun b x := b (e x)
  invFun b y := b (e.symm y)
  left_inv b := by funext y; simp
  right_inv b := by funext x; simp

theorem selected_masks (e : U ≃ W) (b : W → Bool) :
    (CategoricalCoupling.selected (masks e b)).image e = CategoricalCoupling.selected b := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  · intro hy
    refine Finset.mem_image.mpr ⟨e.symm y, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simpa only [masks, Equiv.coe_fn_mk, Equiv.apply_symm_apply] using
      (Finset.mem_filter.mp hy).2⟩

theorem selected_masks_card (e : U ≃ W) (b : W → Bool) :
    (CategoricalCoupling.selected (masks e b)).card = (CategoricalCoupling.selected b).card := by
  rw [← selected_masks e b]
  exact (Finset.card_image_iff.mpr (fun _ _ _ _ h => e.injective h)).symm

theorem pi_pullback (e : U ≃ W) (mu : W → Law Bool) :
    (Law.pi mu).map (masks e) = Law.pi (fun x => mu (e x)) := by
  apply LawOperations.ext_mass
  intro b
  rw [LawOperations.map_equiv_mass]
  change (∏ y : W, (mu y).mass (b (e.symm y))) = ∏ x : U, (mu (e x)).mass (b x)
  exact Fintype.prod_equiv e.symm _ _ (fun y => by simp)

theorem privateBits (e : U ≃ W) (R : U → U → Prop) (S : W → W → Prop)
    (hR : ∀ x y, S (e x) (e y) ↔ R x y) (root : U) (B psi : ℕ) :
    (Covers.Factory.privateBits S (e root) B psi).map (masks e) =
      Covers.Factory.privateBits R root B psi := by
  unfold Covers.Factory.privateBits
  rw [pi_pullback]
  congr 1
  funext x
  exact forcedBitLaw e R S hR root x B psi

end SteinerUpperBound.FactoryEquivariance
