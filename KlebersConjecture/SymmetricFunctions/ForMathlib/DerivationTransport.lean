import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Algebra.Equiv

/-! # Transport of derivations across algebra equivalences

An algebra equivalence transports a derivation by conjugating its underlying linear map.

These declarations extend Mathlib's algebra APIs.

## Main results

* `AlgEquiv.transportDerivation_apply` gives the conjugation formula.
* `AlgEquiv.transportDerivation_symm` gives the inverse transport.
* `AlgEquiv.transportDerivation_trans` describes successive transports.
-/

namespace AlgEquiv

variable {R A B C : Type*}
variable [CommSemiring R] [CommSemiring A] [CommSemiring B] [CommSemiring C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- Conjugate a derivation by an algebra equivalence. -/
def transportDerivation (e : A ≃ₐ[R] B) (D : Derivation R A A) : Derivation R B B where
  toLinearMap := e.toLinearMap.comp (D.toLinearMap.comp e.symm.toLinearMap)
  map_one_eq_zero' := by
    change e (D (e.symm 1)) = 0
    simp only [map_one, Derivation.map_one_eq_zero, map_zero]
  leibniz' x y := by
    change e (D (e.symm (x * y))) = x • e (D (e.symm y)) + y • e (D (e.symm x))
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, apply_symm_apply]

/-- At an argument, transport conjugates the derivative value by the algebra equivalence. -/
@[simp]
theorem transportDerivation_apply (e : A ≃ₐ[R] B) (D : Derivation R A A) (x : B) :
    e.transportDerivation D x = e (D (e.symm x)) := rfl

/-- The value at a transported argument is the transported derivative value. -/
theorem transportDerivation_apply_image (e : A ≃ₐ[R] B) (D : Derivation R A A) (x : A) :
    e.transportDerivation D (e x) = e (D x) := by
  simp only [transportDerivation_apply, symm_apply_apply]

/-- Transport by the identity equivalence leaves a derivation unchanged. -/
@[simp]
theorem transportDerivation_refl (D : Derivation R A A) :
    (AlgEquiv.refl : A ≃ₐ[R] A).transportDerivation D = D := by
  ext x
  rfl

/-- Transporting back by the inverse equivalence recovers the derivation. -/
@[simp]
theorem transportDerivation_symm (e : A ≃ₐ[R] B) (D : Derivation R A A) :
    e.symm.transportDerivation (e.transportDerivation D) = D := by
  ext x
  simp only [transportDerivation_apply, AlgEquiv.symm_symm, symm_apply_apply]

/-- Two successive transports equal transport by the composed equivalence. -/
theorem transportDerivation_trans (e : A ≃ₐ[R] B) (f : B ≃ₐ[R] C)
    (D : Derivation R A A) :
    f.transportDerivation (e.transportDerivation D) = (e.trans f).transportDerivation D := by
  ext x
  rfl

/-- Transport preserves addition of derivations. -/
@[simp]
theorem transportDerivation_add (e : A ≃ₐ[R] B) (D E : Derivation R A A) :
    e.transportDerivation (D + E) = e.transportDerivation D + e.transportDerivation E := by
  ext x
  simp only [transportDerivation_apply, Derivation.add_apply, map_add]

/-- Transport preserves the zero derivation. -/
@[simp]
theorem transportDerivation_zero (e : A ≃ₐ[R] B) :
    e.transportDerivation (0 : Derivation R A A) = 0 := by
  ext x
  simp only [transportDerivation_apply, Derivation.zero_apply, map_zero]

/-- Transport preserves scalar multiplication of derivations by the base semiring. -/
@[simp]
theorem transportDerivation_smul (e : A ≃ₐ[R] B) (r : R) (D : Derivation R A A) :
    e.transportDerivation (r • D) = r • e.transportDerivation D := by
  ext x
  simp only [transportDerivation_apply, Derivation.smul_apply, map_smul]

/-- Transport across an algebra equivalence is injective on derivations. -/
theorem transportDerivation_injective (e : A ≃ₐ[R] B) :
    Function.Injective e.transportDerivation := by
  intro D E h
  have hback := congrArg e.symm.transportDerivation h
  simpa only [transportDerivation_symm] using hback

end AlgEquiv
