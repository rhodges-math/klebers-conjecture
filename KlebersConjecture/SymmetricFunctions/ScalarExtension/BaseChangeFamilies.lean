import KlebersConjecture.SymmetricFunctions.ScalarExtension.BaseChange
import KlebersConjecture.SymmetricFunctions.SymplecticCharacters.Basic

/-! # Standard families under tensor scalar extension

The tensor scalar-extension equivalence preserves Schur functions and symplectic characters,
as well as monomials. Its inverse sends these families to their unit pure tensors.

## Main results

* `baseChangeEquiv_tmul_schur` gives scalar extension on Schur functions.
* `baseChangeEquiv_tmul_symplecticCharacter` gives scalar extension on symplectic characters.
-/

noncomputable section

open scoped TensorProduct

attribute [local instance 1100] Algebra.toModule

namespace SymmetricFunction

/-- Scalar extension sends a pure tensor of a Schur function to its scalar multiple. -/
theorem baseChangeEquiv_tmul_schur (R : Type*) [CommRing R] (r : R) (μ : YoungDiagram) :
    baseChangeEquiv R (r ⊗ₜ[ℤ] schur ℤ μ) = r • schur R μ := by
  rw [baseChangeEquiv_tmul, map_schur]

/-- The inverse scalar-extension equivalence sends a Schur function to its unit pure tensor. -/
theorem baseChangeEquiv_symm_schur (R : Type*) [CommRing R] (μ : YoungDiagram) :
    (baseChangeEquiv R).symm (schur R μ) = 1 ⊗ₜ[ℤ] schur ℤ μ := by
  apply (baseChangeEquiv R).injective
  rw [AlgEquiv.apply_symm_apply, baseChangeEquiv_tmul_schur, one_smul]

/-- Pure tensors of symplectic characters map to the corresponding scalar multiples. -/
theorem baseChangeEquiv_tmul_symplecticCharacter (R : Type*) [CommRing R]
    (r : R) (μ : YoungDiagram) :
    baseChangeEquiv R (r ⊗ₜ[ℤ] symplecticCharacter ℤ μ) = r • symplecticCharacter R μ := by
  rw [baseChangeEquiv_tmul, map_symplecticCharacter]

/-- Inverse scalar extension sends a symplectic character to its unit pure tensor. -/
theorem baseChangeEquiv_symm_symplecticCharacter (R : Type*) [CommRing R] (μ : YoungDiagram) :
    (baseChangeEquiv R).symm (symplecticCharacter R μ) =
      1 ⊗ₜ[ℤ] symplecticCharacter ℤ μ := by
  apply (baseChangeEquiv R).injective
  rw [AlgEquiv.apply_symm_apply, baseChangeEquiv_tmul_symplecticCharacter, one_smul]

end SymmetricFunction
