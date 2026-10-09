import KlebersConjecture.Paper.Products
import KlebersConjecture.SymmetricFunctions.ScalarExtension.BaseChangeFamilies

/-! # Complementary products under tensor scalar extension

Unit pure tensors of the integral pair products map to the corresponding pair products
under the scalar-extension equivalence.

## Main results

* `tmul_schurPair_mk`, `tmul_monomialPair_mk` and `tmul_symplecticPair_mk` factor pure tensors.
* `baseChangeEquiv_schurPair` and the monomial and symplectic versions transport pair products.
-/

noncomputable section

open scoped TensorProduct

attribute [local instance 1100] Algebra.toModule

namespace ComplementaryProducts

/-- The unit tensor of a Schur pair is the product of the unit tensors of its factors. -/
theorem tmul_schurPair_mk (R : Type*) [CommRing R] (α β : YoungDiagram) :
    (1 : R) ⊗ₜ[ℤ] schurPairProduct ℤ s(α, β) =
      (1 ⊗ₜ[ℤ] SymmetricFunction.schur ℤ α) *
        (1 ⊗ₜ[ℤ] SymmetricFunction.schur ℤ β) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, schurPairProduct_mk]

/-- The unit tensor of a monomial pair is the product of the unit tensors of its factors. -/
theorem tmul_monomialPair_mk (R : Type*) [CommRing R] (α β : YoungDiagram) :
    (1 : R) ⊗ₜ[ℤ] monomialPairProduct ℤ s(α, β) =
      (1 ⊗ₜ[ℤ] SymmetricFunction.monomial ℤ α) *
        (1 ⊗ₜ[ℤ] SymmetricFunction.monomial ℤ β) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, monomialPairProduct_mk]

/-- The unit tensor of a character pair is the product of the unit tensors of its factors. -/
theorem tmul_symplecticPair_mk (R : Type*) [CommRing R] (α β : YoungDiagram) :
    (1 : R) ⊗ₜ[ℤ] symplecticPairProduct ℤ s(α, β) =
      (1 ⊗ₜ[ℤ] SymmetricFunction.symplecticCharacter ℤ α) *
        (1 ⊗ₜ[ℤ] SymmetricFunction.symplecticCharacter ℤ β) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, symplecticPairProduct_mk]

/-- The tensor scalar-extension equivalence preserves every Schur pair product. -/
theorem baseChangeEquiv_schurPair (R : Type*) [CommRing R] (p : Sym2 YoungDiagram) :
    SymmetricFunction.baseChangeEquiv R (1 ⊗ₜ[ℤ] schurPairProduct ℤ p) =
      schurPairProduct R p := by
  rw [SymmetricFunction.baseChangeEquiv_tmul, map_schurPairProduct, one_smul]

/-- The tensor scalar-extension equivalence preserves every monomial pair product. -/
theorem baseChangeEquiv_monomialPair (R : Type*) [CommRing R] (p : Sym2 YoungDiagram) :
    SymmetricFunction.baseChangeEquiv R (1 ⊗ₜ[ℤ] monomialPairProduct ℤ p) =
      monomialPairProduct R p := by
  rw [SymmetricFunction.baseChangeEquiv_tmul, map_monomialPairProduct, one_smul]

/-- The tensor scalar-extension equivalence preserves every symplectic-character pair product. -/
theorem baseChangeEquiv_symplecticPair (R : Type*) [CommRing R] (p : Sym2 YoungDiagram) :
    SymmetricFunction.baseChangeEquiv R (1 ⊗ₜ[ℤ] symplecticPairProduct ℤ p) =
      symplecticPairProduct R p := by
  rw [SymmetricFunction.baseChangeEquiv_tmul, map_symplecticPairProduct, one_smul]

end ComplementaryProducts
