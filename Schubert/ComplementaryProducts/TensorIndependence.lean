import Schubert.ComplementaryProducts.TensorProducts
import Schubert.ComplementaryProducts.SplittingIndependence
import Schubert.ComplementaryProducts.RectangularIndependence
import Schubert.ComplementaryProducts.UniversalProducts
import Schubert.ComplementaryProducts.MonomialIndependence

/-! # Independence in tensor scalar extension

Integral pair products give the corresponding symmetric-function products under the
scalar-extension equivalence. Their independence therefore holds in the tensor carrier.

## Main results

* `splitting_linearIndependent_tensor` gives splitting independence in scalar extension.
* `kleber_linearIndependent_tensor` gives rectangular Schur independence in scalar extension.
* `symplectic_linearIndependent_tensor` gives character independence in scalar extension.
* `monomial_linearIndependent_tensor` gives monomial independence in scalar extension.
* `monomial_linearIndependent_int_tensor` gives integral monomial independence in that carrier.
-/

noncomputable section

open scoped TensorProduct

attribute [local instance 1100] Algebra.toModule

namespace ComplementaryProducts

/-- Schur splitting products are independent in tensor scalar extension over every ring. -/
theorem splitting_linearIndependent_tensor (R : Type*) [CommRing R] (θ : YoungDiagram) :
    LinearIndependent R (fun p : splittings θ =>
      (1 : R) ⊗ₜ[ℤ] schurPairProduct ℤ (p : Sym2 YoungDiagram)) := by
  apply LinearIndependent.of_comp (SymmetricFunction.baseChangeEquiv R).toLinearMap
  change LinearIndependent R (fun p : splittings θ =>
    SymmetricFunction.baseChangeEquiv R (1 ⊗ₜ[ℤ] schurPairProduct ℤ p.val))
  simpa only [baseChangeEquiv_schurPair] using splitting_linearIndependent R θ

/-- Rectangular Schur products are independent in tensor scalar extension over every ring. -/
theorem kleber_linearIndependent_tensor (R : Type*) [CommRing R] (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    LinearIndependent R (fun p : complementaryPairs a b =>
      (1 : R) ⊗ₜ[ℤ] schurPairProduct ℤ (p : Sym2 YoungDiagram)) := by
  apply LinearIndependent.of_comp (SymmetricFunction.baseChangeEquiv R).toLinearMap
  change LinearIndependent R (fun p : complementaryPairs a b =>
    SymmetricFunction.baseChangeEquiv R (1 ⊗ₜ[ℤ] schurPairProduct ℤ p.val))
  simpa only [baseChangeEquiv_schurPair] using kleber_linearIndependent R a b ha hb

/-- Rectangular symplectic products are independent in tensor scalar extension over every field. -/
theorem symplectic_linearIndependent_tensor (F : Type*) [Field F] (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    LinearIndependent F (fun p : complementaryPairs a b =>
      (1 : F) ⊗ₜ[ℤ] symplecticPairProduct ℤ (p : Sym2 YoungDiagram)) := by
  apply LinearIndependent.of_comp (SymmetricFunction.baseChangeEquiv F).toLinearMap
  change LinearIndependent F (fun p : complementaryPairs a b =>
    SymmetricFunction.baseChangeEquiv F (1 ⊗ₜ[ℤ] symplecticPairProduct ℤ p.val))
  simpa only [baseChangeEquiv_symplecticPair] using symplectic_linearIndependent F a b ha hb

/-- Rectangular monomial products are independent in characteristic-zero tensor scalar extension. -/
theorem monomial_linearIndependent_tensor (F : Type*) [Field F] [CharZero F] (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    LinearIndependent F (fun p : complementaryPairs a b =>
      (1 : F) ⊗ₜ[ℤ] monomialPairProduct ℤ (p : Sym2 YoungDiagram)) := by
  apply LinearIndependent.of_comp (SymmetricFunction.baseChangeEquiv F).toLinearMap
  change LinearIndependent F (fun p : complementaryPairs a b =>
    SymmetricFunction.baseChangeEquiv F (1 ⊗ₜ[ℤ] monomialPairProduct ℤ p.val))
  simpa only [baseChangeEquiv_monomialPair] using monomial_linearIndependent F a b ha hb

/-- Integral rectangular monomial products are independent in integral tensor scalar extension. -/
theorem monomial_linearIndependent_int_tensor (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    LinearIndependent ℤ (fun p : complementaryPairs a b =>
      (1 : ℤ) ⊗ₜ[ℤ] monomialPairProduct ℤ (p : Sym2 YoungDiagram)) := by
  apply LinearIndependent.of_comp (SymmetricFunction.baseChangeEquiv ℤ).toLinearMap
  change LinearIndependent ℤ (fun p : complementaryPairs a b =>
    SymmetricFunction.baseChangeEquiv ℤ (1 ⊗ₜ[ℤ] monomialPairProduct ℤ p.val))
  simp only [baseChangeEquiv_monomialPair]
  convert! monomial_linearIndependent_int a b ha hb using 1

end ComplementaryProducts
