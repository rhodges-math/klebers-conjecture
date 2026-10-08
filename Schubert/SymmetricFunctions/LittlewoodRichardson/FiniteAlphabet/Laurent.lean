import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic.NormNum

/-! # Integral finite Laurent polynomials

The exponent embedding identifies integral polynomials with Laurent polynomials supported
on nonnegative weights.

## Main results

* `exponentWeight_injective`: the exponent embedding is injective.
* `toLaurent_injective`: the polynomial-to-Laurent ring homomorphism is injective.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction.FiniteAlphabet

variable {n : ℕ}

/-- Integral polynomials in a finite alphabet. -/
abbrev IntPolynomial (n : ℕ) := MvPolynomial (Fin n) ℤ

/-- Integer weights on a finite alphabet. -/
abbrev IntWeight (n : ℕ) := Fin n → ℤ
/-- Integral Laurent polynomials on a finite weight lattice. -/
abbrev IntLaurent (n : ℕ) := AddMonoidAlgebra ℤ (IntWeight n)

/-- Embed a polynomial exponent into the integer weight lattice. -/
def exponentWeight : (Fin n →₀ ℕ) →+ IntWeight n where
  toFun a i := a i
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp

/-- The natural exponent embedding into integral weights is injective. -/
theorem exponentWeight_injective : Function.Injective (exponentWeight (n := n)) := by
  intro a b h
  ext i
  have hi := congrFun h i
  change (a i : ℤ) = (b i : ℤ) at hi
  exact_mod_cast hi

/-- The injective ring map from ordinary to Laurent polynomials. -/
def toLaurent : IntPolynomial n →+* IntLaurent n :=
  AddMonoidAlgebra.mapDomainRingHom ℤ exponentWeight

/-- The Laurent embedding preserves distinct integral polynomials. -/
theorem toLaurent_injective : Function.Injective (toLaurent (n := n)) :=
  AddMonoidAlgebra.mapDomain_injective exponentWeight_injective

/-- The Laurent embedding sends a monomial to its single exponent term. -/
@[simp] theorem toLaurent_monomial (a : Fin n →₀ ℕ) (z : ℤ) :
    toLaurent (MvPolynomial.monomial a z) =
      AddMonoidAlgebra.single (exponentWeight a) z := by
  exact AddMonoidAlgebra.mapDomain_single

end SymmetricFunction.FiniteAlphabet

end
