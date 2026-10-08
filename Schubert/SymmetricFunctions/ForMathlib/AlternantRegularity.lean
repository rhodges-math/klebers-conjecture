import Schubert.SymmetricFunctions.ForMathlib.GeneratorCoefficients
import Mathlib.Algebra.Polynomial.Monic
import TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant
import Mathlib.Data.Fin.Rev

/-! # Regularity of variable differences and staircase alternants

Variable differences become monic polynomials when one variable is isolated. Their products
are therefore regular over arbitrary commutative coefficient rings.

These declarations extend Mathlib's algebra APIs.

## Main results

* `MvPolynomial.isRegular_X_sub_X` permits cancellation of a variable difference.
* `SymmetricFunction.FiniteAlphabet.isRegular_alternant_staircase` permits cancellation
  of the staircase alternant.
-/

namespace AlgEquiv

/-- An algebra equivalence carries regular elements to regular elements. -/
theorem isRegular_apply {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) {a : A} (ha : IsRegular a) :
    IsRegular (e a) := by
  rw [← isLeftRegular_iff_isRegular]
  intro x y h
  apply e.symm.injective
  apply ha.left
  simpa only [map_mul, symm_apply_apply] using congrArg e.symm h

end AlgEquiv

namespace MvPolynomial

variable (R : Type*) [CommRing R] {σ : Type*}

/-- A difference of distinct variables is regular over any commutative coefficient ring. -/
theorem isRegular_X_sub_X {i j : σ} (hji : j ≠ i) :
    IsRegular (X i - X j : MvPolynomial σ R) := by
  let e := variablePolynomialEquiv R i
  have hr : IsRegular (e (X i - X j)) := by
    change IsRegular (variablePolynomialEquiv R i (X i - X j))
    rw [map_sub, variablePolynomialEquiv_X_self, variablePolynomialEquiv_X_of_ne R i j hji]
    exact (Polynomial.monic_X_sub_C _).isRegular
  rw [← isLeftRegular_iff_isRegular]
  intro f g h
  apply e.injective
  apply hr.left
  simpa only [map_mul] using congrArg e h

/-- A finite product of differences of distinct variable pairs is regular. -/
theorem isRegular_prod_X_sub_X {ι : Type*} (s : Finset ι) (a b : ι → σ)
    (h : ∀ t ∈ s, b t ≠ a t) :
    IsRegular (∏ t ∈ s, (X (a t) - X (b t) : MvPolynomial σ R)) :=
  IsRegular.prod fun t ht => isRegular_X_sub_X R (h t ht)

end MvPolynomial

namespace SymmetricFunction.FiniteAlphabet

open TauCeti

variable (R : Type*) [CommRing R]

/-- The alternant with increasing consecutive exponents is regular. -/
theorem isRegular_alternant_fin_val (n : ℕ) :
    IsRegular (alternant (Fin n) R (fun j => (j : ℕ))) := by
  rw [alternant_fin_val_eq_vandermonde]
  apply IsRegular.prod
  intro i _
  apply IsRegular.prod
  intro j hj
  exact MvPolynomial.isRegular_X_sub_X R (ne_of_lt (Finset.mem_Ioi.mp hj))

/-- The descending staircase alternant is regular over any commutative coefficient ring. -/
theorem isRegular_alternant_staircase (n : ℕ) :
    IsRegular (alternant (Fin n) R (fun j => n - 1 - j)) := by
  have hs := alternant_comp_perm (R := R) (Fin.revPerm : Equiv.Perm (Fin n))
    (fun j => (j : ℕ))
  have he : (fun j : Fin n => (j : ℕ)) ∘ Fin.revPerm =
      (fun j : Fin n => n - 1 - (j : ℕ)) := by
    funext j
    simp only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
    omega
  rw [he] at hs
  rw [hs, Units.smul_def, zsmul_eq_mul]
  have hu : IsUnit (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) :
      MvPolynomial (Fin n) R)) :=
    (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))).isUnit.map (Int.castRingHom _)
  exact hu.isRegular.mul (isRegular_alternant_fin_val R n)

end SymmetricFunction.FiniteAlphabet
