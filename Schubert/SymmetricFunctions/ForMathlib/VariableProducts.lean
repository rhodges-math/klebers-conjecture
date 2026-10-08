import Schubert.SymmetricFunctions.ForMathlib.GeneratorCoefficients
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # Product coefficients of a distinguished polynomial variable

These declarations extend Mathlib's multivariate polynomial API.

## Main results

* `MvPolynomial.variableCoeff_mul_at_degrees` extracts a highest product coefficient.
* `MvPolynomial.variableCoeff_pow_at_degree` extracts a highest power coefficient.
-/

noncomputable section

namespace MvPolynomial

variable {R σ : Type*} [CommRing R]

/-- At the sum of variable-degree bounds, product coefficients multiply. -/
theorem variableCoeff_mul_at_degrees (a : σ) (f g : MvPolynomial σ R) (n m : ℕ)
    (hf : f.degreeOf a ≤ n) (hg : g.degreeOf a ≤ m) :
    variableCoeff R a (n + m) (f * g) = variableCoeff R a n f * variableCoeff R a m g := by
  simp only [variableCoeff_apply, map_mul]
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le
    ((variablePolynomialEquiv_natDegree R a f).trans_le hf)
    ((variablePolynomialEquiv_natDegree R a g).trans_le hg), map_mul]

/-- A variable-degree bound gives the corresponding coefficient of every power. -/
theorem variableCoeff_pow_at_degree (a : σ) (f : MvPolynomial σ R) (n m : ℕ)
    (hf : f.degreeOf a ≤ n) :
    variableCoeff R a (m * n) (f ^ m) = variableCoeff R a n f ^ m := by
  simp only [variableCoeff_apply, map_pow]
  rw [Polynomial.coeff_pow_of_natDegree_le
    ((variablePolynomialEquiv_natDegree R a f).trans_le hf), map_pow]

end MvPolynomial
