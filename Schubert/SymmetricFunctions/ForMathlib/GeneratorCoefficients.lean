import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Degree.Support

/-!
# Coefficients of a polynomial generator

Coefficient extraction in one distinguished multivariate polynomial variable.

These declarations extend Mathlib's algebra APIs.

## Main results

* `variableCoeff_reconstruction`: finite reconstruction from the generator coefficients.
* `pderiv_eq_variableCoeff_one`: differentiation extracts coefficient one in degree at most one.
-/

noncomputable section

namespace MvPolynomial

variable (R : Type*) [CommRing R] {σ : Type*}

/-- A polynomial viewed as a polynomial in one distinguished variable. -/
def variablePolynomialEquiv (a : σ) :
    MvPolynomial σ R ≃ₐ[R] Polynomial (MvPolynomial {b : σ // b ≠ a} R) := by
  classical
  exact (renameEquiv R (Equiv.optionSubtypeNe a).symm).trans
    (optionEquivLeft R {b : σ // b ≠ a})

/-- The coefficient of a distinguished variable, embedded in the original variable set. -/
def variableCoeff (a : σ) (j : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (rename (Subtype.val : {b : σ // b ≠ a} → σ)).toLinearMap.comp
    (((Polynomial.lcoeff (MvPolynomial {b : σ // b ≠ a} R) j).restrictScalars R).comp
      (variablePolynomialEquiv R a).toLinearMap)

/-- The explicit coefficient extraction formula. -/
theorem variableCoeff_apply (a : σ) (j : ℕ) (f : MvPolynomial σ R) :
    variableCoeff R a j f =
      rename Subtype.val ((variablePolynomialEquiv R a f).coeff j) := rfl

/-- A scalar remains constant after isolating a variable. -/
theorem variablePolynomialEquiv_C (a : σ) (r : R) :
    variablePolynomialEquiv R a (C r) = Polynomial.C (C r) := by
  classical
  simp [variablePolynomialEquiv]

/-- The distinguished generator becomes the univariate generator. -/
theorem variablePolynomialEquiv_X_self (a : σ) :
    variablePolynomialEquiv R a (X a) = Polynomial.X := by
  classical
  simp [variablePolynomialEquiv]

/-- Every other generator becomes a constant univariate polynomial. -/
theorem variablePolynomialEquiv_X_of_ne (a b : σ) (h : b ≠ a) :
    variablePolynomialEquiv R a (X b) = Polynomial.C (X ⟨b, h⟩) := by
  classical
  simp [variablePolynomialEquiv, Equiv.optionSubtypeNe_symm_of_ne h]

/-- Reembedding the complementary variables gives a constant polynomial. -/
theorem variablePolynomialEquiv_rename (a : σ)
    (f : MvPolynomial {b : σ // b ≠ a} R) :
    variablePolynomialEquiv R a (rename Subtype.val f) = Polynomial.C f := by
  classical
  induction f using MvPolynomial.induction_on with
  | C r => simp [variablePolynomialEquiv_C]
  | add f g hf hg => simp [map_add, hf, hg]
  | mul_X f b hf =>
    simp [map_mul, hf, variablePolynomialEquiv_X_of_ne R a b.val b.property]

/-- Extracting a coefficient and isolating the variable produces a constant polynomial. -/
theorem variablePolynomialEquiv_coeff (a : σ) (j : ℕ) (f : MvPolynomial σ R) :
    variablePolynomialEquiv R a (variableCoeff R a j f) =
      Polynomial.C ((variablePolynomialEquiv R a f).coeff j) :=
  variablePolynomialEquiv_rename R a _

/-- Variable degree agrees with the degree of the isolated polynomial. -/
theorem variablePolynomialEquiv_natDegree (a : σ) (f : MvPolynomial σ R) :
    (variablePolynomialEquiv R a f).natDegree = f.degreeOf a := by
  classical
  exact (degreeOf_eq_natDegree a f).symm

/-- Extracted coefficients contain no distinguished variable. -/
theorem variableCoeff_notMem_vars (a : σ) (j : ℕ) (f : MvPolynomial σ R) :
    a ∉ (variableCoeff R a j f).vars := by
  classical
  intro h
  obtain ⟨b, _, hb⟩ := mem_vars_rename Subtype.val _ h
  exact b.property hb

/-- A coefficient has degree zero in the distinguished variable. -/
theorem degreeOf_variableCoeff (a : σ) (j : ℕ) (f : MvPolynomial σ R) :
    (variableCoeff R a j f).degreeOf a = 0 := by
  classical
  rw [← variablePolynomialEquiv_natDegree R a, variablePolynomialEquiv_coeff]
  exact Polynomial.natDegree_C _

/-- Coefficient extraction on scalar constants. -/
theorem variableCoeff_C (a : σ) (j : ℕ) (r : R) :
    variableCoeff R a j (C r) = if j = 0 then C r else 0 := by
  classical
  rw [variableCoeff_apply, variablePolynomialEquiv_C]
  by_cases h : j = 0
  · subst j
    simp
  · simp [Polynomial.coeff_C, h]

/-- Coefficient extraction on powers of the distinguished generator. -/
theorem variableCoeff_X_pow (a : σ) (j k : ℕ) :
    variableCoeff R a j (X a ^ k) = if k = j then 1 else 0 := by
  classical
  rw [variableCoeff_apply, map_pow, variablePolynomialEquiv_X_self]
  by_cases h : k = j
  · subst k
    simp
  · simp [Polynomial.coeff_X_pow, h, Ne.symm h]

/-- Coefficient extraction on a generator distinct from the distinguished variable. -/
theorem variableCoeff_X_of_ne (a b : σ) (h : b ≠ a) (j : ℕ) :
    variableCoeff R a j (X b) = if j = 0 then X b else 0 := by
  classical
  rw [variableCoeff_apply, variablePolynomialEquiv_X_of_ne R a b h]
  by_cases hj : j = 0
  · subst j
    simp
  · simp [Polynomial.coeff_C, hj]

/-- A coefficient above the distinguished-variable degree vanishes. -/
theorem variableCoeff_eq_zero_of_degree_lt (a : σ) (f : MvPolynomial σ R)
    {j : ℕ} (h : f.degreeOf a < j) : variableCoeff R a j f = 0 := by
  rw [variableCoeff_apply, Polynomial.coeff_eq_zero_of_natDegree_lt]
  · exact map_zero _
  · rwa [variablePolynomialEquiv_natDegree]

/-- A polynomial of distinguished-variable degree zero is its constant coefficient. -/
theorem variableCoeff_zero_of_degree_zero (a : σ) (f : MvPolynomial σ R)
    (h : f.degreeOf a = 0) : variableCoeff R a 0 f = f := by
  apply (variablePolynomialEquiv R a).injective
  rw [variablePolynomialEquiv_coeff]
  exact (Polynomial.eq_C_of_natDegree_eq_zero
    ((variablePolynomialEquiv_natDegree R a f).trans h)).symm

/-- Constant extraction fixes a polynomial whose variables omit the distinguished one. -/
theorem variableCoeff_zero_of_notMem_vars (a : σ) (f : MvPolynomial σ R)
    (h : a ∉ f.vars) : variableCoeff R a 0 f = f := by
  classical
  apply variableCoeff_zero_of_degree_zero
  simpa only [mem_vars_iff_degreeOf_ne_zero, not_not] using h

/-- Positive coefficients vanish for distinguished-variable degree zero. -/
theorem variableCoeff_eq_zero_of_degree_zero (a : σ) (f : MvPolynomial σ R)
    (h : f.degreeOf a = 0) {j : ℕ} (hj : 0 < j) : variableCoeff R a j f = 0 := by
  rw [variableCoeff_apply, Polynomial.coeff_eq_zero_of_natDegree_lt]
  · exact map_zero _
  · simpa [variablePolynomialEquiv_natDegree, h] using hj

/-- Extraction commutes with multiplication by a polynomial avoiding the variable. -/
theorem variableCoeff_mul_of_degree_zero (a : σ) (j : ℕ) (f g : MvPolynomial σ R)
    (hg : g.degreeOf a = 0) :
    variableCoeff R a j (f * g) = variableCoeff R a j f * g := by
  have hC : variablePolynomialEquiv R a g =
      Polynomial.C ((variablePolynomialEquiv R a g).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero
      ((variablePolynomialEquiv_natDegree R a g).trans hg)
  rw [variableCoeff_apply, map_mul, hC, Polynomial.coeff_mul_C, map_mul]
  rw [← variableCoeff_apply R a 0 g, variableCoeff_zero_of_degree_zero R a g hg]
  rfl

/-- A variable-free factor can also be extracted on the left. -/
theorem variableCoeff_mul_left_of_degree_zero (a : σ) (j : ℕ)
    (f g : MvPolynomial σ R) (hg : g.degreeOf a = 0) :
    variableCoeff R a j (g * f) = g * variableCoeff R a j f := by
  simpa only [mul_comm] using variableCoeff_mul_of_degree_zero R a j f g hg

/-- Finite reconstruction from the coefficients of a distinguished variable. -/
theorem variableCoeff_reconstruction (a : σ) (f : MvPolynomial σ R) :
    f = ∑ j ∈ Finset.range (f.degreeOf a + 1), variableCoeff R a j f * X a ^ j := by
  classical
  apply (variablePolynomialEquiv R a).injective
  simpa only [map_sum, map_mul, map_pow, variablePolynomialEquiv_coeff,
    variablePolynomialEquiv_X_self, ← variablePolynomialEquiv_natDegree R a f] using
    Polynomial.as_sum_range_C_mul_X_pow (variablePolynomialEquiv R a f)

/-- A polynomial of distinguished-variable degree at most one has two terms. -/
theorem variableCoeff_reconstruction_one (a : σ) (f : MvPolynomial σ R)
    (h : f.degreeOf a ≤ 1) :
    f = variableCoeff R a 1 f * X a + variableCoeff R a 0 f := by
  apply (variablePolynomialEquiv R a).injective
  simpa only [map_add, map_mul, variablePolynomialEquiv_coeff,
    variablePolynomialEquiv_X_self] using Polynomial.eq_X_add_C_of_natDegree_le_one
      ((variablePolynomialEquiv_natDegree R a f).trans_le h)

/-- In variable degree at most one, differentiation extracts the linear coefficient. -/
theorem pderiv_eq_variableCoeff_one (a : σ) (f : MvPolynomial σ R)
    (h : f.degreeOf a ≤ 1) : pderiv a f = variableCoeff R a 1 f := by
  conv_lhs => rw [variableCoeff_reconstruction_one R a f h]
  rw [map_add, pderiv_mul, pderiv_eq_zero_of_notMem_vars
    (variableCoeff_notMem_vars R a 1 f),
    pderiv_eq_zero_of_notMem_vars (variableCoeff_notMem_vars R a 0 f),
    pderiv_X_self, zero_mul, mul_one, zero_add, add_zero]

end MvPolynomial

namespace AlgEquiv

variable {R σ A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Extract a polynomial-generator coefficient through an algebra presentation. -/
def generatorCoeff (e : MvPolynomial σ R ≃ₐ[R] A) (a : σ) (j : ℕ) : A →ₗ[R] A :=
  e.toLinearMap.comp ((MvPolynomial.variableCoeff R a j).comp e.symm.toLinearMap)

/-- The degree in a polynomial generator through an algebra presentation. -/
def generatorDegree (e : MvPolynomial σ R ≃ₐ[R] A) (a : σ) (f : A) : ℕ :=
  (e.symm f).degreeOf a

/-- Generator extraction is conjugation of polynomial variable extraction. -/
theorem generatorCoeff_apply (e : MvPolynomial σ R ≃ₐ[R] A) (a : σ) (j : ℕ) (f : A) :
    e.generatorCoeff a j f = e (MvPolynomial.variableCoeff R a j (e.symm f)) := rfl

/-- Every extracted coefficient has degree zero in the extracted generator. -/
theorem generatorDegree_generatorCoeff (e : MvPolynomial σ R ≃ₐ[R] A)
    (a : σ) (j : ℕ) (f : A) : e.generatorDegree a (e.generatorCoeff a j f) = 0 := by
  rw [generatorDegree, generatorCoeff_apply, e.symm_apply_apply]
  exact MvPolynomial.degreeOf_variableCoeff R a j _

/-- The constant coefficient fixes elements of generator degree zero. -/
theorem generatorCoeff_zero_of_degree_zero (e : MvPolynomial σ R ≃ₐ[R] A)
    (a : σ) (f : A) (h : e.generatorDegree a f = 0) :
    e.generatorCoeff a 0 f = f := by
  rw [generatorCoeff_apply, MvPolynomial.variableCoeff_zero_of_degree_zero R a _ h,
    e.apply_symm_apply]

/-- Coefficients of positive order vanish in generator degree zero. -/
theorem generatorCoeff_eq_zero (e : MvPolynomial σ R ≃ₐ[R] A)
    (a : σ) (f : A) (h : e.generatorDegree a f = 0) {j : ℕ} (hj : 0 < j) :
    e.generatorCoeff a j f = 0 := by
  rw [generatorCoeff_apply, MvPolynomial.variableCoeff_eq_zero_of_degree_zero R a _ h hj,
    map_zero]

/-- A generator-independent factor passes through coefficient extraction. -/
theorem generatorCoeff_mul_of_degree_zero (e : MvPolynomial σ R ≃ₐ[R] A)
    (a : σ) (j : ℕ) (f g : A) (hg : e.generatorDegree a g = 0) :
    e.generatorCoeff a j (f * g) = e.generatorCoeff a j f * g := by
  rw [generatorCoeff_apply, map_mul,
    MvPolynomial.variableCoeff_mul_of_degree_zero R a j _ _ hg,
    map_mul, e.apply_symm_apply, ← generatorCoeff_apply]

end AlgEquiv
