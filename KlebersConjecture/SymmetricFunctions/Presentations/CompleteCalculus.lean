import KlebersConjecture.SymmetricFunctions.Presentations.CompletePresentation
import KlebersConjecture.SymmetricFunctions.ForMathlib.DerivationTransport
import KlebersConjecture.SymmetricFunctions.ForMathlib.PresentationCoefficients

/-! # Derivatives and generator coefficients of complete symmetric functions

The positive complete presentation transports polynomial derivatives and distinguished-variable
coefficient maps to symmetric functions.

## Main results

* `completeDerivation_generator` and `derivation_ext_complete` characterize differentiation.
* `mem_adjoin_complete_iff` characterizes the coefficient algebra omitting one generator.
* `completeCoeff_mem_adjoin` places extracted coefficients in that coefficient algebra.
* `completeCoeff_reconstruction` and `completeCoeff_sum_mul_pow` show that the coefficients
  `[h_n^j]` are the coefficients of the unique expansion as a polynomial in `h_n`.
* `completeDerivation_eq_coeff_one` identifies differentiation with extraction in degree one.
-/

noncomputable section

namespace SymmetricFunction

/-- Differentiation with respect to a positive complete generator. -/
def completeDerivation (R : Type*) [CommRing R] (n : ℕ+) :
    Derivation R (SymmetricFunction R) (SymmetricFunction R) :=
  (completePresentation R).transportDerivation (MvPolynomial.pderiv n)

/-- A complete-generator coefficient, embedded back into the symmetric-function algebra. -/
def completeCoeff (R : Type*) [CommRing R] (n : ℕ+) (j : ℕ) :
    SymmetricFunction R →ₗ[R] SymmetricFunction R :=
  (completePresentation R).generatorCoeff n j

/-- The degree in a positive complete generator. -/
def completeDegree (R : Type*) [CommRing R] (n : ℕ+) (f : SymmetricFunction R) : ℕ :=
  (completePresentation R).generatorDegree n f

/-- Complete-generator degree is polynomial variable degree in complete coordinates. -/
theorem completeDegree_apply (R : Type*) [CommRing R] (n : ℕ+) (f : SymmetricFunction R) :
    completeDegree R n f = ((completePresentation R).symm f).degreeOf n := rfl

variable {R : Type*} [CommRing R]

/-- The derivative is conjugate to the polynomial partial derivative. -/
theorem completeDerivation_apply (n : ℕ+) (f : SymmetricFunction R) :
    completeDerivation R n f =
      completePresentation R (MvPolynomial.pderiv n ((completePresentation R).symm f)) := rfl

/-- Derivatives of polynomial images are transported partial derivatives. -/
theorem completeDerivation_image (n : ℕ+) (p : MvPolynomial ℕ+ R) :
    completeDerivation R n (completePresentation R p) =
      completePresentation R (MvPolynomial.pderiv n p) := by
  rw [completeDerivation_apply, AlgEquiv.symm_apply_apply]

/-- A positive complete generator has Kronecker derivative. -/
theorem completeDerivation_generator (n m : ℕ+) :
    completeDerivation R n (complete R (m.val : ℤ)) = if m = n then 1 else 0 := by
  classical
  rw [completeDerivation_apply, completePresentation_symm_complete, MvPolynomial.pderiv_X]
  simp only [Pi.single_apply, apply_ite, map_one, map_zero]
  split_ifs <;> rfl

/-- Scalars have zero complete-generator derivative. -/
theorem completeDerivation_constant (n : ℕ+) (r : R) :
    completeDerivation R n (algebraMap R (SymmetricFunction R) r) = 0 :=
  Derivation.map_algebraMap _ _

/-- The complete derivative obeys the product rule. -/
theorem completeDerivation_mul (n : ℕ+) (f g : SymmetricFunction R) :
    completeDerivation R n (f * g) =
      f * completeDerivation R n g + g * completeDerivation R n f := by
  simpa only [smul_eq_mul] using (completeDerivation R n).leibniz f g

/-- A derivation is determined by its values on the positive complete generators. -/
theorem derivation_ext_complete
    {D E : Derivation R (SymmetricFunction R) (SymmetricFunction R)}
    (h : ∀ n : ℕ+, D (complete R (n.val : ℤ)) = E (complete R (n.val : ℤ))) : D = E := by
  apply (completePresentation R).symm.transportDerivation_injective
  apply MvPolynomial.derivation_ext
  intro n
  simp only [AlgEquiv.transportDerivation_apply, AlgEquiv.symm_symm,
    completePresentation_apply_X, h]

/-- Explicit conjugation formula for complete-generator coefficients. -/
theorem completeCoeff_apply (n : ℕ+) (j : ℕ) (f : SymmetricFunction R) :
    completeCoeff R n j f = completePresentation R
      (MvPolynomial.variableCoeff R n j ((completePresentation R).symm f)) := rfl

/-- Coefficient extraction on a polynomial image is transported extraction. -/
theorem completeCoeff_image (n : ℕ+) (j : ℕ) (p : MvPolynomial ℕ+ R) :
    completeCoeff R n j (completePresentation R p) =
      completePresentation R (MvPolynomial.variableCoeff R n j p) :=
  (completePresentation R).generatorCoeff_image n j p

/-- Generator coefficient extraction preserves addition. -/
theorem completeCoeff_add (n : ℕ+) (j : ℕ) (f g : SymmetricFunction R) :
    completeCoeff R n j (f + g) = completeCoeff R n j f + completeCoeff R n j g :=
  map_add _ _ _

/-- Generator coefficient extraction preserves scalar multiplication. -/
theorem completeCoeff_smul (n : ℕ+) (j : ℕ) (r : R) (f : SymmetricFunction R) :
    completeCoeff R n j (r • f) = r • completeCoeff R n j f := map_smul _ _ _

/-- Scalar constants have only a constant generator coefficient. -/
theorem completeCoeff_constant (n : ℕ+) (j : ℕ) (r : R) :
    completeCoeff R n j (algebraMap R (SymmetricFunction R) r) =
      if j = 0 then algebraMap R (SymmetricFunction R) r else 0 :=
  (completePresentation R).generatorCoeff_constant n j r

/-- A power of the distinguished complete generator has its single expected coefficient. -/
theorem completeCoeff_generator_pow (n : ℕ+) (j k : ℕ) :
    completeCoeff R n j (complete R (n.val : ℤ) ^ k) = if k = j then 1 else 0 := by
  simpa only [completeCoeff, completePresentation_apply_X] using
    (completePresentation R).generatorCoeff_generator_pow n j k

/-- A different complete generator contributes only to coefficient zero. -/
theorem completeCoeff_other_generator (n m : ℕ+) (hm : m ≠ n) (j : ℕ) :
    completeCoeff R n j (complete R (m.val : ℤ)) =
      if j = 0 then complete R (m.val : ℤ) else 0 := by
  simpa only [completeCoeff, completePresentation_apply_X] using
    (completePresentation R).generatorCoeff_other_generator n m hm j

/-- An extracted coefficient is independent of the distinguished complete generator. -/
theorem completeCoeff_degree_zero (n : ℕ+) (j : ℕ) (f : SymmetricFunction R) :
    completeDegree R n (completeCoeff R n j f) = 0 :=
  (completePresentation R).generatorDegree_generatorCoeff n j f

/-- The algebra of the other complete generators is exactly distinguished-generator degree zero. -/
theorem mem_adjoin_complete_iff (n : ℕ+) (f : SymmetricFunction R) :
    f ∈ Algebra.adjoin R
      ((fun k : ℕ+ => complete R (k.val : ℤ)) '' {k | k ≠ n}) ↔
        completeDegree R n f = 0 := by
  simpa only [completeDegree, completePresentation_apply_X] using
    (completePresentation R).mem_adjoin_generator_iff n f

/-- Complete-generator extraction lands in the algebra of the remaining generators. -/
theorem completeCoeff_mem_adjoin (n : ℕ+) (j : ℕ) (f : SymmetricFunction R) :
    completeCoeff R n j f ∈ Algebra.adjoin R
      ((fun k : ℕ+ => complete R (k.val : ℤ)) '' {k | k ≠ n}) :=
  (mem_adjoin_complete_iff n _).mpr (completeCoeff_degree_zero n j f)

/-- Extraction fixes an independent function in coefficient zero. -/
theorem completeCoeff_zero_of_degreeOf_eq_zero (n : ℕ+) (f : SymmetricFunction R)
    (h : completeDegree R n f = 0) :
    completeCoeff R n 0 f = f :=
  (completePresentation R).generatorCoeff_zero_of_degree_zero n f h

/-- Extraction commutes with multiplication by a generator-independent factor. -/
theorem completeCoeff_mul_of_degreeOf_eq_zero (n : ℕ+) (j : ℕ) (f g : SymmetricFunction R)
    (hg : completeDegree R n g = 0) :
    completeCoeff R n j (f * g) = completeCoeff R n j f * g :=
  (completePresentation R).generatorCoeff_mul_of_degree_zero n j f g hg

/-- Positive coefficients of a generator-independent function vanish. -/
theorem completeCoeff_pos_of_degreeOf_eq_zero (n : ℕ+) (f : SymmetricFunction R)
    (h : completeDegree R n f = 0) {j : ℕ} (hj : 0 < j) :
    completeCoeff R n j f = 0 :=
  (completePresentation R).generatorCoeff_eq_zero n f h hj

/-- Extraction recovers an independent factor after multiplying by the matching generator power. -/
theorem completeCoeff_generator_mul (n : ℕ+) (j : ℕ) (g : SymmetricFunction R)
    (hg : completeDegree R n g = 0) :
    completeCoeff R n j (complete R (n.val : ℤ) ^ j * g) = g := by
  simpa only [completeCoeff, completePresentation_apply_X] using
    (completePresentation R).generatorCoeff_generator_mul n j g hg

/-- A symmetric function is the sum of its coefficients in `h_n` times the powers of `h_n`. -/
theorem completeCoeff_reconstruction (n : ℕ+) (f : SymmetricFunction R) :
    f = ∑ j ∈ Finset.range (completeDegree R n f + 1),
      completeCoeff R n j f * complete R (n.val : ℤ) ^ j := by
  simpa only [completeCoeff, completeDegree, completePresentation_apply_X] using
    (completePresentation R).generatorCoeff_reconstruction n f

/-- The coefficients of an expansion in powers of `h_n`, with coefficients in the algebra
generated by the other complete functions, are the coefficients `[h_n^j]` of the sum: the
expansion of a symmetric function as a polynomial in `h_n` is unique. -/
theorem completeCoeff_sum_mul_pow (n : ℕ+) (N : ℕ) (c : ℕ → SymmetricFunction R)
    (hc : ∀ i, c i ∈ Algebra.adjoin R
      ((fun k : ℕ+ => complete R (k.val : ℤ)) '' {k | k ≠ n})) (j : ℕ) :
    completeCoeff R n j (∑ i ∈ Finset.range N, c i * complete R (n.val : ℤ) ^ i) =
      if j < N then c j else 0 := by
  simpa only [completeCoeff, completePresentation_apply_X] using
    (completePresentation R).generatorCoeff_sum_mul_pow n N c
      (fun i => (mem_adjoin_complete_iff n (c i)).mp (hc i)) j

/-- In distinguished-generator degree at most one, the derivative is coefficient one. -/
theorem completeDerivation_eq_coeff_one (n : ℕ+) (f : SymmetricFunction R)
    (h : completeDegree R n f ≤ 1) :
    completeDerivation R n f = completeCoeff R n 1 f := by
  rw [completeDerivation_apply, completeCoeff_apply,
    MvPolynomial.pderiv_eq_variableCoeff_one R n _ h]

end SymmetricFunction
