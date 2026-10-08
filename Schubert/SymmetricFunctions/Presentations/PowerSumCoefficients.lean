import Schubert.SymmetricFunctions.Presentations.PowerSumPresentation
import Schubert.SymmetricFunctions.ForMathlib.PresentationCoefficients

/-! # Coefficients of positive power-sum generators

The rational power-sum presentation transports distinguished-variable coefficients to
symmetric functions.

## Main results

* `powerSumCoeff_generator_pow` evaluates extraction on distinguished generator powers.
* `mem_adjoin_powerSum_iff` characterizes the coefficient algebra omitting one generator.
* `powerSumCoeff_mem_adjoin` places extracted coefficients in that coefficient algebra.
* `powerSumCoeff_reconstruction` and `powerSumCoeff_sum_mul_pow` show that the coefficients
  `[p_n^j]` are the coefficients of the unique expansion as a polynomial in `p_n`.
-/

noncomputable section

namespace SymmetricFunction

/-- A power-sum-generator coefficient, embedded back into the symmetric-function algebra. -/
def powerSumCoeff (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ+) (j : ℕ) :
    SymmetricFunction R →ₗ[R] SymmetricFunction R :=
  (powerSumPresentation R).generatorCoeff n j

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Explicit conjugation formula for power-sum-generator coefficients. -/
theorem powerSumCoeff_apply (n : ℕ+) (j : ℕ) (f : SymmetricFunction R) :
    powerSumCoeff R n j f = powerSumPresentation R
      (MvPolynomial.variableCoeff R n j ((powerSumPresentation R).symm f)) := rfl

/-- Coefficient extraction on a polynomial image is transported extraction. -/
theorem powerSumCoeff_image (n : ℕ+) (j : ℕ) (p : MvPolynomial ℕ+ R) :
    powerSumCoeff R n j (powerSumPresentation R p) =
      powerSumPresentation R (MvPolynomial.variableCoeff R n j p) :=
  (powerSumPresentation R).generatorCoeff_image n j p

/-- Generator coefficient extraction preserves addition. -/
theorem powerSumCoeff_add (n : ℕ+) (j : ℕ) (f g : SymmetricFunction R) :
    powerSumCoeff R n j (f + g) = powerSumCoeff R n j f + powerSumCoeff R n j g :=
  map_add _ _ _

/-- Generator coefficient extraction preserves scalar multiplication. -/
theorem powerSumCoeff_smul (n : ℕ+) (j : ℕ) (r : R) (f : SymmetricFunction R) :
    powerSumCoeff R n j (r • f) = r • powerSumCoeff R n j f := map_smul _ _ _

/-- Scalar constants have only a constant generator coefficient. -/
theorem powerSumCoeff_constant (n : ℕ+) (j : ℕ) (r : R) :
    powerSumCoeff R n j (algebraMap R (SymmetricFunction R) r) =
      if j = 0 then algebraMap R (SymmetricFunction R) r else 0 :=
  (powerSumPresentation R).generatorCoeff_constant n j r

/-- A power of the distinguished power-sum generator has its single expected coefficient. -/
theorem powerSumCoeff_generator_pow (n : ℕ+) (j k : ℕ) :
    powerSumCoeff R n j (powerSum R n ^ k) = if k = j then 1 else 0 := by
  simpa only [powerSumCoeff, powerSumPresentation_apply_X] using
    (powerSumPresentation R).generatorCoeff_generator_pow n j k

/-- A different power-sum generator contributes only to coefficient zero. -/
theorem powerSumCoeff_other_generator (n m : ℕ+) (hm : m ≠ n) (j : ℕ) :
    powerSumCoeff R n j (powerSum R m) =
      if j = 0 then powerSum R m else 0 := by
  simpa only [powerSumCoeff, powerSumPresentation_apply_X] using
    (powerSumPresentation R).generatorCoeff_other_generator n m hm j

/-- An extracted coefficient is independent of the distinguished power-sum generator. -/
theorem powerSumCoeff_degree_zero (n : ℕ+) (j : ℕ) (f : SymmetricFunction R) :
    ((powerSumPresentation R).symm (powerSumCoeff R n j f)).degreeOf n = 0 :=
  (powerSumPresentation R).generatorDegree_generatorCoeff n j f

/-- The other power-sum generators generate exactly distinguished-generator degree zero. -/
theorem mem_adjoin_powerSum_iff (n : ℕ+) (f : SymmetricFunction R) :
    f ∈ Algebra.adjoin R ((fun k : ℕ+ => powerSum R k) '' {k | k ≠ n}) ↔
      ((powerSumPresentation R).symm f).degreeOf n = 0 := by
  simpa only [AlgEquiv.generatorDegree, powerSumPresentation_apply_X] using
    (powerSumPresentation R).mem_adjoin_generator_iff n f

/-- Power-sum-generator extraction lands in the algebra of the remaining generators. -/
theorem powerSumCoeff_mem_adjoin (n : ℕ+) (j : ℕ) (f : SymmetricFunction R) :
    powerSumCoeff R n j f ∈
      Algebra.adjoin R ((fun k : ℕ+ => powerSum R k) '' {k | k ≠ n}) :=
  (mem_adjoin_powerSum_iff n _).mpr (powerSumCoeff_degree_zero n j f)

/-- Extraction fixes an independent function in coefficient zero. -/
theorem powerSumCoeff_zero_of_degreeOf_eq_zero (n : ℕ+) (f : SymmetricFunction R)
    (h : ((powerSumPresentation R).symm f).degreeOf n = 0) :
    powerSumCoeff R n 0 f = f :=
  (powerSumPresentation R).generatorCoeff_zero_of_degree_zero n f h

/-- Extraction commutes with multiplication by a generator-independent factor. -/
theorem powerSumCoeff_mul_of_degreeOf_eq_zero (n : ℕ+) (j : ℕ) (f g : SymmetricFunction R)
    (hg : ((powerSumPresentation R).symm g).degreeOf n = 0) :
    powerSumCoeff R n j (f * g) = powerSumCoeff R n j f * g :=
  (powerSumPresentation R).generatorCoeff_mul_of_degree_zero n j f g hg

/-- Positive coefficients of a generator-independent function vanish. -/
theorem powerSumCoeff_pos_of_degreeOf_eq_zero (n : ℕ+) (f : SymmetricFunction R)
    (h : ((powerSumPresentation R).symm f).degreeOf n = 0) {j : ℕ} (hj : 0 < j) :
    powerSumCoeff R n j f = 0 :=
  (powerSumPresentation R).generatorCoeff_eq_zero n f h hj

/-- Extraction recovers an independent factor after multiplying by the matching generator power. -/
theorem powerSumCoeff_generator_mul (n : ℕ+) (j : ℕ) (g : SymmetricFunction R)
    (hg : ((powerSumPresentation R).symm g).degreeOf n = 0) :
    powerSumCoeff R n j (powerSum R n ^ j * g) = g := by
  simpa only [powerSumCoeff, powerSumPresentation_apply_X] using
    (powerSumPresentation R).generatorCoeff_generator_mul n j g hg

/-- A symmetric function is the sum of its coefficients in `p_n` times the powers of `p_n`. -/
theorem powerSumCoeff_reconstruction (n : ℕ+) (f : SymmetricFunction R) :
    f = ∑ j ∈ Finset.range (((powerSumPresentation R).symm f).degreeOf n + 1),
      powerSumCoeff R n j f * powerSum R n ^ j := by
  simpa only [powerSumCoeff, AlgEquiv.generatorDegree, powerSumPresentation_apply_X] using
    (powerSumPresentation R).generatorCoeff_reconstruction n f

/-- The coefficients of an expansion in powers of `p_n`, with coefficients in the algebra
generated by the other power sums, are the coefficients `[p_n^j]` of the sum: the expansion of
a symmetric function as a polynomial in `p_n` is unique. -/
theorem powerSumCoeff_sum_mul_pow (n : ℕ+) (N : ℕ) (c : ℕ → SymmetricFunction R)
    (hc : ∀ i, c i ∈ Algebra.adjoin R ((fun k : ℕ+ => powerSum R k) '' {k | k ≠ n}))
    (j : ℕ) :
    powerSumCoeff R n j (∑ i ∈ Finset.range N, c i * powerSum R n ^ i) =
      if j < N then c j else 0 := by
  simpa only [powerSumCoeff, powerSumPresentation_apply_X] using
    (powerSumPresentation R).generatorCoeff_sum_mul_pow n N c
      (fun i => (mem_adjoin_powerSum_iff n (c i)).mp (hc i)) j

end SymmetricFunction
