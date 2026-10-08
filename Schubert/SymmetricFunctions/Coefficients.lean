import Schubert.SymmetricFunctions.Basic

/-! # Coefficients of symmetric functions

Coefficients in the monomials of the ambient power-series ring determine symmetric functions.

## Main results

* `SymmetricFunction.ext` identifies functions with equal coefficients.
* `SymmetricFunction.coeff_mul` computes multiplication coefficients.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommSemiring R]

/-- The coefficient of a monomial in a symmetric function. -/
def coeff (R : Type*) [CommSemiring R] (n : ℕ →₀ ℕ) : SymmetricFunction R →ₗ[R] R :=
  (MvPowerSeries.coeff n).comp (toPowerSeries R).toLinearMap

/-- The abstract coefficient agrees with the ambient power-series coefficient. -/
theorem coeff_apply (n : ℕ →₀ ℕ) (f : SymmetricFunction R) :
    coeff R n f = MvPowerSeries.coeff n (toPowerSeries R f) := rfl

/-- Symmetric functions with equal monomial coefficients are equal. -/
@[ext]
theorem ext {f g : SymmetricFunction R} (h : ∀ n, coeff R n f = coeff R n g) : f = g :=
  Subtype.ext (MvPowerSeries.ext h)

/-- Every coefficient of the zero function vanishes. -/
@[simp]
theorem coeff_zero (n : ℕ →₀ ℕ) : coeff R n 0 = 0 := map_zero _

/-- Coefficients add under addition. -/
@[simp]
theorem coeff_add (n : ℕ →₀ ℕ) (f g : SymmetricFunction R) :
    coeff R n (f + g) = coeff R n f + coeff R n g := map_add _ _ _

/-- Coefficients negate under negation. -/
@[simp]
theorem coeff_neg {R : Type*} [CommRing R] (n : ℕ →₀ ℕ) (f : SymmetricFunction R) :
    coeff R n (-f) = -coeff R n f := map_neg _ _

/-- Coefficients subtract under subtraction. -/
@[simp]
theorem coeff_sub {R : Type*} [CommRing R] (n : ℕ →₀ ℕ) (f g : SymmetricFunction R) :
    coeff R n (f - g) = coeff R n f - coeff R n g := map_sub _ _ _

/-- Coefficients commute with scalar multiplication. -/
theorem coeff_smul (n : ℕ →₀ ℕ) (r : R) (f : SymmetricFunction R) :
    coeff R n (r • f) = r • coeff R n f := map_smul _ _ _

/-- Multiplication coefficients are the finite convolution of exponent coefficients. -/
theorem coeff_mul (n : ℕ →₀ ℕ) (f g : SymmetricFunction R) :
    coeff R n (f * g) =
      ∑ p ∈ Finset.antidiagonal n, coeff R p.1 f * coeff R p.2 g :=
  MvPowerSeries.coeff_mul n f.val g.val

/-- The identity has only its constant coefficient. -/
@[simp]
theorem coeff_one (n : ℕ →₀ ℕ) :
    coeff R n 1 = if n = 0 then 1 else 0 := MvPowerSeries.coeff_one n

/-- An embedded scalar has only its constant coefficient. -/
@[simp]
theorem coeff_algebraMap (n : ℕ →₀ ℕ) (r : R) :
    coeff R n (algebraMap R (SymmetricFunction R) r) = if n = 0 then r else 0 :=
  MvPowerSeries.coeff_C n r

/-- A symmetric function is zero exactly when all its coefficients vanish. -/
theorem eq_zero_iff {f : SymmetricFunction R} : f = 0 ↔ ∀ n, coeff R n f = 0 := by
  constructor
  · rintro rfl n
    exact coeff_zero n
  · intro hf
    apply ext
    intro n
    rw [coeff_zero]
    exact hf n

end SymmetricFunction
