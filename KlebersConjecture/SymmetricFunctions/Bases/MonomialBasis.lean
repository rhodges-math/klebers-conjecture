import KlebersConjecture.SymmetricFunctions.Families.Monomial
import KlebersConjecture.Partitions.Bounds
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # The monomial basis of symmetric functions

Coefficients at canonical row exponents give finitely supported coordinates indexed by
Young diagrams. These coordinates identify symmetric functions with finite linear combinations
of monomial symmetric functions.

## Main results

* `SymmetricFunction.monomialCoordinateEquiv` identifies finite monomial coordinates.
* `SymmetricFunction.monomialBasis` is the standard basis indexed by Young diagrams.
* `SymmetricFunction.exists_monomialBasis` gives its vectors and coefficient coordinates.
## Implementation notes

The natural and integer scalar actions are unique. Their freeness instances specialize the
monomial basis to those standard actions, alongside the general coefficient-semiring instance.
Only freeness proofs are registered; no additional module or algebra structure is introduced.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommSemiring R]

/-- The nonzero coefficients at canonical row exponents form a finite set. -/
theorem finite_rowCoeff_support (f : SymmetricFunction R) :
    (Function.support (fun μ : YoungDiagram => coeff R (rowExponent μ) f)).Finite := by
  obtain ⟨D, hD⟩ := exists_mem_degreeFiltration f
  refine (YoungDiagram.finite_card_le D).subset ?_
  intro μ hμ
  by_contra h
  apply hμ
  exact hD (rowExponent μ) (by simpa only [degree_rowExponent] using Nat.lt_of_not_le h)

/-- Coordinates of a symmetric function at the canonical row exponents. -/
def monomialCoordinates (R : Type*) [CommSemiring R] :
    SymmetricFunction R →ₗ[R] (YoungDiagram →₀ R) where
  toFun f := Finsupp.ofSupportFinite (fun μ => coeff R (rowExponent μ) f)
    (finite_rowCoeff_support f)
  map_add' f g := by
    ext μ
    exact coeff_add _ f g
  map_smul' r f := by
    ext μ
    exact coeff_smul _ r f

/-- Monomial coordinates are the coefficients at canonical row exponents. -/
@[simp]
theorem monomialCoordinates_apply (f : SymmetricFunction R) (μ : YoungDiagram) :
    monomialCoordinates R f μ = coeff R (rowExponent μ) f := rfl

/-- The coordinate vector of a monomial symmetric function is a single basis coordinate. -/
@[simp]
theorem monomialCoordinates_monomial (μ : YoungDiagram) :
    monomialCoordinates R (monomial R μ) = Finsupp.single μ 1 := by
  classical
  ext ν
  rw [monomialCoordinates_apply, coeff_monomial_rowExponent, Finsupp.single_apply]
  simp only [eq_comm]

/-- Monomial coordinates determine a symmetric function. -/
theorem monomialCoordinates_injective : Function.Injective (monomialCoordinates R) := by
  intro f g h
  apply ext
  intro d
  rw [coeff_eq_rowExponent d f, coeff_eq_rowExponent d g]
  exact DFunLike.congr_fun h (exponentDiagram d)

/-- Taking coordinates reverses a finite linear combination of monomial functions. -/
theorem coordinates_linearCombination (c : YoungDiagram →₀ R) :
    monomialCoordinates R (Finsupp.linearCombination R (monomial R) c) = c := by
  rw [Finsupp.apply_linearCombination]
  simp only [Function.comp_def, monomialCoordinates_monomial]
  rw [Finsupp.linearCombination_apply]
  simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using c.sum_single

/-- Every finitely supported coordinate vector comes from a symmetric function. -/
theorem monomialCoordinates_surjective : Function.Surjective (monomialCoordinates R) :=
  fun c => ⟨Finsupp.linearCombination R (monomial R) c, coordinates_linearCombination c⟩

/-- Canonical coefficients identify symmetric functions with finitely supported coordinates. -/
def monomialCoordinateEquiv (R : Type*) [CommSemiring R] :
    SymmetricFunction R ≃ₗ[R] (YoungDiagram →₀ R) :=
  LinearEquiv.ofBijective (monomialCoordinates R)
    ⟨monomialCoordinates_injective, monomialCoordinates_surjective⟩

/-- The coordinate equivalence evaluates at canonical row-exponent coefficients. -/
theorem monomialCoordinateEquiv_apply (f : SymmetricFunction R) (μ : YoungDiagram) :
    monomialCoordinateEquiv R f μ = coeff R (rowExponent μ) f := rfl

/-- Inverse coordinates form the corresponding finite linear combination of monomials. -/
theorem monomialCoordinateEquiv_symm (c : YoungDiagram →₀ R) :
    (monomialCoordinateEquiv R).symm c = Finsupp.linearCombination R (monomial R) c := by
  apply monomialCoordinates_injective
  rw [coordinates_linearCombination]
  exact (monomialCoordinateEquiv R).apply_symm_apply c

/-- The coefficient of inverse coordinates is the coordinate of the exponent diagram. -/
theorem coeff_monomialCoordinate_symm (c : YoungDiagram →₀ R) (d : ℕ →₀ ℕ) :
    coeff R d ((monomialCoordinateEquiv R).symm c) = c (exponentDiagram d) := by
  rw [coeff_eq_rowExponent]
  exact DFunLike.congr_fun ((monomialCoordinateEquiv R).apply_symm_apply c) (exponentDiagram d)

/-- Every symmetric function is reconstructed by its finite monomial coordinates. -/
theorem linearCombination_coordinates (f : SymmetricFunction R) :
    Finsupp.linearCombination R (monomial R) (monomialCoordinates R f) = f := by
  apply monomialCoordinates_injective
  exact coordinates_linearCombination _

/-- The monomial symmetric functions form a basis indexed by Young diagrams. -/
def monomialBasis (R : Type*) [CommSemiring R] :
    Module.Basis YoungDiagram R (SymmetricFunction R) :=
  .ofRepr (monomialCoordinateEquiv R)

/-- The basis coordinates are the canonical row-exponent coefficients. -/
@[simp]
theorem monomialBasis_repr_apply (f : SymmetricFunction R) (μ : YoungDiagram) :
    (monomialBasis R).repr f μ = coeff R (rowExponent μ) f := rfl

/-- The vector of the monomial basis is the monomial symmetric function of its diagram. -/
@[simp]
theorem monomialBasis_apply (μ : YoungDiagram) : monomialBasis R μ = monomial R μ := by
  apply monomialCoordinates_injective
  rw [monomialCoordinates_monomial]
  change (monomialBasis R).repr (monomialBasis R μ) = Finsupp.single μ 1
  exact Module.Basis.repr_self _ μ

/-- There is a monomial basis with canonical row-exponent coefficient coordinates. -/
theorem exists_monomialBasis (R : Type*) [CommSemiring R] :
    ∃ b : Module.Basis YoungDiagram R (SymmetricFunction R),
      (∀ μ, b μ = monomial R μ) ∧
      (∀ f μ, b.repr f μ = coeff R (rowExponent μ) f) :=
  ⟨monomialBasis R, monomialBasis_apply, monomialBasis_repr_apply⟩

/-- Symmetric functions form a free module over their coefficient semiring. -/
instance moduleFree : Module.Free R (SymmetricFunction R) :=
  Module.Free.of_basis (monomialBasis R)

/-- The canonical natural-scalar module is free with the same monomial basis. -/
instance natModuleFree : Module.Free ℕ (SymmetricFunction ℕ) :=
  Module.Free.of_basis (monomialBasis ℕ)

/-- The canonical integer-scalar module is free with the same monomial basis. -/
instance intModuleFree : Module.Free ℤ (SymmetricFunction ℤ) :=
  Module.Free.of_basis (monomialBasis ℤ)

/-- Monomial coordinates commute with a map of coefficient semirings. -/
theorem monomialBasis_repr_map {S : Type*} [CommSemiring S] (φ : R →+* S)
    (f : SymmetricFunction R) :
    (monomialBasis S).repr (map φ f) = ((monomialBasis R).repr f).mapRange φ φ.map_zero := by
  ext μ
  rw [monomialBasis_repr_apply, coeff_map, Finsupp.mapRange_apply, monomialBasis_repr_apply]

end SymmetricFunction
