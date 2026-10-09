import KlebersConjecture.SymmetricFunctions.SymplecticCharacters.Grading
import KlebersConjecture.SymmetricFunctions.Bases.SchurCoordinates
import KlebersConjecture.SymmetricFunctions.ForMathlib.DegreeLoweringBasis

/-!
# The symplectic universal-character basis

The universal characters differ from the Schur basis only in strictly smaller degrees.

## Main results

* `exists_symplecticCharacterBasis` gives a basis with the prescribed character vectors.
* `symplecticCharacterBasis_apply` identifies the vectors of the chosen basis.
-/

noncomputable section

namespace SymmetricFunction

/-- Symplectic universal characters form a basis over every commutative ring. -/
theorem exists_symplecticCharacterBasis (R : Type*) [CommRing R] :
    ∃ b : Module.Basis YoungDiagram R (SymmetricFunction R),
      ∀ μ, b μ = symplecticCharacter R μ := by
  apply Module.Basis.exists_basis_of_degree_lowering (schurBasis R) YoungDiagram.card
    (symplecticCharacter R)
  intro μ ν hμν
  rw [schurBasis_apply]
  by_cases he : μ.card = ν.card
  · have hz : homogeneousComponent R μ.card (symplecticCharacter R μ - schur R μ) = 0 := by
      rw [map_sub, homogeneousComponent_symplecticCharacter,
        homogeneousComponent_of_isHomogeneous (isHomogeneous_schur (R := R) μ)]
      simp
    have hc := schur_repr_homogeneousComponent μ.card
      (symplecticCharacter R μ - schur R μ) ν
    rw [hz, map_zero, Finsupp.zero_apply, ite_eq_left he.symm] at hc
    exact hc.symm
  · exact schur_repr_eq_zero_of_degreeBound (symplecticCharacter_sub_schur_mem μ) ν (by omega)

/-- The basis of integral symplectic universal characters. -/
def symplecticCharacterBasis (R : Type*) [CommRing R] :
    Module.Basis YoungDiagram R (SymmetricFunction R) :=
  (exists_symplecticCharacterBasis R).choose

/-- Every vector of the chosen universal-character basis is the corresponding character. -/
@[simp] theorem symplecticCharacterBasis_apply {R : Type*} [CommRing R] (μ : YoungDiagram) :
    symplecticCharacterBasis R μ = symplecticCharacter R μ :=
  (exists_symplecticCharacterBasis R).choose_spec μ

end SymmetricFunction
