import KlebersConjecture.Paper.Products
import KlebersConjecture.Paper.RectangularIndependence
import KlebersConjecture.SymmetricFunctions.SymplecticCharacters.ProductComponents
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! # Top components of rectangular symplectic-character products

Every complementary pair has total size equal to the rectangle's area.
Its symplectic-character product has the corresponding Schur product in that degree.

## Main results

* `homogeneousComponent_symplecticPair` projects to the complementary Schur product.
* `symplectic_linearIndependent_of_schur` transfers rectangular Schur independence.
* `symplectic_linearIndependent` gives independence of complementary characters over every field.
-/

noncomputable section

namespace ComplementaryProducts

variable {R : Type*} [CommRing R]

/-- The area-degree component of a complementary character product is its Schur product. -/
theorem homogeneousComponent_symplecticPair (a b : ℕ) (p : complementaryPairs a b) :
    SymmetricFunction.homogeneousComponent R (a * b)
      (symplecticPairProduct R (p : Sym2 YoungDiagram)) =
        schurPairProduct R (p : Sym2 YoungDiagram) := by
  obtain ⟨μ, hμ, hp⟩ := (mem_complementaryPairs a b (p : Sym2 YoungDiagram)).mp p.property
  rw [hp, symplecticPairProduct_mk, schurPairProduct_mk,
    ← YoungDiagram.card_add_rectComplement hμ]
  exact SymmetricFunction.homogeneousComponent_symplectic_mul μ _

/-- Independence of complementary Schur products implies independence of character products. -/
theorem symplectic_linearIndependent_of_schur (a b : ℕ)
    (h : LinearIndependent R (fun p : complementaryPairs a b =>
      schurPairProduct R (p : Sym2 YoungDiagram))) :
    LinearIndependent R (fun p : complementaryPairs a b =>
      symplecticPairProduct R (p : Sym2 YoungDiagram)) := by
  apply LinearIndependent.of_comp (SymmetricFunction.homogeneousComponent R (a * b))
  have he : (SymmetricFunction.homogeneousComponent R (a * b) ∘
      (fun p : complementaryPairs a b => symplecticPairProduct R (p : Sym2 YoungDiagram))) =
        (fun p : complementaryPairs a b => schurPairProduct R (p : Sym2 YoungDiagram)) := by
    funext p
    exact homogeneousComponent_symplecticPair a b p
  rw [he]
  exact h

/-- Complementary symplectic universal-character products are independent over every field. -/
theorem symplectic_linearIndependent (F : Type*) [Field F] (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    LinearIndependent F (fun p : complementaryPairs a b =>
      symplecticPairProduct F (p : Sym2 YoungDiagram)) :=
  symplectic_linearIndependent_of_schur a b (kleber_linearIndependent F a b ha hb)

end ComplementaryProducts
