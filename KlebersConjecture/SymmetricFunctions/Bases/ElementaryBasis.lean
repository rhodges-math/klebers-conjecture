import KlebersConjecture.SymmetricFunctions.Bases.ProductBasis
import KlebersConjecture.SymmetricFunctions.Presentations.ElementaryPresentation

/-! # The elementary symmetric-function basis

## Main results

* `elementaryBasis_apply` identifies basis vectors with elementary row products.
-/

noncomputable section

namespace SymmetricFunction

/-- The elementary products form a basis of the symmetric-function algebra. -/
def elementaryBasis (R : Type*) [CommRing R] :
    Module.Basis YoungDiagram R (SymmetricFunction R) :=
  rowProductBasis R (elementaryPresentation R)

/-- An elementary basis vector is the product of the elementary functions at its row lengths. -/
theorem elementaryBasis_apply (R : Type*) [CommRing R] (μ : YoungDiagram) :
    elementaryBasis R μ = elementaryProd R μ := by
  rw [elementaryBasis, rowProductBasis_apply R _ _ (elementaryPresentation_apply_X R),
    elementaryProd]
  exact congrArg List.prod
    (List.attach_map_val (l := μ.rowLens) (f := fun k : ℕ => elementary R k))

end SymmetricFunction
