import KlebersConjecture.SymmetricFunctions.Families.Families
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Jacobi--Trudi matrices of complete symmetric functions

The integer index convention makes entries below a padded row vanish automatically.

## Main definitions

* `jacobiTrudiMatrix` uses integer complete-function indices at a chosen matrix size.

## Main results

* `jacobiTrudiMatrix_padding`: enlarging the matrix preserves its leading submatrix.
* `jacobiTrudiMatrix_padding_zero`: the lower left padding block vanishes.
* `jacobiTrudiMatrix_padding_diag`: padded diagonal entries are one.

## Implementation notes

Rows and columns start at zero. Integer complete indices make every entry total;
negative indices give zero and index zero gives one.

## References

* I. G. Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, section 3.
-/

noncomputable section

namespace SymmetricFunction

/-- The Jacobi--Trudi matrix with integer complete-function indices and a chosen size. -/
def jacobiTrudiMatrix (R : Type*) [CommRing R] (μ : YoungDiagram) (r : ℕ) :
    Matrix (Fin r) (Fin r) (SymmetricFunction R) :=
  Matrix.of fun i j => complete R ((μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ))

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The entries use row length minus row index plus column index. -/
theorem jacobiTrudiMatrix_apply (μ : YoungDiagram) (r : ℕ) (i j : Fin r) :
    jacobiTrudiMatrix R μ r i j =
      complete R ((μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ)) := rfl

/-- An entry with negative complete-function index vanishes. -/
theorem jacobiTrudiMatrix_entry_zero (μ : YoungDiagram) (r : ℕ) (i j : Fin r)
    (h : μ.rowLen i.val + j.val < i.val) : jacobiTrudiMatrix R μ r i j = 0 := by
  apply complete_neg
  omega

/-- The diagonal entry is the complete function of the corresponding row length. -/
theorem jacobiTrudiMatrix_diag (μ : YoungDiagram) (r : ℕ) (i : Fin r) :
    jacobiTrudiMatrix R μ r i i = complete R (μ.rowLen i.val : ℤ) := by
  rw [jacobiTrudiMatrix_apply]
  congr 1
  omega

/-- Coefficient-ring homomorphisms act entrywise on a Jacobi--Trudi matrix. -/
theorem map_jacobiTrudiMatrix (φ : R →+* S) (μ : YoungDiagram) (r : ℕ) :
    (jacobiTrudiMatrix R μ r).map (map φ) = jacobiTrudiMatrix S μ r := by
  apply Matrix.ext
  intro i j
  exact map_complete φ _

/-- Finite restriction of an entry respects the signed complete-function convention. -/
theorem restrict_jacobiTrudiMatrix_entry (N : ℕ) (μ : YoungDiagram) (r : ℕ) (i j : Fin r) :
    restrict R N (jacobiTrudiMatrix R μ r i j) =
      if 0 ≤ (μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ) then
        MvPolynomial.hsymm (Fin N) R
          (((μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ)).toNat) else 0 :=
  restrict_complete N _

/-- Padding preserves the leading square submatrix. -/
theorem jacobiTrudiMatrix_padding (μ : YoungDiagram) {r s : ℕ} (h : r ≤ s) :
    (jacobiTrudiMatrix R μ s).submatrix (Fin.castLE h) (Fin.castLE h) =
      jacobiTrudiMatrix R μ r := rfl

/-- Rows after the diagram have complete-function index column minus row. -/
theorem jacobiTrudiMatrix_padded_row (μ : YoungDiagram) (r : ℕ) (i j : Fin r)
    (hi : μ.colLen 0 ≤ i.val) :
    jacobiTrudiMatrix R μ r i j = complete R ((j.val : ℤ) - (i.val : ℤ)) := by
  rw [jacobiTrudiMatrix_apply, YoungDiagram.rowLen_eq_zero_of_colLen_le hi]
  congr 1
  omega

/-- Below a size containing the diagram, the lower left padding block is zero. -/
theorem jacobiTrudiMatrix_padding_zero (μ : YoungDiagram) {r s : ℕ}
    (hμ : μ.colLen 0 ≤ r) (i j : Fin s) (hi : r ≤ i.val) (hj : j.val < r) :
    jacobiTrudiMatrix R μ s i j = 0 := by
  rw [jacobiTrudiMatrix_padded_row μ s i j (hμ.trans hi)]
  apply complete_neg
  omega

/-- Every padded diagonal entry is the multiplicative identity. -/
theorem jacobiTrudiMatrix_padding_diag (μ : YoungDiagram) (r : ℕ) (i : Fin r)
    (hi : μ.colLen 0 ≤ i.val) : jacobiTrudiMatrix R μ r i i = 1 := by
  rw [jacobiTrudiMatrix_diag, YoungDiagram.rowLen_eq_zero_of_colLen_le hi]
  exact complete_zero

/-- The determinant of the matrix of size zero is one. -/
theorem det_jacobiTrudiMatrix_zero (μ : YoungDiagram) :
    (jacobiTrudiMatrix R μ 0).det = 1 := Matrix.det_isEmpty

end SymmetricFunction
