import Schubert.SymmetricFunctions.Families.Families
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Symplectic universal characters

The integral symplectic determinant has a single complete function in its first column
and the sum of two complete functions in subsequent columns.

## Main definitions

* `symplecticCharacterMatrix` is the integral complete-function matrix.
* `symplecticCharacter` is its determinant at the diagram height.

## Main results

* `symplecticCharacter_bot` gives the empty-diagram character.
* `symplecticCharacter_height_one` identifies characters of height one.
* `map_symplecticCharacter` gives compatibility with coefficient-ring homomorphisms.
* `symplecticCharacter_eq_det` gives the integral symplectic determinant formula.

## Implementation notes

Rows and columns are zero based. The first column contains `h_(lambda_i - i)` once;
later columns contain `h_(lambda_i - i + j) + h_(lambda_i - i - j)`.
Complete functions have integer indices and vanish at negative indices. An undoubled
first column gives an integral determinant, valid without dividing by two.
The empty diagram has determinant one, and enlarging the matrix preserves its determinant.

## References

* K. Koike and I. Terada, Young-diagrammatic methods for the representation theory of the
  classical groups of type B_n, C_n, D_n, Journal of Algebra 107 (1987), 466-511,
  Definition 2.1.1 (the symplectic universal character).
* S. Okada, Intermediate symplectic characters and shifted plane partitions of shifted
  double staircase shape, Combinatorial Theory 1 (2021), #10, following equation (2.12)
  (the integral determinant with an undoubled first column).
* S. Gao, G. Orelowitz and A. Yong, Newell–Littlewood numbers, Transactions of the American
  Mathematical Society 374 (2021), 6331–6366, Section 2.3 (the same determinant, as the
  universal character basis of the Newell–Littlewood numbers).
-/

noncomputable section

namespace SymmetricFunction

/-- The integral symplectic character matrix with a chosen number of rows and columns. -/
def symplecticCharacterMatrix (R : Type*) [CommRing R] (μ : YoungDiagram) (r : ℕ) :
    Matrix (Fin r) (Fin r) (SymmetricFunction R) :=
  Matrix.of fun i j => complete R ((μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ)) +
    if j.val = 0 then 0 else
      complete R ((μ.rowLen i.val : ℤ) - (i.val : ℤ) - (j.val : ℤ))

/-- The symplectic universal character is the integral determinant of size the height. -/
def symplecticCharacter (R : Type*) [CommRing R] (μ : YoungDiagram) : SymmetricFunction R :=
  Matrix.det (symplecticCharacterMatrix R μ (μ.colLen 0))

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The integral symplectic determinant has an undoubled first column. -/
theorem symplecticCharacter_eq_det (μ : YoungDiagram) :
    symplecticCharacter R μ = Matrix.det (Matrix.of fun i j : Fin (μ.colLen 0) =>
      complete R ((μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ)) +
        if j.val = 0 then 0 else
          complete R ((μ.rowLen i.val : ℤ) - (i.val : ℤ) - (j.val : ℤ))) := rfl

/-- The first column has one complete function and other columns have two. -/
theorem symplecticCharacterMatrix_apply (μ : YoungDiagram) (r : ℕ) (i j : Fin r) :
    symplecticCharacterMatrix R μ r i j =
      complete R ((μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ)) +
        if j.val = 0 then 0 else
          complete R ((μ.rowLen i.val : ℤ) - (i.val : ℤ) - (j.val : ℤ)) := rfl

/-- The first column has complete-function index row length minus row index. -/
theorem symplecticCharacterMatrix_first (μ : YoungDiagram) (r : ℕ) (i j : Fin r)
    (hj : j.val = 0) : symplecticCharacterMatrix R μ r i j =
      complete R ((μ.rowLen i.val : ℤ) - (i.val : ℤ)) := by
  rw [symplecticCharacterMatrix_apply, hj]
  simp only [Nat.cast_zero, add_zero, ite_true]

/-- Enlarging the symplectic matrix preserves its leading square submatrix. -/
theorem symplecticCharacterMatrix_padding (μ : YoungDiagram) {r s : ℕ} (h : r ≤ s) :
    (symplecticCharacterMatrix R μ s).submatrix (Fin.castLE h) (Fin.castLE h) =
      symplecticCharacterMatrix R μ r := rfl

/-- The lower left block after the diagram's height vanishes. -/
theorem symplecticCharacter_padding_zero (μ : YoungDiagram) {r s : ℕ}
    (hμ : μ.colLen 0 ≤ r) (i j : Fin s) (hi : r ≤ i.val) (hj : j.val < r) :
    symplecticCharacterMatrix R μ s i j = 0 := by
  rw [symplecticCharacterMatrix_apply, YoungDiagram.rowLen_eq_zero_of_colLen_le (hμ.trans hi)]
  have hmain : complete R ((0 : ℕ) - (i.val : ℤ) + (j.val : ℤ)) = 0 := by
    apply complete_neg
    omega
  rw [hmain, zero_add]
  split_ifs with hjzero
  · rfl
  · apply complete_neg
    omega

/-- Every padded diagonal entry is one. -/
theorem symplecticCharacter_padding_diag (μ : YoungDiagram) (r : ℕ) (i : Fin r)
    (hi : μ.colLen 0 ≤ i.val) : symplecticCharacterMatrix R μ r i i = 1 := by
  rw [symplecticCharacterMatrix_apply, YoungDiagram.rowLen_eq_zero_of_colLen_le hi]
  have he : ((0 : ℕ) : ℤ) - (i.val : ℤ) + (i.val : ℤ) = 0 := by omega
  rw [he, complete_zero]
  split_ifs with hizero
  · exact add_zero _
  · have hz : complete R (((0 : ℕ) : ℤ) - (i.val : ℤ) - (i.val : ℤ)) = 0 := by
      apply complete_neg
      omega
    rw [hz, add_zero]

/-- Changing coefficient rings acts entrywise on the symplectic character matrix. -/
theorem map_symplecticCharacterMatrix (φ : R →+* S) (μ : YoungDiagram) (r : ℕ) :
    (symplecticCharacterMatrix R μ r).map (map φ) = symplecticCharacterMatrix S μ r := by
  ext i j
  simp only [Matrix.map_apply, symplecticCharacterMatrix_apply, map_add]
  split_ifs <;> simp only [map_complete, map_zero]

/-- The character of the empty diagram is one. -/
@[simp] theorem symplecticCharacter_bot : symplecticCharacter R ⊥ = 1 := by
  unfold symplecticCharacter
  rw [YoungDiagram.colLen_bot]
  exact Matrix.det_isEmpty

/-- A character of height one is the complete function of its row length. -/
theorem symplecticCharacter_height_one (μ : YoungDiagram) (hμ : μ.colLen 0 = 1) :
    symplecticCharacter R μ = complete R (μ.rowLen 0 : ℤ) := by
  unfold symplecticCharacter
  rw [hμ, Matrix.det_fin_one, symplecticCharacterMatrix_first μ 1 0 0 rfl]
  simp only [Fin.val_zero, Nat.cast_zero, sub_zero]

/-- Coefficient-ring homomorphisms preserve symplectic universal characters. -/
theorem map_symplecticCharacter (φ : R →+* S) (μ : YoungDiagram) :
    map φ (symplecticCharacter R μ) = symplecticCharacter S μ := by
  unfold symplecticCharacter
  rw [(map φ).map_det]
  change Matrix.det ((symplecticCharacterMatrix R μ (μ.colLen 0)).map (map φ)) = _
  rw [map_symplecticCharacterMatrix]

end SymmetricFunction
