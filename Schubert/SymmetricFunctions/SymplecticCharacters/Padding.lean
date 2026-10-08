import Schubert.SymmetricFunctions.SymplecticCharacters.Basic

/-! # Padding symplectic character determinants

The lower padded rows have zero entries before their diagonal and one on the diagonal.
Every matrix size at least the diagram's height gives the same character.

## Main results

* `det_symplecticCharacterMatrix_padding` proves independence of the matrix size.
* `symplecticCharacter_eq_padded_det` identifies every padded determinant with the character.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommRing R]

/-- Appending a padded row and column preserves the symplectic determinant. -/
theorem det_symplecticCharacterMatrix_succ (μ : YoungDiagram) (r : ℕ)
    (hμ : μ.colLen 0 ≤ r) :
    Matrix.det (symplecticCharacterMatrix R μ (r + 1)) =
      Matrix.det (symplecticCharacterMatrix R μ r) := by
  rw [Matrix.det_succ_row _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · have hd := symplecticCharacter_padding_diag (R := R) μ (r + 1) (Fin.last r) hμ
    have hs : (-1 : SymmetricFunction R) ^ (r + r) = 1 :=
      Even.neg_one_pow (α := SymmetricFunction R) (show Even (r + r) from ⟨r, rfl⟩)
    have he : (symplecticCharacterMatrix R μ (r + 1)).submatrix
        (Fin.last r).succAbove (Fin.last r).succAbove = symplecticCharacterMatrix R μ r := by
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_last, symplecticCharacterMatrix_apply,
        Fin.val_castSucc]
    rw [show (Fin.last r : Fin (r + 1)).val = r from rfl, hs, hd, one_mul, one_mul, he]
  · intro j _ hj
    have hjr : j.val < r := by
      have := j.isLt
      have hn : j.val ≠ r := fun h => hj (Fin.ext h)
      omega
    rw [symplecticCharacter_padding_zero μ hμ (Fin.last r) j le_rfl hjr, mul_zero, zero_mul]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- All matrix sizes containing the diagram have the same symplectic determinant. -/
theorem det_symplecticCharacterMatrix_padding (μ : YoungDiagram) {r s : ℕ}
    (hμ : μ.colLen 0 ≤ r) (hrs : r ≤ s) :
    Matrix.det (symplecticCharacterMatrix R μ s) =
      Matrix.det (symplecticCharacterMatrix R μ r) := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih =>
    rw [det_symplecticCharacterMatrix_succ μ s (hμ.trans hrs), ih]

/-- A determinant at any size containing the diagram is its symplectic universal character. -/
theorem symplecticCharacter_eq_padded_det (μ : YoungDiagram) (r : ℕ)
    (hμ : μ.colLen 0 ≤ r) :
    symplecticCharacter R μ = Matrix.det (symplecticCharacterMatrix R μ r) := by
  change Matrix.det (symplecticCharacterMatrix R μ (μ.colLen 0)) = _
  exact (det_symplecticCharacterMatrix_padding μ le_rfl hμ).symm

end SymmetricFunction
