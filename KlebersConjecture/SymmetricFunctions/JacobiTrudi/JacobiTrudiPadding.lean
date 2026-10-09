import KlebersConjecture.SymmetricFunctions.JacobiTrudi.JacobiTrudiMatrix

/-!
# Padding Jacobi--Trudi determinants

Every added row after the diagram's height is zero before its diagonal and one on the
diagonal. Enlarging a Jacobi--Trudi matrix beyond that height preserves its determinant.

## Main results

* `det_jacobiTrudiMatrix_padding` gives independence of the padded matrix size.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommRing R]

/-- Appending a padded row and column preserves a Jacobi--Trudi determinant. -/
theorem det_jacobiTrudiMatrix_succ (μ : YoungDiagram) (r : ℕ) (hμ : μ.colLen 0 ≤ r) :
    Matrix.det (jacobiTrudiMatrix R μ (r + 1)) = Matrix.det (jacobiTrudiMatrix R μ r) := by
  rw [Matrix.det_succ_row _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · have hd := jacobiTrudiMatrix_padding_diag (R := R) μ (r + 1) (Fin.last r) hμ
    have hs : (-1 : SymmetricFunction R) ^ (r + r) = 1 := by
      exact Even.neg_one_pow (α := SymmetricFunction R) (show Even (r + r) from ⟨r, rfl⟩)
    have he : (jacobiTrudiMatrix R μ (r + 1)).submatrix
        (Fin.last r).succAbove (Fin.last r).succAbove = jacobiTrudiMatrix R μ r := by
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_last, jacobiTrudiMatrix_apply,
        Fin.val_castSucc]
    rw [show (Fin.last r : Fin (r + 1)).val = r from rfl, hs, hd, one_mul, one_mul, he]
  · intro j _ hj
    have hjr : j.val < r := by
      have := j.isLt
      have hn : j.val ≠ r := fun h => hj (Fin.ext h)
      omega
    rw [jacobiTrudiMatrix_padding_zero μ hμ (Fin.last r) j le_rfl hjr, mul_zero, zero_mul]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- All matrix sizes containing the diagram have the same Jacobi--Trudi determinant. -/
theorem det_jacobiTrudiMatrix_padding (μ : YoungDiagram) {r s : ℕ}
    (hμ : μ.colLen 0 ≤ r) (hrs : r ≤ s) :
    Matrix.det (jacobiTrudiMatrix R μ s) = Matrix.det (jacobiTrudiMatrix R μ r) := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih =>
    rw [det_jacobiTrudiMatrix_succ μ s (hμ.trans hrs), ih]

end SymmetricFunction
