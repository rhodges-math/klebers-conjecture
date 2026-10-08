import Schubert.SymmetricFunctions.JacobiTrudi.JacobiTrudiPadding
import Schubert.SymmetricFunctions.JacobiTrudi.FiniteJacobiTrudi

/-! # Stable Jacobi--Trudi identity

Finite Jacobi--Trudi identities and determinant padding identify stable Schur functions
with the determinant of complete functions at every size containing the diagram.

## Main definitions

* `jacobiTrudiMatrix` has any chosen size at least the diagram height.

## Main results

* `schur_eq_det_jacobiTrudiMatrix` gives the stable complete-function determinant formula.

## Implementation notes

The matrix uses zero-based rows and columns and integer complete-function indices.
Negative indices vanish, index zero is one, and any size at least the diagram height
gives the same determinant. Restriction uses the alphabet `Fin n` directly.

## References

* I. G. Macdonald, Symmetric Functions and Hall Polynomials, second edition,
  Chapter I, section 3, equation (3.4).
-/

noncomputable section

namespace SymmetricFunction

/-- A Schur function is its complete-function Jacobi--Trudi determinant at every padded size. -/
theorem schur_eq_det_jacobiTrudiMatrix (R : Type*) [CommRing R]
    (μ : YoungDiagram) (r : ℕ) (hμ : μ.colLen 0 ≤ r) :
    schur R μ = Matrix.det (jacobiTrudiMatrix R μ r) := by
  apply ext_restrict
  intro n
  let N := max n r
  have hr : r ≤ N := le_max_right n r
  have hn : n ≤ N := le_max_left n r
  have he : restrict R N (schur R μ) =
      restrict R N (Matrix.det (jacobiTrudiMatrix R μ N)) := by
    rw [restrict_schur_eq_diagramSchurPoly,
      FiniteAlphabet.diagramSchurPoly_eq_det_hsymm R N μ (hμ.trans hr),
      (restrict R N).map_det]
    congr 1
    apply Matrix.ext
    intro i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      restrict_jacobiTrudiMatrix_entry]
  rw [det_jacobiTrudiMatrix_padding μ hμ hr] at he
  have h := congrArg (MvPolynomial.killCompl (Fin.castLEEmb hn).injective) he
  simpa only [killCompl_restrict hn] using h

end SymmetricFunction
