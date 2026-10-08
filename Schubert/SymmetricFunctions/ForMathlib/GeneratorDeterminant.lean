import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinants omitting a polynomial generator

The determinant of a matrix whose entries omit a variable also omits that variable.

These declarations extend Mathlib's algebra APIs.

## Main results

* `MvPolynomial.degreeOf_det_eq_zero` preserves distinguished-variable degree zero.
-/

noncomputable section

namespace MvPolynomial

/-- A determinant has degree zero in a variable omitted by every entry. -/
theorem degreeOf_det_eq_zero {R σ ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (a : σ) (A : Matrix ι ι (MvPolynomial σ R))
    (h : ∀ i j, (A i j).degreeOf a = 0) : (Matrix.det A).degreeOf a = 0 := by
  classical
  let S := supported R {b : σ | b ≠ a}
  have hm (i j : ι) : A i j ∈ S := by
    rw [mem_supported]
    intro b hb hba
    subst b
    exact (mem_vars_iff_degreeOf_ne_zero.mp hb) (h i j)
  let B : Matrix ι ι S := fun i j => ⟨A i j, hm i j⟩
  have hd : Matrix.det A ∈ S := by
    have he := S.val.map_det B
    have hA : S.val.mapMatrix B = A := by
      ext i j
      rfl
    rw [hA] at he
    exact he ▸ (Matrix.det B).property
  have hs := mem_supported.mp hd
  by_contra hn
  exact hs (mem_vars_iff_degreeOf_ne_zero.mpr hn) rfl

end MvPolynomial
