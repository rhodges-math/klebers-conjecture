import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Finite interpolation moments

Normalized powers of distinct nodes have the moments of the leading coefficient functional.
These moments give a unit upper triangular matrix for every finite alphabet.

These declarations extend Mathlib's algebra APIs.

## Main results

* `Lagrange.sum_pow_div_prod_sub` evaluates every moment below the number of nodes.
* `Lagrange.det_interpolation_moments` gives the determinant of the normalized moment matrix.
-/

noncomputable section

namespace Lagrange

variable {F ι : Type*} [Field F]

/-- Powers below the number of distinct nodes give the leading coefficient moments. -/
theorem sum_pow_div_prod_sub [DecidableEq ι] (s : Finset ι) (v : ι → F) (hv : Set.InjOn v s)
    (t : ℕ) (ht : t < s.card) :
    (∑ i ∈ s, v i ^ t / ∏ j ∈ s.erase i, (v i - v j)) =
      if t = s.card - 1 then 1 else 0 := by
  have hdeg : (Polynomial.X ^ t : Polynomial F).degree < s.card := by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast ht
  have h := coeff_eq_sum hv hdeg
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.coeff_X_pow,
    eq_comm] using h.symm

/-- A normalized finite moment below the matrix diagonal vanishes. -/
theorem interpolation_moment_below {N : ℕ} (x : Fin N → F)
    (hx : Function.Injective x) (i j : Fin N) (hji : j < i) :
    (∑ a : Fin N, x a ^ (N - 1 - i.val + j.val) /
      ∏ b ∈ Finset.univ.erase a, (x a - x b)) = 0 := by
  have ht : N - 1 - i.val + j.val < N := by omega
  have hne : N - 1 - i.val + j.val ≠ N - 1 := by omega
  have h := sum_pow_div_prod_sub Finset.univ x hx.injOn _ (by simpa using ht)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [ite_eq_right hne] at h
  exact h

/-- A normalized finite moment on the matrix diagonal is one. -/
theorem interpolation_moment_diag {N : ℕ} (x : Fin N → F)
    (hx : Function.Injective x) (i : Fin N) :
    (∑ a : Fin N, x a ^ (N - 1 - i.val + i.val) /
      ∏ b ∈ Finset.univ.erase a, (x a - x b)) = 1 := by
  have he : N - 1 - i.val + i.val = N - 1 := by omega
  have ht : N - 1 < N := by omega
  simpa only [Finset.card_univ, Fintype.card_fin, he, ite_true] using
    sum_pow_div_prod_sub Finset.univ x hx.injOn (N - 1) (by simpa using ht)

/-- The normalized moment matrix has determinant one, including for an empty alphabet. -/
theorem det_interpolation_moments {N : ℕ} (x : Fin N → F)
    (hx : Function.Injective x) :
    Matrix.det (Matrix.of fun i j : Fin N => ∑ a : Fin N,
      x a ^ (N - 1 - i.val + j.val) /
        ∏ b ∈ Finset.univ.erase a, (x a - x b)) = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp only [Matrix.of_apply, interpolation_moment_diag x hx, Finset.prod_const_one]
  · intro i j hji
    exact interpolation_moment_below x hx i j hji

end Lagrange
