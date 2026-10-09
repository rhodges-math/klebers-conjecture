import KlebersConjecture.SymmetricFunctions.ForMathlib.InterpolationMoments

/-!
# Determinants of finite interpolation moments

Multiplying a power moment matrix by the descending Vandermonde determinant gives the
alternant determinant for its row exponents. The identity holds for the empty alphabet too.

These declarations extend Mathlib's algebra APIs.

## Main results

* `Lagrange.det_pow_moments_mul` expresses a moment determinant as an alternant quotient.
-/

noncomputable section

namespace Lagrange

variable {F : Type*} [Field F]

/-- A moment determinant times the staircase determinant equals the power alternant. -/
theorem det_pow_moments_mul {N : ℕ} (x : Fin N → F) (hx : Function.Injective x)
    (β : Fin N → ℕ) :
    Matrix.det (Matrix.of fun i j : Fin N => ∑ a : Fin N,
      x a ^ (β i + j.val) / ∏ b ∈ Finset.univ.erase a, (x a - x b)) *
        Matrix.det (Matrix.of fun i a : Fin N => x a ^ (N - 1 - i.val)) =
      Matrix.det (Matrix.of fun i a : Fin N => x a ^ β i) := by
  let A : Matrix (Fin N) (Fin N) F := Matrix.of fun i a => x a ^ β i
  let W : Matrix (Fin N) (Fin N) F := Matrix.of fun i a => x a ^ (N - 1 - i.val)
  let V : Matrix (Fin N) (Fin N) F := Matrix.of fun a j =>
    x a ^ j.val / ∏ b ∈ Finset.univ.erase a, (x a - x b)
  have hmul : (Matrix.of fun i j : Fin N => ∑ a : Fin N,
      x a ^ (β i + j.val) / ∏ b ∈ Finset.univ.erase a, (x a - x b)) = A * V := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, A, V, pow_add, mul_div_assoc]
  have hbase : Matrix.det (W * V) = 1 := by
    have he : W * V = Matrix.of fun i j : Fin N => ∑ a : Fin N,
        x a ^ (N - 1 - i.val + j.val) /
          ∏ b ∈ Finset.univ.erase a, (x a - x b) := by
      ext i j
      simp only [Matrix.mul_apply, W, V, Matrix.of_apply, pow_add, mul_div_assoc]
    rw [he]
    exact det_interpolation_moments x hx
  change _ * Matrix.det W = Matrix.det A
  rw [hmul, Matrix.det_mul]
  calc
    Matrix.det A * Matrix.det V * Matrix.det W =
        Matrix.det A * (Matrix.det W * Matrix.det V) := by ring
    _ = Matrix.det A * Matrix.det (W * V) := by rw [Matrix.det_mul]
    _ = Matrix.det A := by rw [hbase, mul_one]

end Lagrange
