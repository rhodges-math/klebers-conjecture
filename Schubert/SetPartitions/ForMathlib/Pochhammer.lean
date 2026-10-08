import Mathlib.RingTheory.Polynomial.Pochhammer

/-! # Linear coefficients of falling factorial polynomials

The coefficient of degree one in a nonconstant falling factorial polynomial is a signed
factorial. The formula holds over every commutative ring.

These declarations extend Mathlib's algebra APIs.

## Main results

* `Polynomial.coeff_one_descPochhammer_succ` gives the linear coefficient for degree `n + 1`.
* `Polynomial.coeff_one_descPochhammer` gives the formula for any positive degree.
-/

namespace Polynomial

variable (R : Type*) [CommRing R]

/-- The linear coefficient of the falling factorial of degree `n + 1` is `(-1)^n n!`. -/
theorem coeff_one_descPochhammer_succ (n : ℕ) :
    (descPochhammer R (n + 1)).coeff 1 = (-1 : R) ^ n * (n.factorial : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : (descPochhammer R (n + 1)).coeff 0 = 0 := by
      rw [coeff_zero_eq_eval_zero,
        descPochhammer_ne_zero_eval_zero R (Nat.succ_ne_zero n)]
    rw [descPochhammer_succ_right, mul_sub, coeff_sub, coeff_mul_X,
      ← C_eq_natCast, coeff_mul_C, hz, ih, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    ring

/-- The linear coefficient of a positive-degree falling factorial is a signed factorial. -/
theorem coeff_one_descPochhammer (k : ℕ) (hk : 0 < k) :
    (descPochhammer R k).coeff 1 = (-1 : R) ^ (k - 1) * ((k - 1).factorial : R) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hk)
  simpa only [Nat.succ_sub_one] using coeff_one_descPochhammer_succ R n

end Polynomial
