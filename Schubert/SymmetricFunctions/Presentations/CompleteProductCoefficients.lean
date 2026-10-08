import Schubert.SymmetricFunctions.Presentations.CompleteCalculus
import Schubert.SymmetricFunctions.Presentations.SchurCompleteCalculus
import Schubert.SymmetricFunctions.ForMathlib.VariableProducts

/-! # Highest complete-generator coefficients of products

Degree bounds in one generator identify the coefficient at the sum of the bounds.
The identities use no cancellation or nonzero coefficient-ring assumption.

## Main results

* `completeCoeff_mul_at_degrees` multiplies the coefficients at the degree bounds.
* `completeCoeff_pow_at_degree` extracts the coefficient of a bounded-degree power.
* `completeCoeff_schur_sq` extracts the corner-deleted Schur square.
* `completeCoeff_schur_mul_below` vanishes above both factors' complete indices.
-/

noncomputable section


namespace SymmetricFunction

variable {R : Type*} [CommRing R]

/-- Complete-generator coefficients at the sum of degree bounds multiply. -/
theorem completeCoeff_mul_at_degrees (a : ℕ+) (f g : SymmetricFunction R) (n m : ℕ)
    (hf : completeDegree R a f ≤ n)
    (hg : completeDegree R a g ≤ m) :
    completeCoeff R a (n + m) (f * g) = completeCoeff R a n f * completeCoeff R a m g := by
  simp only [completeCoeff_apply, map_mul]
  rw [MvPolynomial.variableCoeff_mul_at_degrees a _ _ n m hf hg, map_mul]

/-- The complete-generator coefficient at a power's degree bound is the power of the coefficient. -/
theorem completeCoeff_pow_at_degree (a : ℕ+) (f : SymmetricFunction R) (n m : ℕ)
    (hf : completeDegree R a f ≤ n) :
    completeCoeff R a (m * n) (f ^ m) = completeCoeff R a n f ^ m := by
  simp only [completeCoeff_apply, map_pow]
  rw [MvPolynomial.variableCoeff_pow_at_degree a _ n m hf, map_pow]

/-- The highest complete-generator coefficient of a Schur square is the corner-deleted square. -/
theorem completeCoeff_schur_sq (τ : YoungDiagram) (hτ : τ ≠ ⊥) (n : ℕ+)
    (hn : n.val = τ.rowLen 0 + τ.colLen 0 - 1) :
    completeCoeff R n 2 (schur R τ ^ 2) = schur R τ.removeFirstRowCol ^ 2 := by
  have hd := degreeOf_schur_le_one (R := R) τ hτ n hn
  have he := completeCoeff_pow_at_degree n (schur R τ) 1 2 hd
  simp only [mul_one, completeCoeff_schur τ hτ n hn] at he
  rw [he, smul_pow, ← pow_mul]
  rw [Even.neg_one_pow (show Even ((τ.colLen 0 - 1) * 2) from
    ⟨τ.colLen 0 - 1, by omega⟩), one_smul]

/-- A product of Schur functions below a complete index has zero positive coefficients there. -/
theorem completeCoeff_schur_mul_below (α β : YoungDiagram) (n : ℕ+)
    (hα : α.rowLen 0 + α.colLen 0 - 1 < n.val)
    (hβ : β.rowLen 0 + β.colLen 0 - 1 < n.val) (j : ℕ) (hj : 0 < j) :
    completeCoeff R n j (schur R α * schur R β) = 0 := by
  apply completeCoeff_pos_of_degreeOf_eq_zero n _ _ hj
  change ((completePresentation R).symm (schur R α * schur R β)).degreeOf n = 0
  rw [map_mul]
  have hd := MvPolynomial.degreeOf_mul_le n
    ((completePresentation R).symm (schur R α))
    ((completePresentation R).symm (schur R β))
  rw [degreeOf_schur_above α n hα, degreeOf_schur_above β n hβ, zero_add] at hd
  exact Nat.le_zero.mp hd

end SymmetricFunction
