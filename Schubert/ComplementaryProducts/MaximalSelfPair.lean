import Schubert.SymmetricFunctions.Presentations.CompleteProductCoefficients
import Schubert.SymmetricFunctions.LittlewoodRichardson.HighestWeight

/-! # A maximal Schur self-pair

The coefficient of the square of the maximal complete generator isolates a self-pair.
The corner-deleted Schur square has a unit Schur coefficient over every commutative ring.

## Main results

* `coeff_eq_zero_of_maximal_self_pair` isolates the scalar of a maximal Schur square.
-/

noncomputable section

namespace ComplementaryProducts

open SymmetricFunction

/-- A Schur square has zero scalar in a relation whose remaining factors have smaller hooks. -/
theorem coeff_eq_zero_of_maximal_self_pair (R : Type*) [CommRing R]
    (τ : YoungDiagram) (hτ : τ ≠ ⊥) (u : ℕ) (c : R) (d : Fin u → R)
    (α β : Fin u → YoungDiagram)
    (hα : ∀ i, α i = ⊥ ∨ (α i).rowLen 0 + (α i).colLen 0 - 1 <
      τ.rowLen 0 + τ.colLen 0 - 1)
    (hβ : ∀ i, β i = ⊥ ∨ (β i).rowLen 0 + (β i).colLen 0 - 1 <
      τ.rowLen 0 + τ.colLen 0 - 1)
    (hrel : c • schur R τ ^ 2 +
      ∑ i : Fin u, d i • (schur R (α i) * schur R (β i)) = 0) : c = 0 := by
  classical
  have hrow : 0 < τ.rowLen 0 :=
    Nat.pos_of_ne_zero ((YoungDiagram.eq_bot_iff_rowLen_zero τ).not.mp hτ)
  have hheight : 0 < τ.colLen 0 :=
    Nat.pos_of_ne_zero ((YoungDiagram.eq_bot_iff_colLen_zero τ).not.mp hτ)
  let n : ℕ+ := ⟨τ.rowLen 0 + τ.colLen 0 - 1, by omega⟩
  have hsmall (γ : YoungDiagram)
      (hγ : γ = ⊥ ∨ γ.rowLen 0 + γ.colLen 0 - 1 < τ.rowLen 0 + τ.colLen 0 - 1) :
      γ.rowLen 0 + γ.colLen 0 - 1 < n.val := by
    rcases hγ with rfl | hγ
    · simp only [YoungDiagram.rowLen_bot, YoungDiagram.colLen_bot, zero_add, Nat.zero_sub]
      exact n.pos
    · exact hγ
  have hv (i : Fin u) : completeCoeff R n 2 (schur R (α i) * schur R (β i)) = 0 :=
    completeCoeff_schur_mul_below (α i) (β i) n
      (hsmall (α i) (hα i)) (hsmall (β i) (hβ i)) 2 (by omega)
  have hcoeff := congrArg (completeCoeff R n 2) hrel
  rw [map_add, map_smul, completeCoeff_schur_sq τ hτ n rfl, map_sum, map_zero] at hcoeff
  simp only [map_smul, hv, smul_zero, Finset.sum_const_zero, add_zero] at hcoeff
  have he := congrArg (fun f =>
    (schurBasis R).repr f (τ.removeFirstRowCol + τ.removeFirstRowCol)) hcoeff
  simp only [map_smul, Finsupp.smul_apply, map_zero, Finsupp.zero_apply] at he
  rw [pow_two, schurBasis_repr_schur_mul_schur R, lrCoeff_add_eq_one, Nat.cast_one,
    smul_eq_mul, mul_one] at he
  exact he

end ComplementaryProducts
