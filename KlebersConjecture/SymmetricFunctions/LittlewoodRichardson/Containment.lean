import KlebersConjecture.SymmetricFunctions.LittlewoodRichardson.HighestWeight
import KlebersConjecture.SymmetricFunctions.Bases.SchurCoordinates

/-! # Containment from nonzero Littlewood–Richardson coefficients

A tableau counted by a nonzero coefficient has nonnegative content in each coordinate.
Its weight equation therefore places the initial diagram inside the final diagram.

## Main results

* `le_of_lrCoeff_ne_zero` gives containment from a nonzero coefficient.
* `lrCoeff_eq_zero_of_not_le` gives vanishing when containment fails.
* `card_eq_of_lrCoeff_ne_zero` gives size conservation.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction

open FiniteAlphabet.LittlewoodRichardson SemistandardYoungTableau

/-- A nonzero Littlewood–Richardson coefficient forces containment of the first diagram. -/
theorem le_of_lrCoeff_ne_zero (α β ν : YoungDiagram) (h : lrCoeff α β ν ≠ 0) : α ≤ ν := by
  classical
  obtain ⟨n, hα, hν, hf⟩ := exists_lr_alphabet_bound α β ν
  rw [lrCoeff_eq_tableau_count α β ν n hα hν hf] at h
  obtain ⟨T, hT⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  have hw := (Finset.mem_filter.mp hT).2.2
  apply YoungDiagram.le_of_forall_rowLen_le
  intro i
  by_cases hi : i < n
  · have he := congrFun hw ⟨i, hi⟩
    change (α.rowLen i : ℤ) + (content T.1 i : ℤ) = (ν.rowLen i : ℤ) at he
    omega
  · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (hα.trans (Nat.not_lt.mp hi))]
    exact Nat.zero_le _

/-- A nonzero Littlewood--Richardson coefficient preserves the total number of cells. -/
theorem card_eq_of_lrCoeff_ne_zero (α β ν : YoungDiagram)
    (h : lrCoeff α β ν ≠ 0) : ν.card = α.card + β.card := by
  by_contra hcard
  have hh : IsHomogeneous (schur ℤ α * schur ℤ β) (α.card + β.card) :=
    IsHomogeneous.mul (isHomogeneous_schur (R := ℤ) α)
      (isHomogeneous_schur (R := ℤ) β)
  have he := schur_repr_homogeneousComponent (α.card + β.card)
    (schur ℤ α * schur ℤ β) ν
  rw [homogeneousComponent_of_isHomogeneous hh, ite_eq_left rfl,
    ite_eq_right hcard, ← intCast_lrCoeff] at he
  apply h
  exact_mod_cast he

/-- Failure of containment forces a Littlewood–Richardson coefficient to vanish. -/
theorem lrCoeff_eq_zero_of_not_le (α β ν : YoungDiagram) (h : ¬ α ≤ ν) :
    lrCoeff α β ν = 0 := by
  by_contra hc
  exact h (le_of_lrCoeff_ne_zero α β ν hc)

end SymmetricFunction
