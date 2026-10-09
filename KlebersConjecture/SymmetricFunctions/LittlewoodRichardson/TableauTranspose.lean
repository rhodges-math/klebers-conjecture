import KlebersConjecture.SymmetricFunctions.LittlewoodRichardson.SkewReconstruction
import KlebersConjecture.SymmetricFunctions.LittlewoodRichardson.StraightReconstruction
import KlebersConjecture.SymmetricFunctions.LittlewoodRichardson.Containment

/-! # Transposing Littlewood--Richardson tableaux

The row multiplicity matrix exchanges straight rows with positive labels of skew rows.
Reconstruction in each direction preserves this matrix, so the constructions are inverse.

## Main definitions

* `YoungDiagram.SkewFilling` labels the cells of a skew diagram by positive integers.
* `YoungDiagram.LRTableau` imposes semistandardness, content and a lattice reading word.
* `SymmetricFunction.lrTableauTransposeEquiv` transposes the row multiplicity matrix.

## Main results

* `lrCoeff_eq_card_lrTableaux` identifies the stable coefficient with the skew count.
* `lrTableauTransposeEquiv` identifies the finite straight count with skew LR tableaux.

## Implementation notes

The skew carrier belongs to `YoungDiagram`; its labels lie in `ℕ+`. Straight tableaux
use zero-based bounded labels. Transposition sends a straight row index to the corresponding
positive skew label, and a straight label to a skew row index. The two reconstruction maps
preserve row multiplicities, which determine semistandard fillings uniquely.
The public counting endpoint remains `SymmetricFunction.lrCoeff_eq_card_lrTableaux`;
outside diagram containment, both its coefficient and its skew tableau count vanish.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction

open FiniteAlphabet.LittlewoodRichardson

/-- Bounded straight tableaux satisfying the initial lattice and terminal weight conditions. -/
private abbrev Counted (α β ν : YoungDiagram) (n : ℕ) :=
  {T : TauCeti.BoundedSSYT n β //
    IsLattice (fun i : Fin n => (α.rowLen i : ℤ)) T.val ∧
      (fun i : Fin n => (α.rowLen i : ℤ)) + weightVec T =
        (fun i : Fin n => (ν.rowLen i : ℤ))}

/-- Reconstruct a skew LR tableau from the multiplicities of a counted straight tableau. -/
private def skewOfStraight (α β ν : YoungDiagram) (n : ℕ)
    (hα : α.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n) (T : Counted α β ν n) :
    YoungDiagram.LRTableau α β ν :=
  (exists_skew_of_straight α β ν n hα hν T.val T.property.1 T.property.2).choose

private theorem skewOfStraight_counts (α β ν : YoungDiagram) (n : ℕ)
    (hα : α.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n) (T : Counted α β ν n) (r i : ℕ) :
    YoungDiagram.skewRowCount (skewOfStraight α β ν n hα hν T).val r i = rowCount T.val.val i r :=
  (exists_skew_of_straight α β ν n hα hν T.val T.property.1 T.property.2).choose_spec r i

/-- Reconstruct a counted straight tableau from the multiplicities of a skew LR tableau. -/
private def straightOfSkew (α β ν : YoungDiagram) (n : ℕ)
    (hα : α.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n) (U : YoungDiagram.LRTableau α β ν) :
    Counted α β ν n :=
  let h := exists_straight_of_skew α β ν n hα hν U
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1⟩

private theorem straightOfSkew_counts (α β ν : YoungDiagram) (n : ℕ)
    (hα : α.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n) (U : YoungDiagram.LRTableau α β ν) (r i : ℕ) :
    rowCount (straightOfSkew α β ν n hα hν U).val.val r i = YoungDiagram.skewRowCount U.val i r :=
  (exists_straight_of_skew α β ν n hα hν U).choose_spec.2.2 r i

/-- The finite straight lattice tableaux and the skew LR tableaux are in bijection. -/
def lrTableauTransposeEquiv (α β ν : YoungDiagram) (n : ℕ)
    (hα : α.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n) :
    {T : TauCeti.BoundedSSYT n β //
      IsLattice (fun i : Fin n => (α.rowLen i : ℤ)) T.val ∧
        (fun i : Fin n => (α.rowLen i : ℤ)) + weightVec T =
          (fun i : Fin n => (ν.rowLen i : ℤ))} ≃ YoungDiagram.LRTableau α β ν where
  toFun := skewOfStraight α β ν n hα hν
  invFun := straightOfSkew α β ν n hα hν
  left_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    apply eq_of_rowCount_eq
    intro r i
    exact (straightOfSkew_counts α β ν n hα hν _ r i).trans
      (skewOfStraight_counts α β ν n hα hν T i r)
  right_inv U := by
    apply Subtype.ext
    apply YoungDiagram.skewFilling_eq_of_rowCounts _ _
      (skewOfStraight α β ν n hα hν _).semistandard.1 U.semistandard.1
    intro r i
    exact (skewOfStraight_counts α β ν n hα hν _ r i).trans
      (straightOfSkew_counts α β ν n hα hν U i r)

end SymmetricFunction

noncomputable section

namespace SymmetricFunction

open FiniteAlphabet.LittlewoodRichardson

/-- A Littlewood--Richardson coefficient counts skew tableaux of the prescribed content. -/
theorem lrCoeff_eq_card_lrTableaux (α β ν : YoungDiagram) :
    lrCoeff α β ν = Fintype.card (YoungDiagram.LRTableau α β ν) := by
  classical
  by_cases hαν : α ≤ ν
  · obtain ⟨n, hα, hν, hf⟩ := exists_lr_alphabet_bound α β ν
    rw [lrCoeff_eq_tableau_count α β ν n hα hν hf]
    exact (Fintype.card_subtype _).symm.trans
      (Fintype.card_congr (lrTableauTransposeEquiv α β ν n hα hν))
  · rw [lrCoeff_eq_zero_of_not_le α β ν hαν, YoungDiagram.card_lrTableau_of_not_le hαν]

end SymmetricFunction
