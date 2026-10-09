import KlebersConjecture.SymmetricFunctions.LittlewoodRichardson.TransposeCounts
import KlebersConjecture.Partitions.Skew.LatticeWord
import KlebersConjecture.Partitions.Skew.Cutoffs

/-! # Straight tableaux from skew row multiplicities

Transposing a skew tableau's row multiplicities reconstructs a bounded straight tableau.
Skew lattice inequalities become strict columns, and skew strict columns become lattice
inequalities from the inner diagram.

## Main results

* `LRTableau.sum_labels_skewRowCount` counts every cell in one skew row.
* `exists_straight_of_skew` reconstructs a bounded straight tableau with transposed counts.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace YoungDiagram.LRTableau

open scoped Classical

/-- The content height suffices to count all labels in each row of an LR tableau. -/
theorem sum_labels_skewRowCount {α β ν : YoungDiagram}
    (U : YoungDiagram.LRTableau α β ν) (r : ℕ) :
    (∑ i ∈ Finset.range (β.colLen 0), YoungDiagram.skewRowCount U.val r i) =
      ν.rowLen r - α.rowLen r := by
  change YoungDiagram.skewCountLt U.val r (β.colLen 0) = _
  rw [YoungDiagram.skewCountLt_eq_card]
  have he : ((Finset.range (ν.rowLen r)).filter fun c =>
      α.rowLen r ≤ c ∧ YoungDiagram.skewEntry U.val r c < Nat.succPNat (β.colLen 0)) =
      Finset.Ico (α.rowLen r) (ν.rowLen r) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hc, hl, _⟩
      exact ⟨hl, hc⟩
    · rintro ⟨hl, hc⟩
      have hp : (r, c) ∈ YoungDiagram.skewCells α ν :=
        (YoungDiagram.mem_skewCells _ _ _ _).mpr ⟨hl, hc⟩
      have hb := U.entry_le ⟨(r, c), hp⟩
      have he := YoungDiagram.skewEntry_cell U.val ⟨(r, c), hp⟩
      refine ⟨hc, hl, ?_⟩
      rw [he]
      change (U.val ⟨(r, c), hp⟩).val < β.colLen 0 + 1
      omega
  rw [he, Nat.card_Ico]

end YoungDiagram.LRTableau

namespace SymmetricFunction

open scoped Classical
open SemistandardYoungTableau FiniteAlphabet.LittlewoodRichardson

/-- Transposed row counts reconstruct a straight lattice tableau with the required weight. -/
theorem exists_straight_of_skew (α β ν : YoungDiagram) (n : ℕ)
    (_hα : α.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n) (U : YoungDiagram.LRTableau α β ν) :
    ∃ T : TauCeti.BoundedSSYT n β,
      IsLattice (fun i : Fin n => (α.rowLen i : ℤ)) T.val ∧
        (fun i : Fin n => (α.rowLen i : ℤ)) + weightVec T =
          (fun i : Fin n => (ν.rowLen i : ℤ)) ∧
        ∀ r i, rowCount T.val r i = YoungDiagram.skewRowCount U.val i r := by
  let m (r i : ℕ) := YoungDiagram.skewRowCount U.val i r
  have hb : ∀ r j, n ≤ j → m r j = 0 := by
    intro r j hj
    exact YoungDiagram.skewRowCount_eq_zero U.val j r (hν.trans hj)
  have hs : ∀ r, (∑ j ∈ Finset.range n, m r j) = β.rowLen r := by
    intro r
    change (∑ j ∈ Finset.range n, YoungDiagram.skewRowCount U.val j r) = _
    rw [YoungDiagram.sum_skewRowCount_stable U.val n r hν, U.sum_skewRowCount]
  have hc : ∀ r j, (∑ t ∈ Finset.range (j + 1), m (r + 1) t) ≤
      ∑ t ∈ Finset.range j, m r t := by
    intro r j
    exact (YoungDiagram.isLatticeWord_iff_skewRowCount U.val U.semistandard).mp U.lattice j r
  obtain ⟨T, hT⟩ := exists_ssyt_of_counts β m n hb hs hc
  have hcounts : ∀ r i, rowCount T.val r i = YoungDiagram.skewRowCount U.val i r := hT
  have hprefix (r i : ℕ) : countBelow T.val r i = YoungDiagram.skewCountLt U.val i r := by
    simp only [countBelow, YoungDiagram.skewCountLt, hcounts]
  have hlat : IsLattice (fun i : Fin n => (α.rowLen i : ℤ)) T.val := by
    intro r i hi
    rw [weightAt_of_lt _ hi, weightAt_of_lt _ (by omega), hprefix, hprefix]
    have he := (YoungDiagram.skewSemistandard_iff_cutoffs U.val U.contained U.semistandard.1).mp
      U.semistandard i r
    simp only [YoungDiagram.skewCutoff] at he
    exact_mod_cast he
  have hw : (fun i : Fin n => (α.rowLen i : ℤ)) + weightVec T =
      (fun i : Fin n => (ν.rowLen i : ℤ)) := by
    funext i
    change (α.rowLen i : ℤ) + (content T.val i : ℤ) = (ν.rowLen i : ℤ)
    have he : content T.val i = ν.rowLen i - α.rowLen i := by
      rw [content_eq_countBelow]
      simp only [countBelow, hcounts]
      exact U.sum_labels_skewRowCount i
    rw [he]
    have hl := YoungDiagram.rowLen_le_of_le U.contained i
    omega
  exact ⟨T, hlat, hw, hcounts⟩

end SymmetricFunction
