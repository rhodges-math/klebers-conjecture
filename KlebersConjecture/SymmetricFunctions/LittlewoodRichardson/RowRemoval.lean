import KlebersConjecture.SymmetricFunctions.LittlewoodRichardson.HighestWeight
import KlebersConjecture.Partitions.Rows
import KlebersConjecture.SymmetricFunctions.LittlewoodRichardson.TableauRows

/-! # First-row bounds and removal of saturated rows

Zero entries of a semistandard tableau lie in its first row. The finite tableau count
therefore bounds the first row of every nonzero Schur product coordinate.

## Main results

* `rowLen_zero_le_of_lrCoeff_ne_zero` bounds the first row of a nonzero coefficient.
* `lrCoeff_eq_lrCoeff_dropRows` deletes a saturated first row from all three diagrams.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction

open FiniteAlphabet.LittlewoodRichardson SemistandardYoungTableau

private theorem content_zero_le_rowLen {β : YoungDiagram} (T : SemistandardYoungTableau β) :
    content T 0 ≤ β.rowLen 0 := by
  have h := Finset.card_le_card (filter_entry_lt_subset_filter_fst_lt T 1)
  rw [← sum_content_eq_card_filter, ← YoungDiagram.sum_range_rowLen_eq_card_filter_fst] at h
  simpa using h

/-- A nonzero Littlewood--Richardson coefficient bounds the first row of the target. -/
theorem rowLen_zero_le_of_lrCoeff_ne_zero (α β ν : YoungDiagram) (hc : lrCoeff α β ν ≠ 0) :
    ν.rowLen 0 ≤ α.rowLen 0 + β.rowLen 0 := by
  classical
  obtain ⟨m, ha, hv, hm⟩ := exists_lr_alphabet_bound α β ν
  let n := m + 1
  have hn : 0 < n := Nat.zero_lt_succ m
  have hα : α.colLen 0 ≤ n := ha.trans (Nat.le_succ m)
  have hν : ν.colLen 0 ≤ n := hv.trans (Nat.le_succ m)
  have hf : ∀ μ ∈ lrSupport α β, μ.colLen 0 ≤ n :=
    fun μ hμ => (hm μ hμ).trans (Nat.le_succ m)
  rw [lrCoeff_eq_tableau_count α β ν n hα hν hf] at hc
  obtain ⟨T, hT⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
  have hw := congrFun (Finset.mem_filter.mp hT).2.2 (⟨0, hn⟩ : Fin n)
  simp only [Pi.add_apply, weightVec] at hw
  have hb := content_zero_le_rowLen T.1
  omega

/-- Deleting a saturated first row from both inputs and the target preserves the coefficient. -/
theorem lrCoeff_eq_lrCoeff_dropRows (α β ν : YoungDiagram)
    (hs : ν.rowLen 0 = α.rowLen 0 + β.rowLen 0) :
    lrCoeff α β ν = lrCoeff (α.dropRows 1) (β.dropRows 1) (ν.dropRows 1) := by
  classical
  obtain ⟨m, hαm, hνm, hm⟩ := exists_lr_alphabet_bound α β ν
  obtain ⟨k, hak, hvk, hk⟩ :=
    exists_lr_alphabet_bound (α.dropRows 1) (β.dropRows 1) (ν.dropRows 1)
  let n := max m k
  have hα : α.colLen 0 ≤ n := hαm.trans (le_max_left _ _)
  have hν : ν.colLen 0 ≤ n := hνm.trans (le_max_left _ _)
  have hf : ∀ μ ∈ lrSupport α β, μ.colLen 0 ≤ n + 1 := fun μ hμ =>
    (hm μ hμ).trans ((le_max_left _ _).trans (Nat.le_succ n))
  have ht : ∀ μ ∈ lrSupport (α.dropRows 1) (β.dropRows 1), μ.colLen 0 ≤ n :=
    fun μ hμ => (hk μ hμ).trans (le_max_right _ _)
  have ha : (α.dropRows 1).colLen 0 ≤ n := hak.trans (le_max_right _ _)
  have hv : (ν.dropRows 1).colLen 0 ≤ n := hvk.trans (le_max_right _ _)
  rw [lrCoeff_eq_tableau_count α β ν (n + 1) (hα.trans (Nat.le_succ n))
    (hν.trans (Nat.le_succ n)) hf,
    lrCoeff_eq_tableau_count (α.dropRows 1) (β.dropRows 1) (ν.dropRows 1) n ha hv ht]
  simpa only [Fintype.card_subtype] using saturated_tableau_count n α β ν hs

end SymmetricFunction
