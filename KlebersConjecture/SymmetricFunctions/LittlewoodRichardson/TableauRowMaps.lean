import KlebersConjecture.SymmetricFunctions.LittlewoodRichardson.FiniteAlphabet.RowCount
import KlebersConjecture.Partitions.Tableau.RowMaps

/-! # Row multiplicities after inserting a zero first row

The straight-tableau row operations are supplied by the partition library. Their row
multiplicities, prefix counts and content follow by shifting the positive letters.

## Main results

* `rowCount_prependRow_succ` shifts row multiplicities below the first row.
* `countBelow_prependRow_succ` shifts prefix multiplicities.
* `content_prependRow_succ` shifts total content.
-/

noncomputable section

namespace SymmetricFunction.FiniteAlphabet.LittlewoodRichardson

open SemistandardYoungTableau

variable {β : YoungDiagram} {N : ℕ}

private theorem rowCountLt_zero (T : SemistandardYoungTableau β) (r : ℕ) :
    rowCountLt T r 0 = 0 := by
  simp only [rowCountLt, Nat.not_lt_zero, Finset.filter_false, Finset.card_empty]

/-- Insertion shifts each nonzero-letter row count to the preceding letter. -/
theorem rowCount_prependRow_succ (U : TauCeti.BoundedSSYT N (β.dropRows 1))
    (r x : ℕ) :
    rowCount (SemistandardYoungTableau.prependRow U).1 (r + 1) (x + 1) = rowCount U.1 r x := by
  simp only [rowCount, SemistandardYoungTableau.rowCountLt_prependRow_succ]

private theorem rowCountLt_prependRow_first (U : TauCeti.BoundedSSYT N (β.dropRows 1))
    (x : ℕ) : rowCountLt (SemistandardYoungTableau.prependRow U).1 0 (x + 1) = β.rowLen 0 := by
  simp only [rowCountLt, SemistandardYoungTableau.prependRow_zero, Nat.zero_lt_succ,
    Finset.filter_true, Finset.card_range]

/-- No positive letter occurs in the inserted first row. -/
theorem rowCount_prependRow_first (U : TauCeti.BoundedSSYT N (β.dropRows 1))
    (x : ℕ) : rowCount (SemistandardYoungTableau.prependRow U).1 0 (x + 1) = 0 := by
  simp only [rowCount, rowCountLt_prependRow_first, Nat.sub_self]

/-- Prefix counts of positive letters ignore the inserted zero row. -/
theorem countBelow_prependRow_succ (U : TauCeti.BoundedSSYT N (β.dropRows 1))
    (r x : ℕ) :
    countBelow (SemistandardYoungTableau.prependRow U).1 (r + 1) (x + 1) =
      countBelow U.1 r x := by
  induction r with
  | zero => simp only [countBelow_succ, countBelow_zero,
      rowCount_prependRow_first, add_zero]
  | succ r ih => rw [countBelow_succ, ih, rowCount_prependRow_succ, countBelow_succ]

/-- Inserting the zero first row shifts all positive content entries. -/
theorem content_prependRow_succ (U : TauCeti.BoundedSSYT N (β.dropRows 1)) (x : ℕ) :
    content (SemistandardYoungTableau.prependRow U).1 (x + 1) = content U.1 x := by
  rw [content_eq_countBelow_of_le _ _ (Nat.le_succ (β.colLen 0)),
    countBelow_prependRow_succ,
    ← content_eq_countBelow_of_le U.1 x (by rw [YoungDiagram.colLen_dropRows]; omega)]

/-- Below the first row, the letter zero never occurs. -/
theorem rowCount_zero_succ (T : SemistandardYoungTableau β) (r : ℕ) :
    rowCount T (r + 1) 0 = 0 := by
  have h : rowCountLt T (r + 1) 1 = 0 := by
    unfold rowCountLt
    have he : (Finset.range (β.rowLen (r + 1))).filter (fun j => T (r + 1) j < 1) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hm := Finset.mem_filter.mp hj
      have hp := le_entry T (YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_range.mp hm.1))
      omega
    rw [he, Finset.card_empty]
  simp only [rowCount, h, rowCountLt_zero, Nat.zero_sub]

/-- Every nonempty prefix contains all zeros in the inserted first row. -/
theorem countBelow_prependRow_zero (U : TauCeti.BoundedSSYT N (β.dropRows 1)) (r : ℕ) :
    countBelow (SemistandardYoungTableau.prependRow U).1 (r + 1) 0 = β.rowLen 0 := by
  induction r with
  | zero => simp only [countBelow_succ, countBelow_zero, rowCount,
      rowCountLt_prependRow_first, rowCountLt_zero, Nat.sub_zero, zero_add]
  | succ r ih => rw [countBelow_succ, ih, rowCount_zero_succ, add_zero]

/-- The inserted tableau has exactly one zero for each cell of the first row. -/
theorem content_prependRow_zero (U : TauCeti.BoundedSSYT N (β.dropRows 1)) :
    content (SemistandardYoungTableau.prependRow U).1 0 = β.rowLen 0 := by
  rw [content_eq_countBelow_of_le _ _ (Nat.le_succ (β.colLen 0)),
    countBelow_prependRow_zero]

/-- Saturating the zero-letter dominance bound forces the whole first row to be zero. -/
theorem firstRow_zero_of_content (T : SemistandardYoungTableau β)
    (h : content T 0 = β.rowLen 0) : ∀ j, T 0 j = 0 := by
  have he : β.cells.filter (fun c => T c.1 c.2 < 1) =
      β.cells.filter (fun c => c.1 < 1) := by
    apply Finset.eq_of_subset_of_card_le (filter_entry_lt_subset_filter_fst_lt T 1)
    rw [← sum_content_eq_card_filter, ← YoungDiagram.sum_range_rowLen_eq_card_filter_fst]
    simpa only [Finset.sum_range_one] using h.ge
  intro j
  by_cases hc : (0, j) ∈ β
  · have hm : (0, j) ∈ β.cells.filter (fun c => T c.1 c.2 < 1) := by
      rw [he, Finset.mem_filter]
      exact ⟨hc, by omega⟩
    have hp := (Finset.mem_filter.mp hm).2
    change T 0 j < 1 at hp
    omega
  · exact T.zeros hc

end SymmetricFunction.FiniteAlphabet.LittlewoodRichardson
