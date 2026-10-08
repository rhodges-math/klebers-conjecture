import Schubert.Partitions.Rows
import TauCeti.Combinatorics.Young.Kostka
import TauCeti.Combinatorics.Young.BenderKnuth

/-! # Deleting and inserting the first tableau row

These extensions of Mathlib's straight tableaux decrease the letters after deleting the first
row and increase them after inserting a zero first row.

## Main results

* `deleteRow_prependRow` and `prependRow_deleteRow` give the inverse identities.
* `rowCountLt_prependRow_succ` shifts the cumulative row multiplicities.

## Implementation notes

Entries of straight tableaux start at zero. Deletion removes a saturated zero first row
and decreases all remaining entries; prepending reverses this operation.
-/

noncomputable section

namespace SemistandardYoungTableau

variable {β : YoungDiagram} {N : ℕ}

/-- Delete the first tableau row and decrement the remaining entries. -/
def deleteRow (T : TauCeti.BoundedSSYT (N + 1) β) :
    TauCeti.BoundedSSYT N (β.dropRows 1) :=
  ⟨{ entry := fun i j => T.1 (i + 1) j - 1
     row_weak' := by
       intro i j k hj hc
       have h : (i + 1, k) ∈ β := by
         simpa only [YoungDiagram.mem_dropRows, Nat.add_comm 1] using hc
       exact Nat.sub_le_sub_right (T.1.row_weak hj h) 1
     col_strict' := by
       intro i k j hik hc
       have h : (k + 1, j) ∈ β := by
         simpa only [YoungDiagram.mem_dropRows, Nat.add_comm 1] using hc
       have hi : (i + 1, j) ∈ β := β.up_left_mem (by omega) le_rfl h
       have hpos := le_entry T.1 hi
       have hlt := T.1.col_strict (show i + 1 < k + 1 by omega) h
       omega
     zeros' := by
       intro i j hc
       have h : (i + 1, j) ∉ β := by
         simpa only [YoungDiagram.mem_dropRows, Nat.add_comm 1] using hc
       rw [T.1.zeros h, Nat.zero_sub] }, by
     intro i j hc
     have h : (i + 1, j) ∈ β := by
       simpa only [YoungDiagram.mem_dropRows, Nat.add_comm 1] using hc
     have hb := T.2 (i + 1) j h
     have hp := le_entry T.1 h
     change T.1 (i + 1) j - 1 < N
     omega⟩

/-- Insert a zero first row and increment the letters in every remaining row. -/
def prependRow (U : TauCeti.BoundedSSYT N (β.dropRows 1)) :
    TauCeti.BoundedSSYT (N + 1) β :=
  ⟨{ entry := fun i j => if (i, j) ∈ β then
         if i = 0 then 0 else U.1 (i - 1) j + 1 else 0
     row_weak' := by
       intro i j k hj hc
       have hcj := β.up_left_mem le_rfl hj.le hc
       rw [ite_eq_left hcj, ite_eq_left hc]
       split_ifs with hi
       · exact le_rfl
       · have h : (i - 1, k) ∈ β.dropRows 1 := by
           rw [YoungDiagram.mem_dropRows]
           simpa only [Nat.add_sub_of_le (by omega : 1 ≤ i)] using hc
         exact Nat.add_le_add_right (U.1.row_weak hj h) 1
     col_strict' := by
       intro i k j hik hc
       have hci := β.up_left_mem hik.le le_rfl hc
       rw [ite_eq_left hci, ite_eq_left hc]
       have hk : k ≠ 0 := by omega
       rw [ite_eq_right hk]
       split_ifs with hi
       · omega
       · have h : (k - 1, j) ∈ β.dropRows 1 := by
           rw [YoungDiagram.mem_dropRows]
           simpa only [Nat.add_sub_of_le (by omega : 1 ≤ k)] using hc
         have hlt := U.1.col_strict (show i - 1 < k - 1 by omega) h
         omega
     zeros' := by
       intro i j hc
       exact ite_eq_right hc }, by
     intro i j hc
     change (if (i, j) ∈ β then if i = 0 then 0 else U.1 (i - 1) j + 1 else 0) < N + 1
     rw [ite_eq_left hc]
     split_ifs with hi
     · omega
     · have h : (i - 1, j) ∈ β.dropRows 1 := by
         rw [YoungDiagram.mem_dropRows]
         simpa only [Nat.add_sub_of_le (by omega : 1 ≤ i)] using hc
       have hb := U.2 (i - 1) j h
       omega⟩

/-- Deletion decrements the entries of the following row. -/
theorem deleteRow_apply (T : TauCeti.BoundedSSYT (N + 1) β) (i j : ℕ) :
    (deleteRow T).1 i j = T.1 (i + 1) j - 1 := rfl

/-- A cell below the inserted row has the incremented tail entry. -/
theorem prependRow_succ (U : TauCeti.BoundedSSYT N (β.dropRows 1)) {i j : ℕ}
    (hc : (i, j) ∈ β.dropRows 1) : (prependRow U).1 (i + 1) j = U.1 i j + 1 := by
  have h : (i + 1, j) ∈ β := by
    simpa only [YoungDiagram.mem_dropRows, Nat.add_comm 1] using hc
  change (if (i + 1, j) ∈ β then if i + 1 = 0 then 0 else U.1 (i + 1 - 1) j + 1
    else 0) = _
  simp only [ite_eq_left h, Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false]

/-- The inserted first row consists entirely of zeros. -/
theorem prependRow_zero (U : TauCeti.BoundedSSYT N (β.dropRows 1)) (j : ℕ) :
    (prependRow U).1 0 j = 0 := by
  change (if (0, j) ∈ β then if 0 = 0 then 0 else U.1 (0 - 1) j + 1 else 0) = 0
  simp only [ite_true, ite_self]

/-- Removing the inserted row recovers the original bounded tableau. -/
theorem deleteRow_prependRow (U : TauCeti.BoundedSSYT N (β.dropRows 1)) :
    deleteRow (prependRow U) = U := by
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro i j
  rw [deleteRow_apply]
  by_cases hc : (i, j) ∈ β.dropRows 1
  · rw [prependRow_succ U hc]
    omega
  · have h : (i + 1, j) ∉ β := by
      simpa only [YoungDiagram.mem_dropRows, Nat.add_comm 1] using hc
    rw [(prependRow U).1.zeros h, U.1.zeros hc, Nat.zero_sub]

/-- Inserting a row after deletion recovers a tableau whose first row is zero. -/
theorem prependRow_deleteRow (T : TauCeti.BoundedSSYT (N + 1) β)
    (hzero : ∀ j, T.1 0 j = 0) : prependRow (deleteRow T) = T := by
  apply Subtype.ext
  apply SemistandardYoungTableau.ext
  intro i j
  cases i with
  | zero => rw [prependRow_zero, hzero]
  | succ i =>
    by_cases hc : (i + 1, j) ∈ β
    · have h : (i, j) ∈ β.dropRows 1 := by
        simpa only [YoungDiagram.mem_dropRows, Nat.add_comm 1] using hc
      rw [prependRow_succ _ h, deleteRow_apply]
      have hp := le_entry T.1 hc
      omega
    · rw [(prependRow (deleteRow T)).1.zeros hc, T.1.zeros hc]

/-- The cumulative count below a letter shifts by one after inserting the first row. -/
theorem rowCountLt_prependRow_succ (U : TauCeti.BoundedSSYT N (β.dropRows 1))
    (r x : ℕ) : rowCountLt (prependRow U).1 (r + 1) (x + 1) = rowCountLt U.1 r x := by
  unfold rowCountLt
  rw [YoungDiagram.rowLen_dropRows]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hx⟩
    have hc : (r, j) ∈ β.dropRows 1 := by
      rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.rowLen_dropRows]
      simpa only [Nat.add_comm 1] using hj
    rw [prependRow_succ U hc] at hx
    exact ⟨by simpa only [Nat.add_comm 1] using hj, by omega⟩
  · rintro ⟨hj, hx⟩
    have hc : (r, j) ∈ β.dropRows 1 := by
      rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.rowLen_dropRows]
      exact hj
    refine ⟨by simpa only [Nat.add_comm 1] using hj, ?_⟩
    rw [prependRow_succ U hc]
    omega

end SemistandardYoungTableau
