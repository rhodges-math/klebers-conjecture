import KlebersConjecture.Partitions.Basic
import TauCeti.Combinatorics.Young.HookLength.Basic

/-! # Deleting rows and columns of Young diagrams

Deleting initial rows and translating the remaining cells gives another Young diagram.
Deleting the first row and column subtracts one from each remaining row length.

## Main results

* `YoungDiagram.rowLen_dropRows` and `YoungDiagram.colLen_dropRows` describe row deletion.
* `YoungDiagram.dropRows_add` states that row deletion preserves componentwise addition.
* `YoungDiagram.rowLen_removeFirstRowCol` describes the first row and column deletion.
* `YoungDiagram.hookLength_zero_zero` gives the first hook of a nonempty diagram.

## Implementation notes

Row and column coordinates start at zero. Deleted rows are translated upward; sizes and
lengths use natural subtraction, so deletion beyond the boundary gives the empty diagram.
-/

namespace YoungDiagram

/-- Delete the first `r` rows of a diagram and move the remaining rows upward. -/
def dropRows (μ : YoungDiagram) (r : ℕ) : YoungDiagram :=
  ofRowLensFin (fun i : Fin (μ.colLen 0) => μ.rowLen (r + i))
    (fun _ _ h => μ.rowLen_anti _ _ (Nat.add_le_add_left h r))

/-- The row lengths after deleting initial rows are the shifted row lengths. -/
@[simp]
theorem rowLen_dropRows (μ : YoungDiagram) (r i : ℕ) :
    (μ.dropRows r).rowLen i = μ.rowLen (r + i) := by
  unfold dropRows
  by_cases hi : i < μ.colLen 0
  · exact rowLen_ofRowLensFin _ _ ⟨i, hi⟩
  · have hz := rowLen_ofRowLensFin_eq_zero_of_le
      (fun k : Fin (μ.colLen 0) => μ.rowLen (r + k))
      (fun _ _ h => μ.rowLen_anti _ _ (Nat.add_le_add_left h r))
      (Nat.le_of_not_lt hi)
    rw [rowLen_eq_zero_of_colLen_le (by omega : μ.colLen 0 ≤ r + i)]
    exact hz

/-- Membership after deleting initial rows is membership at the shifted coordinates. -/
@[simp]
theorem mem_dropRows (μ : YoungDiagram) (r i j : ℕ) :
    (i, j) ∈ μ.dropRows r ↔ (r + i, j) ∈ μ := by
  simp only [mem_iff_lt_rowLen, rowLen_dropRows]

/-- Deleting initial rows removes that many cells from every column, up to its length. -/
@[simp]
theorem colLen_dropRows (μ : YoungDiagram) (r j : ℕ) :
    (μ.dropRows r).colLen j = μ.colLen j - r := by
  apply Nat.le_antisymm
  · by_contra h
    have hm : (μ.colLen j - r, j) ∈ μ.dropRows r :=
      mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
    rw [mem_dropRows, mem_iff_lt_colLen] at hm
    omega
  · by_contra h
    have hm : ((μ.dropRows r).colLen j, j) ∈ μ.dropRows r := by
      rw [mem_dropRows, mem_iff_lt_colLen]
      omega
    have hp := mem_iff_lt_colLen.mp hm
    omega

/-- Deleting no rows leaves the diagram unchanged. -/
@[simp]
theorem dropRows_zero (μ : YoungDiagram) : μ.dropRows 0 = μ := by
  apply rowLen_injective
  funext i
  simp

/-- Deleting initial rows from the empty diagram gives the empty diagram. -/
@[simp]
theorem dropRows_bot (r : ℕ) : (⊥ : YoungDiagram).dropRows r = ⊥ := by
  apply rowLen_injective
  funext i
  simp

/-- Successive row deletions add their numbers of deleted rows. -/
@[simp]
theorem dropRows_dropRows (μ : YoungDiagram) (r s : ℕ) :
    (μ.dropRows r).dropRows s = μ.dropRows (r + s) := by
  apply rowLen_injective
  funext i
  simp only [rowLen_dropRows, Nat.add_assoc]

/-- Row deletion preserves componentwise sums. -/
@[simp]
theorem dropRows_add (μ ν : YoungDiagram) (r : ℕ) :
    (μ + ν).dropRows r = μ.dropRows r + ν.dropRows r := by
  apply rowLen_injective
  funext i
  simp

/-- Deleting rows preserves containment. -/
theorem dropRows_mono {μ ν : YoungDiagram} (h : μ ≤ ν) (r : ℕ) :
    μ.dropRows r ≤ ν.dropRows r := by
  apply le_of_forall_rowLen_le
  intro i
  simpa only [rowLen_dropRows] using rowLen_le_of_le h (r + i)

/-- The shifted remainder is contained in the original diagram. -/
theorem dropRows_le (μ : YoungDiagram) (r : ℕ) : μ.dropRows r ≤ μ := by
  apply le_of_forall_rowLen_le
  intro i
  rw [rowLen_dropRows]
  exact μ.rowLen_anti i (r + i) (Nat.le_add_left i r)

/-- Deleting all the rows gives the empty diagram. -/
theorem dropRows_eq_bot {μ : YoungDiagram} {r : ℕ} (h : μ.colLen 0 ≤ r) :
    μ.dropRows r = ⊥ := by
  rw [eq_bot_iff_colLen_zero, colLen_dropRows]
  exact Nat.sub_eq_zero_of_le h

/-- The size after deleting rows is the sum of the shifted row lengths. -/
theorem card_dropRows (μ : YoungDiagram) (r : ℕ) :
    (μ.dropRows r).card = ∑ i ∈ Finset.range (μ.colLen 0), μ.rowLen (r + i) := by
  rw [card_eq_sum_range_rowLen (μ.dropRows r) (N := μ.colLen 0) (by simp)]
  simp only [rowLen_dropRows]

/-- The removed rows and the remaining diagram together have the original size. -/
theorem card_dropRows_add (μ : YoungDiagram) (r : ℕ) :
    (μ.dropRows r).card + ∑ i ∈ Finset.range r, μ.rowLen i = μ.card := by
  rw [card_dropRows, card_eq_sum_range_rowLen μ (N := r + μ.colLen 0) (by omega),
    Finset.sum_range_add]
  exact Nat.add_comm _ _

/-- Deleting initial rows cannot increase the number of cells. -/
theorem card_dropRows_le (μ : YoungDiagram) (r : ℕ) : (μ.dropRows r).card ≤ μ.card := by
  have h := card_dropRows_add μ r
  omega

/-- Delete the first row and first column, moving the remaining cells up and left. -/
def removeFirstRowCol (μ : YoungDiagram) : YoungDiagram :=
  ofRowLensFin (fun i : Fin (μ.colLen 0) => μ.rowLen (i + 1) - 1)
    (fun _ _ h => Nat.sub_le_sub_right (μ.rowLen_anti _ _ (Nat.add_le_add_right h 1)) 1)

/-- Removing the first row and column subtracts one from each later row length. -/
@[simp]
theorem rowLen_removeFirstRowCol (μ : YoungDiagram) (i : ℕ) :
    μ.removeFirstRowCol.rowLen i = μ.rowLen (i + 1) - 1 := by
  unfold removeFirstRowCol
  by_cases hi : i < μ.colLen 0
  · exact rowLen_ofRowLensFin _ _ ⟨i, hi⟩
  · have hz := rowLen_ofRowLensFin_eq_zero_of_le
      (fun k : Fin (μ.colLen 0) => μ.rowLen (k + 1) - 1)
      (fun _ _ h => Nat.sub_le_sub_right
        (μ.rowLen_anti _ _ (Nat.add_le_add_right h 1)) 1)
      (Nat.le_of_not_lt hi)
    rw [rowLen_eq_zero_of_colLen_le (by omega : μ.colLen 0 ≤ i + 1)]
    exact hz

/-- Membership after deleting the first row and column is shifted in both coordinates. -/
@[simp]
theorem mem_removeFirstRowCol (μ : YoungDiagram) (i j : ℕ) :
    (i, j) ∈ μ.removeFirstRowCol ↔ (i + 1, j + 1) ∈ μ := by
  simp only [mem_iff_lt_rowLen, rowLen_removeFirstRowCol]
  omega

/-- Removing the first row and column subtracts one from each later column length. -/
@[simp]
theorem colLen_removeFirstRowCol (μ : YoungDiagram) (j : ℕ) :
    μ.removeFirstRowCol.colLen j = μ.colLen (j + 1) - 1 := by
  apply Nat.le_antisymm
  · by_contra h
    have hm : (μ.colLen (j + 1) - 1, j) ∈ μ.removeFirstRowCol :=
      mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
    rw [mem_removeFirstRowCol, mem_iff_lt_colLen] at hm
    omega
  · by_contra h
    have hm : (μ.removeFirstRowCol.colLen j, j) ∈ μ.removeFirstRowCol := by
      rw [mem_removeFirstRowCol, mem_iff_lt_colLen]
      omega
    have hp := mem_iff_lt_colLen.mp hm
    omega

/-- Removing the first row and column from the empty diagram gives the empty diagram. -/
@[simp]
theorem removeFirstRowCol_bot : (⊥ : YoungDiagram).removeFirstRowCol = ⊥ := by
  apply rowLen_injective
  funext i
  simp

/-- First row and column deletion commutes with deleting initial rows. -/
theorem dropRows_removeFirstRowCol (μ : YoungDiagram) (r : ℕ) :
    μ.removeFirstRowCol.dropRows r = (μ.dropRows r).removeFirstRowCol := by
  apply rowLen_injective
  funext i
  simp only [rowLen_dropRows, rowLen_removeFirstRowCol, Nat.add_assoc]

/-- First row and column deletion preserves containment. -/
theorem removeFirstRowCol_mono {μ ν : YoungDiagram} (h : μ ≤ ν) :
    μ.removeFirstRowCol ≤ ν.removeFirstRowCol := by
  apply le_of_forall_rowLen_le
  intro i
  simpa only [rowLen_removeFirstRowCol] using Nat.sub_le_sub_right (rowLen_le_of_le h (i + 1)) 1

/-- The shifted diagram without the first row and column is contained in the original. -/
theorem removeFirstRowCol_le (μ : YoungDiagram) : μ.removeFirstRowCol ≤ μ := by
  apply le_of_forall_rowLen_le
  intro i
  rw [rowLen_removeFirstRowCol]
  exact (Nat.sub_le _ _).trans (μ.rowLen_anti i (i + 1) (Nat.le_succ i))

end YoungDiagram

/-!
# The hook at the first cell

The hook at the first cell of a nonempty Young diagram records its first row and column.
-/

namespace YoungDiagram

/-- The first hook has the first row length plus the first column length minus one. -/
theorem hookLength_zero_zero {μ : YoungDiagram} (hμ : μ ≠ ⊥) :
    μ.hookLength (0, 0) = μ.rowLen 0 + μ.colLen 0 - 1 := by
  have hrow : 0 < μ.rowLen 0 := by
    by_contra h
    apply hμ
    apply rowLen_injective
    funext i
    have := μ.rowLen_anti 0 i (Nat.zero_le i)
    simp only [rowLen_bot]
    omega
  have hcol : 0 < μ.colLen 0 :=
    mem_iff_lt_colLen.mp (mem_iff_lt_rowLen.mpr hrow : (0, 0) ∈ μ)
  simp only [hookLength, armLength, legLength, Nat.sub_zero]
  omega

end YoungDiagram
