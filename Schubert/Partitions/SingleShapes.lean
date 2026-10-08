import Schubert.Partitions.Rectangle
import TauCeti.Combinatorics.Young.Partitions

/-! # Single-row and single-column Young diagrams

These shape constructors distinguish diagrams from the existing row-cell operation.

## Main results

* `diagramOf_indiscrete_eq_singleRow` identifies the single-part partition with a single row.
* `diagramOf_ones_eq_singleColumn` identifies the partition into ones with a single column.

## Implementation notes

Rows are zero based. Size zero gives the empty diagram for both constructors.
-/

namespace YoungDiagram

/-- The Young diagram consisting of one row of length k. -/
def singleRow (k : ℕ) : YoungDiagram := rectangle 1 k

/-- The Young diagram consisting of one column of length k. -/
def singleColumn (k : ℕ) : YoungDiagram := rectangle k 1

/-- A single row is the rectangle of height one. -/
theorem singleRow_eq_rectangle (k : ℕ) : singleRow k = rectangle 1 k := rfl

/-- A single column is the rectangle of width one. -/
theorem singleColumn_eq_rectangle (k : ℕ) : singleColumn k = rectangle k 1 := rfl

/-- A single row has its prescribed length only at row zero. -/
@[simp] theorem rowLen_singleRow (k i : ℕ) :
    (singleRow k).rowLen i = if i = 0 then k else 0 := by
  simp only [singleRow, rowLen_rectangle, Nat.lt_one_iff]

/-- A single column has one cell in each row before its height. -/
@[simp] theorem rowLen_singleColumn (k i : ℕ) :
    (singleColumn k).rowLen i = if i < k then 1 else 0 := rowLen_rectangle k 1 i

/-- The size of a single row is its length. -/
@[simp] theorem card_singleRow (k : ℕ) : (singleRow k).card = k := by
  simp [singleRow]

/-- The size of a single column is its height. -/
@[simp] theorem card_singleColumn (k : ℕ) : (singleColumn k).card = k := by
  simp [singleColumn]

/-- The diagram of the partition with one part is the single-row shape. -/
@[simp] theorem diagramOf_indiscrete_eq_singleRow (k : ℕ) :
    TauCeti.diagramOf (Nat.Partition.indiscrete k) = singleRow k := by
  apply rowLen_injective
  funext i
  rw [TauCeti.rowLen_diagramOf, rowLen_singleRow]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [Nat.Partition.indiscrete_parts hk.ne', Multiset.sort_singleton]
    cases i <;> simp

/-- The diagram of the partition into ones is the single-column shape. -/
@[simp] theorem diagramOf_ones_eq_singleColumn (k : ℕ) :
    TauCeti.diagramOf (TauCeti.Nat.Partition.ones k) = singleColumn k := by
  have hs : (Multiset.replicate k 1).sort (· ≥ ·) = List.replicate k 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Multiset.replicate_succ, Multiset.sort_cons]
      · simpa only [List.replicate_succ] using congrArg (List.cons 1) ih
      · intro x hx
        exact le_of_eq (Multiset.eq_of_mem_replicate hx)
  apply rowLen_injective
  funext i
  rw [TauCeti.rowLen_diagramOf, TauCeti.Nat.Partition.ones_parts, hs, rowLen_singleColumn]
  by_cases hi : i < k
  · simp only [List.getD_replicate 1 hi, ite_eq_left hi]
  · simp only [List.getD_eq_default (List.replicate k 1) 0 (by simpa using hi), ite_eq_right hi]

end YoungDiagram
