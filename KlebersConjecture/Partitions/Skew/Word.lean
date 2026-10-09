import KlebersConjecture.Partitions.Skew.Tableau
import Mathlib.Data.List.Intervals
import Mathlib.Data.List.Count

/-! # Reading words of positive skew fillings

Each row is read from right to left and the rows are concatenated from top to bottom.
A lattice word has at least as many labels i as i+1 in every initial segment.

## Main results

* `mem_skewRowWord` identifies its labels with the skew cells in the chosen row.
* `skewReadingWord_self` gives the empty word for the empty skew shape.
* `IsLatticeWord` expresses the positive-label lattice condition.

## Implementation notes

Labels start at one. Prefix lengths and row indices start at zero; every prefix includes
the empty prefix.
-/

noncomputable section

namespace YoungDiagram

/-- Read one skew row from its rightmost cell to its leftmost cell. -/
def skewRowWord {α ν : YoungDiagram} (T : SkewFilling α ν) (r : ℕ) : List ℕ+ :=
  (List.range' (α.rowLen r) (ν.rowLen r - α.rowLen r)).reverse.map (skewEntry T r)

/-- A row word has one label for every column between its inner and outer boundaries. -/
theorem length_skewRowWord {α ν : YoungDiagram} (T : SkewFilling α ν) (r : ℕ) :
    (skewRowWord T r).length = ν.rowLen r - α.rowLen r := by
  simp only [skewRowWord, List.length_map, List.length_reverse, List.length_range']

/-- A label belongs to the row word exactly when a cell of that row carries it. -/
theorem mem_skewRowWord {α ν : YoungDiagram} (T : SkewFilling α ν) (r : ℕ) (x : ℕ+) :
    x ∈ skewRowWord T r ↔
      ∃ c, (r, c) ∈ skewCells α ν ∧ skewEntry T r c = x := by
  simp only [skewRowWord, List.mem_map, List.mem_reverse, List.mem_range', mem_skewCells, one_mul]
  constructor
  · rintro ⟨c, ⟨i, hi, hc⟩, he⟩
    exact ⟨c, ⟨by omega, by omega⟩, he⟩
  · rintro ⟨c, ⟨hl, hr⟩, he⟩
    exact ⟨c, ⟨c - α.rowLen r, by omega, by omega⟩, he⟩

/-- Concatenate the words of the first r rows in increasing row order. -/
def skewRowsWord {α ν : YoungDiagram} (T : SkewFilling α ν) : ℕ → List ℕ+
  | 0 => []
  | r + 1 => skewRowsWord T r ++ skewRowWord T r

/-- The right-to-left, top-to-bottom reading word of a skew filling. -/
def skewReadingWord {α ν : YoungDiagram} (T : SkewFilling α ν) : List ℕ+ :=
  skewRowsWord T (ν.colLen 0)

/-- Every initial segment has at least as many i labels as i+1 labels. -/
def IsLatticeWord (w : List ℕ+) : Prop :=
  ∀ k ≤ w.length, ∀ i : ℕ+, (w.take k).count (i + 1) ≤ (w.take k).count i

/-- The empty word is lattice. -/
@[simp] theorem isLatticeWord_nil : IsLatticeWord [] := by
  intro k hk i
  simp

/-- A row of an empty skew shape has empty reading word. -/
@[simp] theorem skewRowWord_self (α : YoungDiagram) (T : SkewFilling α α) (r : ℕ) :
    skewRowWord T r = [] := by
  simp only [skewRowWord, Nat.sub_self, List.range'_zero, List.reverse_nil, List.map_nil]

/-- Any initial collection of rows of an empty skew shape has empty word. -/
@[simp] theorem skewRowsWord_self (α : YoungDiagram) (T : SkewFilling α α) (r : ℕ) :
    skewRowsWord T r = [] := by
  induction r with
  | zero => rfl
  | succ r ih => rw [skewRowsWord, ih, skewRowWord_self, List.append_nil]

/-- An empty skew shape has empty reading word. -/
@[simp] theorem skewReadingWord_self (α : YoungDiagram) (T : SkewFilling α α) :
    skewReadingWord T = [] := skewRowsWord_self α T _

end YoungDiagram
