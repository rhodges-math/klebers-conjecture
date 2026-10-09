import KlebersConjecture.Partitions.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.PNat.Basic

/-! # Positive fillings of skew Young diagrams

A skew filling assigns a positive integer to every cell of the outer diagram
outside the inner diagram. Semistandardness compares entries along rows and columns.

## Main definitions

* `skewCells` is the finite set difference of the diagram cells.
* `SkewFilling` assigns positive natural labels to those cells.
* `SkewSemistandard` imposes weak rows and strict columns.
* `skewContent` records label multiplicities.

## Main results

* `mem_skewCells` gives the interval of columns in each skew row.
* `skewContent_apply` counts the cells carrying a prescribed positive label.
* `skewContent_sum` counts all cells.
## Implementation notes

Cells and row indices start at zero, while filling labels are positive natural numbers.
A filling is a function on the finite subtype of skew cells.
## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Section I.9.
-/

noncomputable section

namespace YoungDiagram

/-- Cells of the outer Young diagram outside the inner Young diagram. -/
def skewCells (α ν : YoungDiagram) : Finset (ℕ × ℕ) := ν.cells \ α.cells

/-- A skew cell lies between the inner and outer row boundaries. -/
@[simp] theorem mem_skewCells (α ν : YoungDiagram) (r c : ℕ) :
    (r, c) ∈ skewCells α ν ↔ α.rowLen r ≤ c ∧ c < ν.rowLen r := by
  simp only [skewCells, Finset.mem_sdiff, YoungDiagram.mem_cells,
    YoungDiagram.mem_iff_lt_rowLen, not_lt]
  exact and_comm

/-- A diagram has no cells outside itself. -/
@[simp] theorem skewCells_self (α : YoungDiagram) : skewCells α α = ∅ :=
  Finset.sdiff_self α.cells

/-- The number of skew cells is the difference of sizes under containment. -/
theorem card_skewCells {α ν : YoungDiagram} (h : α ≤ ν) :
    (skewCells α ν).card = ν.card - α.card :=
  Finset.card_sdiff_of_subset (YoungDiagram.cells_subset_iff.mpr h)

/-- A filling of the skew cells by the positive integers. -/
abbrev SkewFilling (α ν : YoungDiagram) := (skewCells α ν) → ℕ+

/-- Extend a skew filling by the label one outside its cells. -/
def skewEntry {α ν : YoungDiagram} (T : SkewFilling α ν) (r c : ℕ) : ℕ+ :=
  if h : (r, c) ∈ skewCells α ν then T ⟨(r, c), h⟩ else 1

/-- On a skew cell the extended entry is its assigned label. -/
@[simp] theorem skewEntry_cell {α ν : YoungDiagram} (T : SkewFilling α ν)
    (p : skewCells α ν) : skewEntry T p.val.1 p.val.2 = T p := by
  simp only [skewEntry, dite_eq_left p.property]

/-- Rows weakly increase to the right and columns strictly increase downward. -/
def SkewSemistandard {α ν : YoungDiagram} (T : SkewFilling α ν) : Prop :=
  (∀ p q : skewCells α ν, p.val.1 = q.val.1 → p.val.2 ≤ q.val.2 → T p ≤ T q) ∧
    (∀ p q : skewCells α ν, p.val.2 = q.val.2 → p.val.1 < q.val.1 → T p < T q)

/-- The content records the multiplicity of every positive label among the skew cells. -/
def skewContent {α ν : YoungDiagram} (T : SkewFilling α ν) : ℕ+ →₀ ℕ :=
  ((skewCells α ν).val.map fun p => skewEntry T p.1 p.2).toFinsupp

/-- Content at a label is the number of cells carrying that label. -/
theorem skewContent_apply {α ν : YoungDiagram} (T : SkewFilling α ν) (x : ℕ+) :
    skewContent T x = ((skewCells α ν).filter fun p => skewEntry T p.1 p.2 = x).card := by
  rw [skewContent, Multiset.toFinsupp_apply, Multiset.count_map]
  simp [Finset.card, Finset.filter_val, eq_comm]

/-- The support of content consists exactly of the labels used by skew cells. -/
theorem support_skewContent {α ν : YoungDiagram} (T : SkewFilling α ν) :
    (skewContent T).support = (skewCells α ν).image (fun p => skewEntry T p.1 p.2) := by
  rw [skewContent, Multiset.toFinsupp_support, Multiset.toFinset_map, Finset.val_toFinset]

/-- Summing all label multiplicities gives the number of skew cells. -/
theorem skewContent_sum {α ν : YoungDiagram} (T : SkewFilling α ν) :
    (skewContent T).sum (fun _ n => n) = (skewCells α ν).card := by
  change (((skewCells α ν).val.map fun p => skewEntry T p.1 p.2).toFinsupp).sum
    (fun _ => id) = (skewCells α ν).card
  rw [Multiset.toFinsupp_sum_eq, Multiset.card_map]
  rfl

/-- A filling of an empty skew shape has zero content. -/
@[simp] theorem skewContent_self (α : YoungDiagram) (T : SkewFilling α α) :
    skewContent T = 0 := by
  simp only [skewContent, skewCells_self, Finset.empty_val, Multiset.map_zero,
    map_zero]

/-- Every used label has positive content. -/
theorem skewContent_entry_pos {α ν : YoungDiagram} (T : SkewFilling α ν)
    (p : skewCells α ν) : 0 < skewContent T (T p) := by
  apply Nat.pos_of_ne_zero
  apply Finsupp.mem_support_iff.mp
  rw [support_skewContent]
  exact Finset.mem_image.mpr ⟨p.val, p.property, skewEntry_cell T p⟩

end YoungDiagram
