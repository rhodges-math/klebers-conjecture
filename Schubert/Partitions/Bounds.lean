import Schubert.Partitions.Rectangle
import TauCeti.Combinatorics.Young.Partitions

/-! # Size bounds and finite sets of Young diagrams

Every row and column has at most as many cells as the diagram. A size bound therefore
places a diagram inside a finite rectangle, giving finiteness of the diagrams of bounded size.

## Main results

* `YoungDiagram.le_rectangle_of_card_le` bounds both coordinates by the size bound.
* `YoungDiagram.finite_card_le` gives finiteness under a size bound.
* `YoungDiagram.finite_card_eq` gives finiteness at an exact size.

## Implementation notes

Fixed-size finiteness is transported through Tau Ceti's equivalence with `Nat.Partition`.
Containment bounds use the existing Young-diagram order.
-/

namespace YoungDiagram

/-- Diagrams of a fixed size form a finite type through the standard partition equivalence. -/
instance instFintypeCardEq (n : ℕ) : Fintype {μ : YoungDiagram // μ.card = n} :=
  Fintype.ofEquiv n.Partition (TauCeti.partitionEquivYoungDiagram n)

/-- The length of a row is at most the number of cells of the diagram. -/
theorem rowLen_le_card (μ : YoungDiagram) (i : ℕ) : μ.rowLen i ≤ μ.card := by
  rw [rowLen_eq_card]
  exact Finset.card_filter_le _ _

/-- The length of a column is at most the number of cells of the diagram. -/
theorem colLen_le_card (μ : YoungDiagram) (j : ℕ) : μ.colLen j ≤ μ.card := by
  simpa only [rowLen_transpose, card_transpose] using rowLen_le_card μ.transpose j

/-- A diagram of size at most `d` lies inside the square of side length `d`. -/
theorem le_rectangle_of_card_le {μ : YoungDiagram} {d : ℕ} (hμ : μ.card ≤ d) :
    μ ≤ rectangle d d := by
  intro c hc
  obtain ⟨i, j⟩ := c
  apply (mem_rectangle d d i j).mpr
  exact ⟨(mem_iff_lt_colLen.mp hc).trans_le ((colLen_le_card μ j).trans hμ),
    (mem_iff_lt_rowLen.mp hc).trans_le ((rowLen_le_card μ i).trans hμ)⟩

/-- Every diagram lies inside the square whose side length is its size. -/
theorem le_rectangle_card (μ : YoungDiagram) : μ ≤ rectangle μ.card μ.card :=
  le_rectangle_of_card_le le_rfl

/-- There are finitely many Young diagrams of size at most `d`. -/
theorem finite_card_le (d : ℕ) : {μ : YoungDiagram | μ.card ≤ d}.Finite := by
  apply (finite_Iic (rectangle d d)).subset
  intro μ hμ
  exact le_rectangle_of_card_le hμ

/-- There are finitely many Young diagrams of any fixed size. -/
theorem finite_card_eq (d : ℕ) : {μ : YoungDiagram | μ.card = d}.Finite := by
  apply (finite_card_le d).subset
  intro μ hμ
  exact Nat.le_of_eq hμ

end YoungDiagram
