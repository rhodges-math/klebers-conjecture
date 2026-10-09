import KlebersConjecture.Partitions.Basic

/-!
# Rectangular Young diagrams and complements

Rectangular complementation reverses the rows and subtracts their lengths from the width.

## Main results

* `YoungDiagram.rectComplement_rectComplement`: complementation is an involution.
* `YoungDiagram.card_add_rectComplement`: complementary sizes add to the rectangle's size.
* `YoungDiagram.mem_rectComplement_iff`: cells are rotated missing cells of the rectangle.

## Implementation notes

The first rectangle parameter is its height and the second its width. Complement is a
total operation; its row formula is asserted under containment in the rectangle.
-/

namespace YoungDiagram

/-- The rectangle with `a` rows and `b` columns. -/
def rectangle (a b : ℕ) : YoungDiagram :=
  ofRowLensFin (fun _ : Fin a => b) antitone_const

/-- The length of every row of a rectangle, including rows outside it. -/
@[simp] theorem rowLen_rectangle (a b i : ℕ) :
    (rectangle a b).rowLen i = if i < a then b else 0 := by
  by_cases hi : i < a
  · simpa [rectangle, hi] using rowLen_ofRowLensFin
      (fun _ : Fin a => b) antitone_const ⟨i, hi⟩
  · simpa [rectangle, hi] using rowLen_ofRowLensFin_eq_zero_of_le
      (fun _ : Fin a => b) antitone_const (Nat.le_of_not_gt hi)

/-- A rectangle contains exactly the cells within its two coordinate bounds. -/
@[simp] theorem mem_rectangle (a b i j : ℕ) :
    (i, j) ∈ rectangle a b ↔ i < a ∧ j < b := by
  rw [mem_iff_lt_rowLen, rowLen_rectangle]
  split_ifs <;> simp_all

/-- A rectangle contains `a * b` cells. -/
@[simp] theorem card_rectangle (a b : ℕ) : (rectangle a b).card = a * b := by
  simp [rectangle, card_ofRowLensFin]

/-- Containment in a rectangle bounds every row length. -/
theorem rowLen_le_of_le_rectangle {a b : ℕ} {μ : YoungDiagram}
    (hμ : μ ≤ rectangle a b) (i : ℕ) : μ.rowLen i ≤ b := by
  have h := rowLen_le_of_le hμ i
  rw [rowLen_rectangle] at h
  split_ifs at h <;> omega

/-- A contained diagram has no rows past the rectangle. -/
theorem rowLen_eq_zero_of_le_rectangle {a b i : ℕ} {μ : YoungDiagram}
    (hμ : μ ≤ rectangle a b) (hi : a ≤ i) : μ.rowLen i = 0 := by
  have h := rowLen_le_of_le hμ i
  simpa [rowLen_rectangle, Nat.not_lt.mpr hi] using h

/-- Containment in a rectangle bounds the number of rows. -/
theorem colLen_le_of_le_rectangle {a b : ℕ} {μ : YoungDiagram}
    (hμ : μ ≤ rectangle a b) : μ.colLen 0 ≤ a := by
  by_contra h
  have hc : (a, 0) ∈ μ := mem_iff_lt_colLen.mpr (by omega)
  have := (mem_rectangle a b a 0).mp (hμ hc)
  omega

/-- Subtracting reversed row lengths gives a weakly decreasing family. -/
theorem rectComplementRows_antitone (a b : ℕ) (μ : YoungDiagram) :
    Antitone (fun i : Fin a => b - μ.rowLen i.rev) := by
  intro i j hij
  apply Nat.sub_le_sub_left
  apply μ.rowLen_anti
  simp only [Fin.val_rev]
  omega

/-- Reverse rows and subtract their lengths from the width, with natural subtraction. -/
def rectComplement (a b : ℕ) (μ : YoungDiagram) : YoungDiagram :=
  ofRowLensFin (fun i : Fin a => b - μ.rowLen i.rev) (rectComplementRows_antitone a b μ)

/-- The rows of a rectangular complement, including rows outside the rectangle. -/
@[simp] theorem rowLen_rectComplement (a b : ℕ) (μ : YoungDiagram) (i : ℕ) :
    (rectComplement a b μ).rowLen i = if i < a then b - μ.rowLen (a - 1 - i) else 0 := by
  by_cases hi : i < a
  · have hsub : a - (i + 1) = a - 1 - i := by omega
    simpa [rectComplement, hi, Fin.val_rev, hsub] using rowLen_ofRowLensFin
      (fun j : Fin a => b - μ.rowLen j.rev) (rectComplementRows_antitone a b μ) ⟨i, hi⟩
  · simpa [rectComplement, hi] using rowLen_ofRowLensFin_eq_zero_of_le
      (fun j : Fin a => b - μ.rowLen j.rev) (rectComplementRows_antitone a b μ)
      (Nat.le_of_not_gt hi)

/-- A rectangular complement is contained in its rectangle. -/
theorem rectComplement_le_rectangle (a b : ℕ) (μ : YoungDiagram) :
    rectComplement a b μ ≤ rectangle a b := by
  apply le_of_forall_rowLen_le
  intro i
  simp only [rowLen_rectComplement, rowLen_rectangle]
  split_ifs <;> omega

/-- Two rectangular complementations recover a contained diagram. -/
@[simp] theorem rectComplement_rectComplement {a b : ℕ} {μ : YoungDiagram}
    (hμ : μ ≤ rectangle a b) :
    rectComplement a b (rectComplement a b μ) = μ := by
  apply rowLen_injective
  funext i
  by_cases hi : i < a
  · have hrev : a - 1 - i < a := by omega
    have htwice : a - 1 - (a - 1 - i) = i := by omega
    have hbound := rowLen_le_of_le_rectangle hμ i
    simp only [rowLen_rectComplement, hi, hrev, htwice, ite_true]
    omega
  · simp [rowLen_rectComplement, hi,
      rowLen_eq_zero_of_le_rectangle hμ (Nat.le_of_not_gt hi)]

/-- A cell of the complement is a rotated missing cell, with both bounds explicit. -/
theorem mem_rectComplement_iff {a b i j : ℕ} {μ : YoungDiagram}
    (hμ : μ ≤ rectangle a b) :
    (i, j) ∈ rectComplement a b μ ↔
      i < a ∧ j < b ∧ (a - 1 - i, b - 1 - j) ∉ μ := by
  rw [mem_iff_lt_rowLen, rowLen_rectComplement]
  by_cases hi : i < a
  · have hbound := rowLen_le_of_le_rectangle hμ (a - 1 - i)
    simp only [hi, ite_true, true_and, mem_iff_lt_rowLen]
    omega
  · simp [hi]

/-- Complementary sizes sum to the size of their rectangle. -/
theorem card_add_rectComplement {a b : ℕ} {μ : YoungDiagram}
    (hμ : μ ≤ rectangle a b) : μ.card + (rectComplement a b μ).card = a * b := by
  have hcard : μ.card = ∑ i : Fin a, μ.rowLen i := by
    rw [card_eq_sum_range_rowLen μ (colLen_le_of_le_rectangle hμ)]
    exact (Fin.sum_univ_eq_sum_range (fun i => μ.rowLen i) a).symm
  have hrev : (∑ i : Fin a, μ.rowLen i.rev) = ∑ i : Fin a, μ.rowLen i :=
    Equiv.sum_comp Fin.revPerm (fun i : Fin a => μ.rowLen i)
  have hcompcard : (rectComplement a b μ).card =
      ∑ i : Fin a, (b - μ.rowLen i.rev) := by
    simp only [rectComplement, card_ofRowLensFin]
  rw [hcard, hcompcard, ← hrev, ← Finset.sum_add_distrib]
  have hterm : ∀ i : Fin a, μ.rowLen i.rev + (b - μ.rowLen i.rev) = b := by
    intro i
    have := rowLen_le_of_le_rectangle hμ i.rev
    omega
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id]

end YoungDiagram

