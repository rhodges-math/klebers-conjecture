import KlebersConjecture.Partitions.Rectangle

/-!
# Gap vectors and their tail diagrams

A gap vector records differences between opposite rows. Its tail diagram has reversed
width-minus-gap rows, preceded by a full-width row when the rectangle has odd height.

## Main results

* `validGap_gap`: a contained diagram has a valid gap vector.
* `rowLen_gapShape_gap`: reversed gaps prescribe the rows after the parity prefix.
* `gapShape_le_rectangle`: the tail diagram fits in the remaining rectangle.
-/

noncomputable section

namespace ComplementaryProducts

/-- Differences between the first half of the rows and their opposite rows. -/
def gap (a : ℕ) (μ : YoungDiagram) : Fin (a / 2) → ℕ :=
  fun i => μ.rowLen i.val - μ.rowLen (a - 1 - i.val)

/-- A valid rectangular gap vector is weakly decreasing and bounded by the width. -/
def ValidGap (a b : ℕ) (g : Fin (a / 2) → ℕ) : Prop :=
  Antitone g ∧ ∀ i, g i ≤ b

/-- Every gap entry is the difference of the corresponding opposite row lengths. -/
theorem gap_apply (a : ℕ) (μ : YoungDiagram) (i : Fin (a / 2)) :
    gap a μ i = μ.rowLen i.val - μ.rowLen (a - 1 - i.val) := rfl

/-- Opposite-row differences are weakly decreasing. -/
theorem gap_antitone (a : ℕ) (μ : YoungDiagram) : Antitone (gap a μ) := by
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  have ht := μ.rowLen_anti i.val j.val hij'
  have hb := μ.rowLen_anti (a - 1 - j.val) (a - 1 - i.val) (by omega)
  unfold gap
  omega

/-- Each opposite-row difference of a contained diagram is at most the width. -/
theorem gap_le_width {a b : ℕ} {μ : YoungDiagram}
    (hμ : μ ≤ YoungDiagram.rectangle a b) (i : Fin (a / 2)) : gap a μ i ≤ b :=
  (Nat.sub_le _ _).trans (YoungDiagram.rowLen_le_of_le_rectangle hμ i.val)

/-- Gaps of a diagram contained in a rectangle satisfy the validity conditions. -/
theorem validGap_gap {a b : ℕ} {μ : YoungDiagram}
    (hμ : μ ≤ YoungDiagram.rectangle a b) : ValidGap a b (gap a μ) :=
  ⟨gap_antitone a μ, gap_le_width hμ⟩

/-- The prescribed rows of the gap shape, with an odd-height parity prefix. -/
private def gapRows (a b : ℕ) (g : Fin (a / 2) → ℕ) (i : Fin (a - a / 2)) : ℕ :=
  if hi : i.val < a % 2 then b else
    b - g ⟨a - a / 2 - 1 - i.val, by have := i.isLt; omega⟩

private theorem gapRows_antitone {a b : ℕ} {g : Fin (a / 2) → ℕ}
    (hg : ValidGap a b g) : Antitone (gapRows a b g) := by
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  unfold gapRows
  split_ifs with hi hj
  · exact le_rfl
  · omega
  · exact Nat.sub_le _ _
  · apply Nat.sub_le_sub_left
    apply hg.1
    change a - a / 2 - 1 - j.val ≤ a - a / 2 - 1 - i.val
    omega

/-- The tail diagram prescribed by a valid gap vector, including heights zero and one. -/
def gapShape (a b : ℕ) (g : Fin (a / 2) → ℕ) (hg : ValidGap a b g) : YoungDiagram :=
  YoungDiagram.ofRowLensFin (gapRows a b g) (gapRows_antitone hg)

/-- The gap shape is independent of the proof of validity. -/
theorem gapShape_proof_irrel (a b : ℕ) (g : Fin (a / 2) → ℕ)
    (hg hg' : ValidGap a b g) : gapShape a b g hg = gapShape a b g hg' := rfl

/-- Every prescribed row has the parity-prefix or reversed-gap formula. -/
theorem rowLen_gapShape (a b : ℕ) (g : Fin (a / 2) → ℕ) (hg : ValidGap a b g)
    (i : Fin (a - a / 2)) :
    (gapShape a b g hg).rowLen i.val =
      if hi : i.val < a % 2 then b else
        b - g ⟨a - a / 2 - 1 - i.val, by have := i.isLt; omega⟩ :=
  YoungDiagram.rowLen_ofRowLensFin _ _ i

/-- Rows past the remaining height are empty. -/
theorem rowLen_gapShape_eq_zero (a b : ℕ) (g : Fin (a / 2) → ℕ)
    (hg : ValidGap a b g) {i : ℕ} (hi : a - a / 2 ≤ i) :
    (gapShape a b g hg).rowLen i = 0 :=
  YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le _ _ hi

/-- The prefix in odd height is a row of the full rectangle width. -/
theorem rowLen_gapShape_prefix (a b : ℕ) (g : Fin (a / 2) → ℕ)
    (hg : ValidGap a b g) {i : ℕ} (hi : i < a % 2) :
    (gapShape a b g hg).rowLen i = b := by
  have hil : i < a - a / 2 := by omega
  simpa only [dite_eq_left hi] using rowLen_gapShape a b g hg ⟨i, hil⟩

/-- Reversed width-minus-gap entries form the rows after the parity prefix. -/
theorem rowLen_gapShape_gap (a b : ℕ) (g : Fin (a / 2) → ℕ)
    (hg : ValidGap a b g) (i : Fin (a / 2)) :
    (gapShape a b g hg).rowLen (a % 2 + i.val) = b - g i.rev := by
  have hil : a % 2 + i.val < a - a / 2 := by have := i.isLt; omega
  have hn : ¬a % 2 + i.val < a % 2 := by omega
  rw [rowLen_gapShape a b g hg ⟨a % 2 + i.val, hil⟩, dite_eq_right hn]
  congr 2
  apply Fin.ext
  simp only [Fin.val_rev]
  omega

/-- In even height every remaining row is a reversed width-minus-gap entry. -/
theorem rowLen_gapShape_even {a : ℕ} (b : ℕ) (g : Fin (a / 2) → ℕ)
    (hg : ValidGap a b g) (ha : a % 2 = 0) (i : Fin (a / 2)) :
    (gapShape a b g hg).rowLen i.val = b - g i.rev := by
  simpa only [ha, zero_add] using rowLen_gapShape_gap a b g hg i

/-- In odd height reversed width-minus-gap entries follow the full-width first row. -/
theorem rowLen_gapShape_odd {a : ℕ} (b : ℕ) (g : Fin (a / 2) → ℕ)
    (hg : ValidGap a b g) (ha : a % 2 = 1) (i : Fin (a / 2)) :
    (gapShape a b g hg).rowLen (i.val + 1) = b - g i.rev := by
  simpa only [ha, Nat.add_comm 1] using rowLen_gapShape_gap a b g hg i

/-- The number of rows is bounded by the remaining rectangle height. -/
theorem colLen_gapShape_le (a b : ℕ) (g : Fin (a / 2) → ℕ) (hg : ValidGap a b g) :
    (gapShape a b g hg).colLen 0 ≤ a - a / 2 :=
  YoungDiagram.colLen_zero_ofRowLensFin_le _ _

/-- The gap shape is contained in the rectangle with the remaining height. -/
theorem gapShape_le_rectangle (a b : ℕ) (g : Fin (a / 2) → ℕ)
    (hg : ValidGap a b g) : gapShape a b g hg ≤ YoungDiagram.rectangle (a - a / 2) b := by
  apply YoungDiagram.le_of_forall_rowLen_le
  intro i
  rw [YoungDiagram.rowLen_rectangle]
  split_ifs with hi
  · rw [rowLen_gapShape a b g hg ⟨i, hi⟩]
    split_ifs <;> omega
  · rw [rowLen_gapShape_eq_zero a b g hg (Nat.le_of_not_lt hi)]

/-- The size is bounded by the area of the remaining rectangle. -/
theorem card_gapShape_le (a b : ℕ) (g : Fin (a / 2) → ℕ) (hg : ValidGap a b g) :
    (gapShape a b g hg).card ≤ (a - a / 2) * b := by
  have h := Finset.card_le_card
    (YoungDiagram.cells_subset_iff.mpr (gapShape_le_rectangle a b g hg))
  change (gapShape a b g hg).card ≤ (YoungDiagram.rectangle (a - a / 2) b).card at h
  simpa only [YoungDiagram.card_rectangle] using h

/-- At height zero the gap shape is empty. -/
theorem gapShape_zero (b : ℕ) (g : Fin (0 / 2) → ℕ) (hg : ValidGap 0 b g) :
    gapShape 0 b g hg = ⊥ := by
  apply YoungDiagram.rowLen_injective
  funext i
  rw [YoungDiagram.rowLen_bot, rowLen_gapShape_eq_zero 0 b g hg (by omega)]

/-- At height one the gap shape is the single full-width row. -/
theorem gapShape_one (b : ℕ) (g : Fin (1 / 2) → ℕ) (hg : ValidGap 1 b g) :
    gapShape 1 b g hg = YoungDiagram.rectangle 1 b := by
  apply YoungDiagram.rowLen_injective
  funext i
  rw [YoungDiagram.rowLen_rectangle]
  split_ifs with hi
  · exact rowLen_gapShape_prefix 1 b g hg (by omega)
  · exact rowLen_gapShape_eq_zero 1 b g hg (by omega)

end ComplementaryProducts
