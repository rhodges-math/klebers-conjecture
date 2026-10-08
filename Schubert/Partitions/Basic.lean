import TauCeti.Combinatorics.Young.OfRowLens
import Mathlib.Algebra.Order.Monoid.Defs

/-! # Componentwise addition of Young diagrams

Young diagrams form an ordered cancellative additive commutative monoid by adding
corresponding row lengths.

## Main results

* `YoungDiagram.rowLen_add` describes the rows of a sum.
* `YoungDiagram.card_add` describes its size.
* `YoungDiagram.colLen_add` describes its number of rows.

## Implementation notes

Row indices start at zero. Addition is componentwise addition of row lengths, and its identity
is the existing bottom diagram. This extends Mathlib's containment order without changing it.
-/

namespace YoungDiagram

/-- Every row of the empty diagram has length zero. -/
@[simp]
theorem rowLen_bot (i : ℕ) : (⊥ : YoungDiagram).rowLen i = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro h
  exact notMem_bot (i, 0) (mem_iff_lt_rowLen.mpr h)

/-- Every column of the empty diagram has length zero. -/
@[simp]
theorem colLen_bot (j : ℕ) : (⊥ : YoungDiagram).colLen j = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro h
  exact notMem_bot (0, j) (mem_iff_lt_colLen.mpr h)

/-- The additive identity is the empty Young diagram. -/
instance instZero : Zero YoungDiagram := ⟨⊥⟩

/-- The zero diagram is the bottom element for containment. -/
theorem zero_eq_bot : (0 : YoungDiagram) = ⊥ := rfl

/-- Every row of the additive identity has length zero. -/
@[simp]
theorem rowLen_zero (i : ℕ) : (0 : YoungDiagram).rowLen i = 0 := rowLen_bot i

/-- Every column of the additive identity has length zero. -/
@[simp]
theorem colLen_zero (j : ℕ) : (0 : YoungDiagram).colLen j = 0 := colLen_bot j

/-- Addition of Young diagrams adds their corresponding row lengths. -/
instance instAdd : Add YoungDiagram where
  add α β := ofRowLensFin
    (fun i : Fin (max (α.colLen 0) (β.colLen 0)) => α.rowLen i + β.rowLen i)
    (fun i j h => Nat.add_le_add (α.rowLen_anti i j h) (β.rowLen_anti i j h))

/-- The length of each row of a sum is the sum of the two row lengths. -/
@[simp]
theorem rowLen_add (α β : YoungDiagram) (i : ℕ) :
    (α + β).rowLen i = α.rowLen i + β.rowLen i := by
  change (ofRowLensFin
    (fun k : Fin (max (α.colLen 0) (β.colLen 0)) => α.rowLen k + β.rowLen k)
    _).rowLen i = _
  by_cases hi : i < max (α.colLen 0) (β.colLen 0)
  · exact rowLen_ofRowLensFin _ _ ⟨i, hi⟩
  · have hz := rowLen_ofRowLensFin_eq_zero_of_le
      (fun k : Fin (max (α.colLen 0) (β.colLen 0)) => α.rowLen k + β.rowLen k)
      (fun j k h => Nat.add_le_add (α.rowLen_anti j k h) (β.rowLen_anti j k h))
      (Nat.le_of_not_lt hi)
    rw [rowLen_eq_zero_of_colLen_le (by omega : α.colLen 0 ≤ i),
      rowLen_eq_zero_of_colLen_le (by omega : β.colLen 0 ≤ i)]
    exact hz

/-- Componentwise addition gives Young diagrams a cancellative additive commutative monoid. -/
instance instAddCancelCommMonoid : AddCancelCommMonoid YoungDiagram where
  add_assoc α β γ := rowLen_injective (by ext i; simp [Nat.add_assoc])
  zero_add α := rowLen_injective (by ext i; simp)
  add_zero α := rowLen_injective (by ext i; simp)
  add_comm α β := rowLen_injective (by ext i; simp [Nat.add_comm])
  nsmul := nsmulRec
  add_left_cancel α β γ h := rowLen_injective (by
    funext i
    have hr := congrArg (fun μ : YoungDiagram => μ.rowLen i) h
    simpa only [rowLen_add, Nat.add_left_cancel_iff] using hr)

/-- Rowwise addition preserves and reflects Young-diagram containment. -/
instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid YoungDiagram where
  add_le_add_left α β h γ := by
    apply le_of_forall_rowLen_le
    intro i
    simpa only [rowLen_add] using Nat.add_le_add_right (rowLen_le_of_le h i) (γ.rowLen i)
  le_of_add_le_add_left α β γ h := by
    apply le_of_forall_rowLen_le
    intro i
    have hr := rowLen_le_of_le h i
    simpa only [rowLen_add, Nat.add_le_add_iff_left] using hr

/-- A diagram is empty precisely when it has no rows. -/
theorem eq_bot_iff_colLen_zero (μ : YoungDiagram) : μ = ⊥ ↔ μ.colLen 0 = 0 := by
  constructor
  · rintro rfl
    exact colLen_bot 0
  · intro h
    apply rowLen_injective
    funext i
    rw [rowLen_bot, rowLen_eq_zero_of_colLen_le (by omega)]

/-- A diagram is empty precisely when its first row is empty. -/
theorem eq_bot_iff_rowLen_zero (μ : YoungDiagram) : μ = ⊥ ↔ μ.rowLen 0 = 0 := by
  constructor
  · rintro rfl
    exact rowLen_bot 0
  · intro h
    apply rowLen_injective
    funext i
    rw [rowLen_bot]
    have := μ.rowLen_anti 0 i (Nat.zero_le i)
    omega

/-- The first column of a sum reaches as far as the longer first column. -/
@[simp]
theorem colLen_add (α β : YoungDiagram) :
    (α + β).colLen 0 = max (α.colLen 0) (β.colLen 0) := by
  apply Nat.le_antisymm
  · by_contra h
    have hm : (max (α.colLen 0) (β.colLen 0), 0) ∈ α + β :=
      mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
    rw [mem_iff_lt_rowLen, rowLen_add,
      rowLen_eq_zero_of_colLen_le (Nat.le_max_left _ _),
      rowLen_eq_zero_of_colLen_le (Nat.le_max_right _ _)] at hm
    omega
  · apply max_le
    · by_contra h
      have hm : ((α + β).colLen 0, 0) ∈ α :=
        mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
      have hp := mem_iff_lt_rowLen.mp hm
      have hz := rowLen_eq_zero_of_colLen_le (μ := α + β) (le_refl ((α + β).colLen 0))
      rw [rowLen_add] at hz
      omega
    · by_contra h
      have hm : ((α + β).colLen 0, 0) ∈ β :=
        mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
      have hp := mem_iff_lt_rowLen.mp hm
      have hz := rowLen_eq_zero_of_colLen_le (μ := α + β) (le_refl ((α + β).colLen 0))
      rw [rowLen_add] at hz
      omega

/-- The size of a componentwise sum is the sum of the sizes. -/
@[simp]
theorem card_add (α β : YoungDiagram) : (α + β).card = α.card + β.card := by
  rw [card_eq_sum_range_rowLen (α + β) (N := max (α.colLen 0) (β.colLen 0)) (by simp),
    card_eq_sum_range_rowLen α (Nat.le_max_left (α.colLen 0) (β.colLen 0)),
    card_eq_sum_range_rowLen β (Nat.le_max_right (α.colLen 0) (β.colLen 0))]
  simp only [rowLen_add, Finset.sum_add_distrib]

/-- The left summand is contained in a componentwise sum. -/
protected theorem le_self_add (α β : YoungDiagram) : α ≤ α + β := by
  apply le_of_forall_rowLen_le
  intro i
  simp

/-- The right summand is contained in a componentwise sum. -/
protected theorem le_add_self (α β : YoungDiagram) : β ≤ α + β := by
  apply le_of_forall_rowLen_le
  intro i
  simp

end YoungDiagram
