import Schubert.Partitions.Skew.Word
import Mathlib.Data.Fintype.Pi

/-! # Finite Littlewood--Richardson skew tableaux

An LR tableau is a positive filling of the skew cells with containment,
semistandardness, prescribed content and lattice reading word. Its labels are bounded
by the height of the content diagram, making the carrier finite.

## Main results

* `LRTableau.entry_le` bounds every used positive label by the content height.
* `instFintypeLRTableau` supplies the finite type of LR tableaux.
* `card_lrTableau_self` counts the empty shape with empty content.
* `card_lrTableau_of_not_le` vanishes outside containment.

## Implementation notes

The carrier is a subtype of positive skew fillings. Containment is explicit, and the
content condition refers to zero-based row lengths after subtracting one from a label.
-/

noncomputable section

namespace YoungDiagram

/-- Positive semistandard skew tableaux of prescribed content and lattice reading word. -/
abbrev LRTableau (α β ν : YoungDiagram) :=
  {T : SkewFilling α ν // α ≤ ν ∧ SkewSemistandard T ∧
    (∀ x : ℕ+, skewContent T x = β.rowLen (x.val - 1)) ∧
      IsLatticeWord (skewReadingWord T)}

namespace LRTableau

variable {α β ν : YoungDiagram}

/-- The inner diagram of an LR tableau is contained in its outer diagram. -/
theorem contained (T : LRTableau α β ν) : α ≤ ν := T.property.1

/-- An LR tableau satisfies the standard row and column inequalities. -/
theorem semistandard (T : LRTableau α β ν) : SkewSemistandard T.val := T.property.2.1

/-- The number of occurrences of a positive label is the corresponding content row length. -/
theorem content (T : LRTableau α β ν) (x : ℕ+) :
    skewContent T.val x = β.rowLen (x.val - 1) := T.property.2.2.1 x

/-- Every prefix of the reading word of an LR tableau is lattice. -/
theorem lattice (T : LRTableau α β ν) : IsLatticeWord (skewReadingWord T.val) :=
  T.property.2.2.2

/-- Every label used by an LR tableau is at most the height of its content diagram. -/
theorem entry_le (T : LRTableau α β ν) (p : skewCells α ν) :
    (T.val p).val ≤ β.colLen 0 := by
  have hp := skewContent_entry_pos T.val p
  rw [T.content] at hp
  by_contra h
  have hi : β.colLen 0 ≤ (T.val p).val - 1 := by omega
  rw [YoungDiagram.rowLen_eq_zero_of_colLen_le hi] at hp
  omega

/-- Equality of all individual cell entries determines an LR tableau. -/
@[ext] theorem ext {T U : LRTableau α β ν} (h : ∀ p, T.val p = U.val p) : T = U :=
  Subtype.ext (funext h)

end LRTableau

/-- The content bound embeds LR tableaux into a finite set of bounded fillings. -/
instance instFiniteLRTableau (α β ν : YoungDiagram) : Finite (LRTableau α β ν) := by
  let f : LRTableau α β ν → (skewCells α ν → Fin (β.colLen 0)) :=
    fun T p => ⟨(T.val p).val - 1, by have := T.entry_le p; have := (T.val p).pos; omega⟩
  apply Finite.of_injective f
  intro T U h
  apply LRTableau.ext
  intro p
  apply PNat.natPred_injective
  exact congrArg (fun g => (g p).val) h

/-- LR tableaux form a finite type, including empty shapes and empty content. -/
instance instFintypeLRTableau (α β ν : YoungDiagram) : Fintype (LRTableau α β ν) :=
  Fintype.ofFinite _

/-- The empty skew shape with empty content has exactly one filling. -/
instance instUniqueLRTableauSelf (α : YoungDiagram) : Unique (LRTableau α ⊥ α) where
  default := ⟨fun _ => 1, by
    refine ⟨le_rfl, ?_, ?_, ?_⟩
    · constructor
      · intro p
        have h : False := by simpa only [skewCells_self, Finset.notMem_empty] using p.property
        exact h.elim
      · intro p
        have h : False := by simpa only [skewCells_self, Finset.notMem_empty] using p.property
        exact h.elim
    · intro x
      rw [skewContent_self, Finsupp.zero_apply, YoungDiagram.rowLen_bot]
    · rw [skewReadingWord_self]
      exact isLatticeWord_nil⟩
  uniq T := by
    apply LRTableau.ext
    intro p
    have h : False := by simpa only [skewCells_self, Finset.notMem_empty] using p.property
    exact h.elim

/-- Empty skew shape and empty content have tableau count one. -/
theorem card_lrTableau_self (α : YoungDiagram) :
    Fintype.card (LRTableau α ⊥ α) = 1 := Fintype.card_unique

/-- There are no LR tableaux when the inner diagram is not contained in the outer diagram. -/
theorem lrTableau_isEmpty_of_not_le {α β ν : YoungDiagram} (h : ¬α ≤ ν) :
    IsEmpty (LRTableau α β ν) := ⟨fun T => h T.contained⟩

/-- The tableau count vanishes outside containment. -/
theorem card_lrTableau_of_not_le {α β ν : YoungDiagram} (h : ¬α ≤ ν) :
    Fintype.card (LRTableau α β ν) = 0 := by
  have := lrTableau_isEmpty_of_not_le (β := β) h
  exact Fintype.card_of_isEmpty

/-- An empty skew shape admits no tableau with nonempty content. -/
theorem lrTableau_isEmpty_self {α β : YoungDiagram} (hβ : β ≠ ⊥) :
    IsEmpty (LRTableau α β α) := by
  refine ⟨fun T => ?_⟩
  have h := T.content 1
  rw [skewContent_self, Finsupp.zero_apply] at h
  have hz : β.rowLen 0 = 0 := by simpa using h.symm
  exact hβ ((YoungDiagram.eq_bot_iff_rowLen_zero β).mpr hz)

end YoungDiagram
