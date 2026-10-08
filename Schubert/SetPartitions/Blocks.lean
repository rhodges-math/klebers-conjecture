import Schubert.SetPartitions.Basic

/-!
# Block counts of finite set partitions

The discrete partition has one block per element. A partition of a nonempty set has one
block exactly when it is indiscrete.

## Main results

* `Finpartition.card_parts_bot_univ`: the discrete block count.
* `Finpartition.card_parts_eq_one_iff`: one block characterizes the indiscrete partition.

## Implementation notes

Block counts apply to arbitrary finite index types. Positivity hypotheses are required
only for the one-block characterization; empty sets are handled separately.
-/

namespace Finpartition

open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The discrete partition has one block per argument. -/
theorem card_parts_bot_univ (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (⊥ : Finpartition (Finset.univ : Finset (ι))).parts.card = Fintype.card ι := by
  rw [card_bot, Finset.card_univ]

/-- Every partition of a nonempty finite set has a positive number of blocks. -/
theorem card_parts_pos (hk : 0 < Fintype.card ι)
    (P : Finpartition (Finset.univ : Finset (ι))) : 0 < P.parts.card := by
  apply Finset.card_pos.mpr
  apply P.parts_nonempty
  intro h
  have hi : (Finset.univ : Finset ι).Nonempty := Finset.card_pos.mp (by simpa using hk)
  rw [h] at hi
  exact Finset.not_nonempty_empty hi

/-- The indiscrete partition of a nonempty set has the full set as its only block. -/
theorem parts_top_univ (hk : 0 < Fintype.card ι) :
    (⊤ : Finpartition (Finset.univ : Finset (ι))).parts = {Finset.univ} := by
  apply Finset.Subset.antisymm (parts_top_subset _)
  obtain ⟨s, hs⟩ := Finset.card_pos.mp (card_parts_pos hk
    (⊤ : Finpartition (Finset.univ : Finset (ι))))
  have he : s = Finset.univ := Finset.mem_singleton.mp (parts_top_subset _ hs)
  simpa only [Finset.singleton_subset_iff, ← he] using hs

/-- The indiscrete partition of a nonempty set has exactly one block. -/
@[simp] theorem card_parts_top_univ (hk : 0 < Fintype.card ι) :
    (⊤ : Finpartition (Finset.univ : Finset (ι))).parts.card = 1 := by
  rw [parts_top_univ hk, Finset.card_singleton]

/-- A partition of a nonempty set has one block precisely when it is indiscrete. -/
theorem card_parts_eq_one_iff (hk : 0 < Fintype.card ι)
    (P : Finpartition (Finset.univ : Finset (ι))) : P.parts.card = 1 ↔ P = ⊤ := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := Finset.card_eq_one.mp h
    have he : s = Finset.univ := by simpa only [hs, Finset.sup_singleton, id_eq] using P.sup_parts
    apply Finpartition.ext
    rw [hs, he, parts_top_univ hk]
  · rintro rfl
    exact card_parts_top_univ hk

/-- The unique partition of the empty set has no blocks. -/
@[simp] theorem card_parts_univ_zero
    (P : Finpartition (Finset.univ : Finset (Fin 0))) : P.parts.card = 0 := by
  rw [eq_bot_univ_zero P, card_parts_bot_univ]
  exact Fintype.card_fin 0

end Finpartition
