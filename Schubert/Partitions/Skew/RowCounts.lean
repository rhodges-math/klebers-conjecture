import Schubert.Partitions.Skew.LRTableau
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Row multiplicities of positive skew fillings

The second count index is zero based: index i counts the positive label i+1.
Row counts recover both the content and the counts in complete row prefixes.

## Main results

* `skewRowCount_eq_card` counts a filtered interval of columns.
* `skewContent_eq_sum_rows` recovers content from row counts.
* `count_skewRowsWord` counts labels in a complete row prefix.

## Implementation notes

`skewRowCount T r i` counts label `i + 1` in row `r`. Both count indices start at zero.
-/

noncomputable section

namespace YoungDiagram

open scoped Classical

/-- The multiplicity of positive label i+1 in skew row r. -/
def skewRowCount {α ν : YoungDiagram} (T : SkewFilling α ν) (r i : ℕ) : ℕ :=
  (skewRowWord T r).count (Nat.succPNat i)

/-- Row multiplicities count the columns inside the skew interval with the given label. -/
theorem skewRowCount_eq_card {α ν : YoungDiagram} (T : SkewFilling α ν) (r i : ℕ) :
    skewRowCount T r i = ((Finset.range (ν.rowLen r)).filter fun c =>
      α.rowLen r ≤ c ∧ skewEntry T r c = Nat.succPNat i).card := by
  let l := List.range' (α.rowLen r) (ν.rowLen r - α.rowLen r)
  have hn : l.Nodup := List.nodup_range'
  have he : (l.toFinset.filter fun c => skewEntry T r c = Nat.succPNat i) =
      (Finset.range (ν.rowLen r)).filter (fun c =>
        α.rowLen r ≤ c ∧ skewEntry T r c = Nat.succPNat i) := by
    ext c
    dsimp [l]
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_range', Finset.mem_range]
    constructor
    · rintro ⟨⟨j, hj, hc⟩, he⟩
      exact ⟨by omega, by omega, he⟩
    · rintro ⟨hc, hl, he⟩
      exact ⟨⟨c - α.rowLen r, by omega, by omega⟩, he⟩
  rw [← he, hn.card_eq_countP]
  simp only [skewRowCount, skewRowWord, List.count, List.countP_map, List.countP_reverse]
  rfl

/-- A row at or below the height boundary has no skew entries. -/
@[simp] theorem skewRowCount_eq_zero {α ν : YoungDiagram} (T : SkewFilling α ν)
    (r i : ℕ) (hr : ν.colLen 0 ≤ r) : skewRowCount T r i = 0 := by
  rw [skewRowCount_eq_card, YoungDiagram.rowLen_eq_zero_of_colLen_le hr]
  simp

/-- Counts in a complete row prefix are sums of its row multiplicities. -/
theorem count_skewRowsWord {α ν : YoungDiagram} (T : SkewFilling α ν) (r i : ℕ) :
    (skewRowsWord T r).count (Nat.succPNat i) =
      ∑ t ∈ Finset.range r, skewRowCount T t i := by
  induction r with
  | zero => simp [skewRowsWord]
  | succ r ih =>
    simp only [skewRowsWord, List.count_append, ih, Finset.sum_range_succ]
    rfl

private theorem row_fiber_card {α ν : YoungDiagram} (T : SkewFilling α ν) (r i : ℕ) :
    (((skewCells α ν).filter fun p => skewEntry T p.1 p.2 = Nat.succPNat i).filter
      fun p => p.1 = r).card = skewRowCount T r i := by
  rw [skewRowCount_eq_card]
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    obtain ⟨hp, hr⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
    have hm := (mem_skewCells _ _ _ _).mp hp
    rw [hr] at hm he
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm.2, hm.1, he⟩
  · intro p hp q hq he
    have hp := (Finset.mem_filter.mp hp).2
    have hq := (Finset.mem_filter.mp hq).2
    exact Prod.ext (hp.trans hq.symm) he
  · intro c hc
    obtain ⟨hc, hl, he⟩ := Finset.mem_filter.mp hc
    refine ⟨(r, c), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨(mem_skewCells _ _ _ _).mpr ⟨hl, Finset.mem_range.mp hc⟩, he⟩, rfl⟩

/-- Content is the sum of multiplicities over all rows of the outer diagram. -/
theorem skewContent_eq_sum_rows {α ν : YoungDiagram} (T : SkewFilling α ν) (i : ℕ) :
    skewContent T (Nat.succPNat i) =
      ∑ r ∈ Finset.range (ν.colLen 0), skewRowCount T r i := by
  rw [skewContent_apply]
  simp_rw [← row_fiber_card T]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  symm
  apply Finset.filter_true_of_mem
  intro p hp
  have hm := (Finset.mem_filter.mp hp).1
  have hν := (Finset.mem_sdiff.mp hm).1
  have hν' : p ∈ ν := by simpa only [YoungDiagram.mem_cells] using hν
  exact Finset.mem_range.mpr ((YoungDiagram.mem_iff_lt_colLen.mp
    hν').trans_le (ν.colLen_anti 0 p.2 (Nat.zero_le _)))

/-- The row counts of an LR tableau sum to its prescribed content row length. -/
theorem LRTableau.sum_skewRowCount {α β ν : YoungDiagram} (T : LRTableau α β ν) (i : ℕ) :
    ∑ r ∈ Finset.range (ν.colLen 0), skewRowCount T.val r i = β.rowLen i := by
  rw [← skewContent_eq_sum_rows, T.content]
  rfl

end YoungDiagram
