import KlebersConjecture.Partitions.Skew.RowCounts
import Mathlib.Data.List.Pairwise

/-! # Lattice prefixes and skew row counts

In a weakly decreasing row word all occurrences of i+1 precede all occurrences of i.
The lattice condition is consequently determined by the prefix between these labels.

## Main results

* `isLatticeWord_append_iff` gives the row-prefix criterion for a decreasing list.
* `isLatticeWord_iff_skewRowCount` gives the criterion for semistandard skew fillings.

## Implementation notes

Row counts use zero-based labels while lattice words use positive labels. The row-prefix
criterion includes empty rows and rows beyond the outer diagram.
-/

noncomputable section

namespace YoungDiagram

open scoped Classical

/-- The beginning of a lattice concatenation is lattice. -/
theorem isLatticeWord_of_append {a b : List ℕ+} (h : IsLatticeWord (a ++ b)) :
    IsLatticeWord a := by
  intro k hk i
  have he := h k (by simp only [List.length_append]; omega) i
  rwa [List.take_append_of_le_length hk] at he

private theorem append_row_bound (b : List ℕ+) (hb : b.Pairwise (· ≥ ·))
    (a : List ℕ+) (h : IsLatticeWord (a ++ b)) (i : ℕ+) :
    a.count (i + 1) + b.count (i + 1) ≤ a.count i := by
  induction b generalizing a with
  | nil => simpa using h a.length (by simp) i
  | cons x b ih =>
    have hs := List.pairwise_cons.mp hb
    have ht : IsLatticeWord ((a ++ [x]) ++ b) := by
      simpa only [List.append_assoc, List.singleton_append] using h
    have hi := ih hs.2 (a ++ [x]) ht
    by_cases hx : x = i
    · have hn : i + 1 ∉ b := by
        intro hm
        have he := hs.1 _ hm
        rw [hx] at he
        have := i.pos
        have hv := show (i + 1).val ≤ i.val from he
        simp only [PNat.add_coe, PNat.one_coe] at hv
        omega
      have hz : b.count (i + 1) = 0 := List.count_eq_zero.mpr hn
      have ha := isLatticeWord_of_append h a.length le_rfl i
      have hne : i ≠ i + 1 := by
        intro he
        have he := congrArg PNat.val he
        simp only [PNat.add_coe, PNat.one_coe] at he
        omega
      simpa [List.count_cons, hx, hz, hne] using ha
    · simp only [List.count_append, List.count_cons, List.count_nil,
        beq_iff_eq, hx, ite_false, Nat.add_zero] at hi ⊢
      omega

/-- A decreasing appended row is lattice exactly when its next-label counts fit above it. -/
theorem isLatticeWord_append_iff (a b : List ℕ+) (hb : b.Pairwise (· ≥ ·)) :
    IsLatticeWord (a ++ b) ↔ IsLatticeWord a ∧
      ∀ i : ℕ+, a.count (i + 1) + b.count (i + 1) ≤ a.count i := by
  refine ⟨fun h => ⟨isLatticeWord_of_append h, append_row_bound b hb a h⟩, ?_⟩
  rintro ⟨ha, hc⟩ k hk i
  by_cases he : k ≤ a.length
  · rw [List.take_append_of_le_length he]
    exact ha k he i
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_ge he)
    rw [List.take_length_add_append, List.count_append, List.count_append]
    have hm := (List.take_sublist m b).count_le (i + 1)
    have hi := hc i
    omega

/-- A semistandard skew row is weakly decreasing in its reading order. -/
theorem pairwise_skewRowWord {α ν : YoungDiagram} (T : SkewFilling α ν)
    (h : SkewSemistandard T) (r : ℕ) : (skewRowWord T r).Pairwise (· ≥ ·) := by
  have hm : ∀ l : List ℕ, l.Pairwise (· ≤ ·) →
      (∀ c ∈ l, (r, c) ∈ skewCells α ν) →
      (l.map (skewEntry T r)).Pairwise (· ≤ ·) := by
    intro l
    induction l with
    | nil => simp
    | cons c l ih =>
      intro hl hc
      obtain ⟨hlc, hll⟩ := List.pairwise_cons.mp hl
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih hll (fun d hd => hc d (List.mem_cons_of_mem _ hd))⟩
      intro x hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      have hc' := hc c List.mem_cons_self
      have hd' := hc d (List.mem_cons_of_mem _ hd)
      have he := h.1 ⟨(r, c), hc'⟩ ⟨(r, d), hd'⟩ rfl (hlc d hd)
      simpa only [← skewEntry_cell T] using he
  rw [skewRowWord, List.map_reverse, List.pairwise_reverse]
  apply hm _ (List.pairwise_le_range' _)
  intro c hc
  obtain ⟨j, hj, he⟩ := List.mem_range'.mp hc
  apply (mem_skewCells _ _ _ _).mpr
  constructor <;> omega

/-- Adding empty rows beyond the outer height does not change a row-count sum. -/
theorem sum_skewRowCount_stable {α ν : YoungDiagram} (T : SkewFilling α ν)
    (r i : ℕ) (hr : ν.colLen 0 ≤ r) :
    (∑ t ∈ Finset.range r, skewRowCount T t i) =
      ∑ t ∈ Finset.range (ν.colLen 0), skewRowCount T t i := by
  symm
  apply Finset.sum_subset (Finset.range_mono hr)
  intro t ht hn
  apply skewRowCount_eq_zero
  simpa only [Finset.mem_range, not_lt] using hn

private theorem skewRowsWord_append {α ν : YoungDiagram} (T : SkewFilling α ν)
    {r s : ℕ} (h : r ≤ s) : ∃ l, skewRowsWord T s = skewRowsWord T r ++ l := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  induction m with
  | zero => exact ⟨[], by simp⟩
  | succ m ih =>
    obtain ⟨l, hl⟩ := ih (Nat.le_add_right _ _)
    exact ⟨l ++ skewRowWord T (r + m), by
      rw [← Nat.add_assoc, skewRowsWord, hl, List.append_assoc]⟩

/-- The skew lattice word condition is equivalent to its worst prefix in each row. -/
theorem isLatticeWord_iff_skewRowCount {α ν : YoungDiagram} (T : SkewFilling α ν)
    (hT : SkewSemistandard T) : IsLatticeWord (skewReadingWord T) ↔
      ∀ r i : ℕ, (∑ t ∈ Finset.range (r + 1), skewRowCount T t (i + 1)) ≤
        ∑ t ∈ Finset.range r, skewRowCount T t i := by
  refine ⟨?_, ?_⟩
  · intro h r i
    by_cases hr : r < ν.colLen 0
    · obtain ⟨l, hl⟩ := skewRowsWord_append T (Nat.succ_le_of_lt hr)
      have hp : IsLatticeWord (skewRowsWord T (r + 1)) :=
        isLatticeWord_of_append (by simpa only [skewReadingWord, hl] using h)
      have he := ((isLatticeWord_append_iff (skewRowsWord T r) (skewRowWord T r)
        (pairwise_skewRowWord T hT r)).mp hp).2 (Nat.succPNat i)
      change (skewRowsWord T r).count (Nat.succPNat (i + 1)) +
        skewRowCount T r (i + 1) ≤ (skewRowsWord T r).count (Nat.succPNat i) at he
      simpa only [count_skewRowsWord, Finset.sum_range_succ] using he
    · have hr := Nat.not_lt.mp hr
      rw [sum_skewRowCount_stable T _ _ (hr.trans (Nat.le_succ r)),
        sum_skewRowCount_stable T _ _ hr]
      have he := h _ le_rfl (Nat.succPNat i)
      change ((skewReadingWord T).take (skewReadingWord T).length).count
        (Nat.succPNat (i + 1)) ≤
          ((skewReadingWord T).take (skewReadingWord T).length).count (Nat.succPNat i) at he
      simpa only [List.take_length, skewReadingWord, count_skewRowsWord] using he
  · intro h
    have hs : ∀ r, IsLatticeWord (skewRowsWord T r) := by
      intro r
      induction r with
      | zero => exact isLatticeWord_nil
      | succ r ih =>
        apply (isLatticeWord_append_iff _ _ (pairwise_skewRowWord T hT r)).mpr
        refine ⟨ih, ?_⟩
        intro i
        have he := h r i.natPred
        rw [Finset.sum_range_succ] at he
        have hi := PNat.succPNat_natPred i
        have hi' : Nat.succPNat (i.natPred + 1) = i + 1 := by rw [← hi]; rfl
        rw [← count_skewRowsWord, ← count_skewRowsWord] at he
        simpa only [skewRowCount, hi, hi'] using he
    exact hs _

end YoungDiagram
