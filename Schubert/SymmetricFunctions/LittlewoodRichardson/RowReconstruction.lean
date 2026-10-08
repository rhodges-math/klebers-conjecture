import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Find

/-! # Rows reconstructed from multiplicities

A finitely supported sequence of natural multiplicities determines an increasing row.
Cumulative sums describe every threshold and recover the multiplicity of each entry.

## Main results

* `exists_row_of_counts` reconstructs a row from bounded multiplicities.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction.FiniteAlphabet.LittlewoodRichardson

/-- Bounded multiplicities determine a row with the prescribed cumulative thresholds. -/
theorem exists_row_of_counts (a : ℕ → ℕ) (k : ℕ)
    (ha : ∀ i, k ≤ i → a i = 0) :
    ∃ f : ℕ → ℕ,
      (∀ c, (∑ i ∈ Finset.range k, a i) ≤ c → f c = 0) ∧
      (∀ c, c < (∑ i ∈ Finset.range k, a i) → f c < k) ∧
      (∀ c, c < (∑ i ∈ Finset.range k, a i) → ∀ i,
        f c < i ↔ c < ∑ j ∈ Finset.range i, a j) ∧
      (∀ i, ((Finset.range (∑ j ∈ Finset.range k, a j)).filter
        (fun c => f c = i)).card = a i) := by
  classical
  let C (i : ℕ) := ∑ j ∈ Finset.range i, a j
  have hmono : Monotone C := fun i j hij =>
    Finset.sum_le_sum_of_subset (Finset.range_mono hij)
  have hbound (i : ℕ) : C i ≤ C k := by
    rcases le_total i k with hi | hi
    · exact hmono hi
    · have he : C k = C i := Finset.sum_subset (Finset.range_mono hi) (by
        intro j hj hjk
        exact ha j (by simpa only [Finset.mem_range, not_lt] using hjk))
      exact he.symm.le
  have hex (c : ℕ) (hc : c < C k) : ∃ i, c < C (i + 1) :=
    ⟨k, hc.trans_le (hmono (Nat.le_succ k))⟩
  let f (c : ℕ) := if hc : c < C k then Nat.find (hex c hc) else 0
  have hthreshold (c : ℕ) (hc : c < C k) (i : ℕ) : f c < i ↔ c < C i := by
    rw [show f c = Nat.find (hex c hc) from dite_eq_left hc, Nat.find_lt_iff]
    constructor
    · rintro ⟨j, hj, hcj⟩
      exact hcj.trans_le (hmono (by omega))
    · intro hci
      cases i with
      | zero => simp only [C, Finset.range_zero, Finset.sum_empty, Nat.not_lt_zero] at hci
      | succ i => exact ⟨i, Nat.lt_succ_self i, hci⟩
  refine ⟨f, ?_, ?_, hthreshold, ?_⟩
  · intro c hc
    exact dite_eq_right (Nat.not_lt.mpr hc)
  · intro c hc
    exact (hthreshold c hc k).mpr hc
  · intro i
    have he : (Finset.range (C k)).filter (fun c => f c = i) =
        Finset.Ico (C i) (C (i + 1)) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨hc, hfi⟩
        refine ⟨?_, ?_⟩
        · by_contra hlt
          have hf := (hthreshold c hc i).mpr (Nat.lt_of_not_ge hlt)
          omega
        · exact (hthreshold c hc (i + 1)).mp (by omega)
      · rintro ⟨hl, hu⟩
        have hc := hu.trans_le (hbound (i + 1))
        refine ⟨hc, ?_⟩
        have hf := (hthreshold c hc (i + 1)).mpr hu
        have hg : ¬ f c < i := fun h => (Nat.not_lt.mpr hl)
          ((hthreshold c hc i).mp h)
        omega
    rw [he, Nat.card_Ico]
    change (∑ j ∈ Finset.range (i + 1), a j) - (∑ j ∈ Finset.range i, a j) = a i
    rw [Finset.sum_range_succ, Nat.add_sub_cancel_left]

end SymmetricFunction.FiniteAlphabet.LittlewoodRichardson
