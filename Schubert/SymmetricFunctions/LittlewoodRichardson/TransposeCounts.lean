import Schubert.SymmetricFunctions.LittlewoodRichardson.FiniteAlphabet.RowCount
import Schubert.SymmetricFunctions.LittlewoodRichardson.RowReconstruction

/-! # Row multiplicities and straight tableau reconstruction

Cumulative row counts determine every entry of a semistandard tableau.
The strict-column inequalities allow reconstruction from a bounded multiplicity matrix.

## Main results

* `rowCount_eq_card` expresses row multiplicities as cell counts.
* `sum_rowCount` recovers cumulative counts by telescoping.
* `exists_ssyt_of_counts` reconstructs a bounded semistandard tableau.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction.FiniteAlphabet.LittlewoodRichardson

open SemistandardYoungTableau

/-- A row multiplicity is the number of columns carrying its letter. -/
theorem rowCount_eq_card {β : YoungDiagram} (T : SemistandardYoungTableau β) (r x : ℕ) :
    rowCount T r x = ((Finset.range (β.rowLen r)).filter (fun c => T r c = x)).card := by
  classical
  have he : ((Finset.range (β.rowLen r)).filter (fun c => T r c = x)) =
      ((Finset.range (β.rowLen r)).filter (fun c => T r c < x + 1)) \
        ((Finset.range (β.rowLen r)).filter (fun c => T r c < x)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hc, he⟩
      exact ⟨⟨hc, by omega⟩, fun h => by omega⟩
    · rintro ⟨⟨hc, hlt⟩, hn⟩
      refine ⟨hc, ?_⟩
      have hge : ¬ T r c < x := fun h => hn ⟨hc, h⟩
      omega
  rw [he, filter_lt_eq_range, filter_lt_eq_range,
    Finset.card_sdiff_of_subset (Finset.range_mono (T.rowCountLt_mono r (Nat.le_succ x))),
    Finset.card_range, Finset.card_range]
  rfl

/-- The sum of initial multiplicities is the cumulative count below that threshold. -/
theorem sum_rowCount {β : YoungDiagram} (T : SemistandardYoungTableau β) (r x : ℕ) :
    (∑ j ∈ Finset.range x, rowCount T r j) = rowCountLt T r x := by
  simp only [rowCount]
  rw [Finset.sum_range_tsub (fun _ _ h => T.rowCountLt_mono r h)]
  have hz : rowCountLt T r 0 = 0 := by simp [rowCountLt]
  rw [hz, Nat.sub_zero]

/-- At the alphabet bound every column of a row has already been counted. -/
theorem sum_rowCount_bounded {β : YoungDiagram} {n : ℕ} (T : TauCeti.BoundedSSYT n β)
    (r : ℕ) : (∑ j ∈ Finset.range n, rowCount T.val r j) = β.rowLen r := by
  rw [sum_rowCount, rowCountLt]
  have he : ((Finset.range (β.rowLen r)).filter (fun c => T.val r c < n)) =
      Finset.range (β.rowLen r) := by
    apply Finset.filter_eq_self.mpr
    intro c hc
    exact T.entry_lt (YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_range.mp hc))
  rw [he, Finset.card_range]

/-- A letter beyond the alphabet has no occurrences in any row. -/
theorem rowCount_bounded_zero {β : YoungDiagram} {n : ℕ} (T : TauCeti.BoundedSSYT n β)
    (r x : ℕ) (hx : n ≤ x) : rowCount T.val r x = 0 := by
  rw [rowCount_eq_card]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨hc, he⟩ := Finset.mem_filter.mp hc
  have hb := T.entry_lt (YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_range.mp hc))
  omega

/-- A row multiplicity is bounded by the total content of its letter. -/
theorem rowCount_le_content {β : YoungDiagram} (T : SemistandardYoungTableau β) (r x : ℕ) :
    rowCount T r x ≤ content T x := by
  have h := countBelow_le_content T (r + 1) x
  rw [countBelow_succ] at h
  omega

/-- The terminal weight equation identifies the nonnegative content coordinates. -/
theorem content_of_weight_eq {β : YoungDiagram} {n : ℕ} (T : TauCeti.BoundedSSYT n β)
    (α ν : YoungDiagram) (hν : ν.colLen 0 ≤ n)
    (hw : (fun i : Fin n => (α.rowLen i : ℤ)) + weightVec T =
      (fun i : Fin n => (ν.rowLen i : ℤ))) (r : ℕ) :
    content T.val r = ν.rowLen r - α.rowLen r := by
  by_cases hr : r < n
  · have he := congrFun hw ⟨r, hr⟩
    change (α.rowLen r : ℤ) + (content T.val r : ℤ) = (ν.rowLen r : ℤ) at he
    omega
  · rw [content_eq_countBelow, YoungDiagram.rowLen_eq_zero_of_colLen_le
      (hν.trans (Nat.not_lt.mp hr)), Nat.zero_sub]
    simp only [countBelow, rowCount_bounded_zero T _ r (Nat.not_lt.mp hr),
      Finset.sum_const_zero]

/-- No row uses a letter at or beyond the height of the terminal diagram. -/
theorem rowCount_target_zero {β : YoungDiagram} {n : ℕ} (T : TauCeti.BoundedSSYT n β)
    (α ν : YoungDiagram) (hν : ν.colLen 0 ≤ n)
    (hw : (fun i : Fin n => (α.rowLen i : ℤ)) + weightVec T =
      (fun i : Fin n => (ν.rowLen i : ℤ))) (r j : ℕ) (hj : ν.colLen 0 ≤ j) :
    rowCount T.val r j = 0 := by
  have hc := rowCount_le_content T.val r j
  rw [content_of_weight_eq T α ν hν hw j,
    YoungDiagram.rowLen_eq_zero_of_colLen_le hj, Nat.zero_sub] at hc
  exact Nat.eq_zero_of_le_zero hc

/-- The terminal height suffices to sum every multiplicity in each straight row. -/
theorem sum_rowCount_target {β : YoungDiagram} {n : ℕ} (T : TauCeti.BoundedSSYT n β)
    (α ν : YoungDiagram) (hν : ν.colLen 0 ≤ n)
    (hw : (fun i : Fin n => (α.rowLen i : ℤ)) + weightVec T =
      (fun i : Fin n => (ν.rowLen i : ℤ))) (r : ℕ) :
    (∑ j ∈ Finset.range (ν.colLen 0), rowCount T.val r j) = β.rowLen r := by
  rw [← sum_rowCount_bounded T r]
  apply Finset.sum_subset (Finset.range_mono hν)
  intro j hj hjν
  exact rowCount_target_zero T α ν hν hw r j
    (by simpa only [Finset.mem_range, not_lt] using hjν)

/-- Equal row multiplicities determine a semistandard tableau. -/
theorem eq_of_rowCount_eq {β : YoungDiagram} (T U : SemistandardYoungTableau β)
    (h : ∀ r x, rowCount T r x = rowCount U r x) : T = U := by
  apply SemistandardYoungTableau.ext
  intro r c
  by_cases hc : c < β.rowLen r
  · have hs (x : ℕ) : rowCountLt T r x = rowCountLt U r x := by
      rw [← sum_rowCount, ← sum_rowCount]
      exact Finset.sum_congr rfl (fun x _ => h r x)
    have htu := (T.lt_rowCountLt_iff (x := T r c + 1) hc).mpr (by omega)
    rw [hs] at htu
    have hut := (U.lt_rowCountLt_iff (x := U r c + 1) hc).mpr (by omega)
    rw [← hs] at hut
    have h1 := (U.lt_rowCountLt_iff hc).mp htu
    have h2 := (T.lt_rowCountLt_iff hc).mp hut
    omega
  · have hn : (r, c) ∉ β := by simpa only [YoungDiagram.mem_iff_lt_rowLen] using hc
    rw [T.zeros hn, U.zeros hn]

/-- Bounded multiplicities with strict-column inequalities reconstruct a straight tableau. -/
theorem exists_ssyt_of_counts (β : YoungDiagram) (m : ℕ → ℕ → ℕ) (n : ℕ)
    (hbound : ∀ r j, n ≤ j → m r j = 0)
    (hsum : ∀ r, (∑ j ∈ Finset.range n, m r j) = β.rowLen r)
    (hcol : ∀ r j, (∑ t ∈ Finset.range (j + 1), m (r + 1) t) ≤
      ∑ t ∈ Finset.range j, m r t) :
    ∃ T : TauCeti.BoundedSSYT n β, ∀ r j, rowCount T.val r j = m r j := by
  classical
  choose f hf using fun r => exists_row_of_counts (m r) n (hbound r)
  have hthreshold (r c i : ℕ) (hc : c < β.rowLen r) :
      f r c < i ↔ c < ∑ j ∈ Finset.range i, m r j := by
    apply (hf r).2.2.1
    rwa [hsum]
  have hadj (r c : ℕ) (hc : c < β.rowLen (r + 1)) : f r c < f (r + 1) c := by
    have hupper : c < β.rowLen r := hc.trans_le (β.rowLen_anti r (r + 1) (by omega))
    have hl := (hthreshold (r + 1) c (f (r + 1) c + 1) hc).mp (Nat.lt_succ_self _)
    exact (hthreshold r c (f (r + 1) c) hupper).mpr (hl.trans_le (hcol r _))
  have hcolumns : ∀ r s c, r < s → c < β.rowLen s → f r c < f s c := by
    intro r s
    induction s generalizing r with
    | zero => intro c hrs hc; omega
    | succ s ih =>
      intro c hrs hc
      by_cases he : r = s
      · subst r
        exact hadj s c hc
      · have hrs' : r < s := by omega
        exact (ih r c hrs' (hc.trans_le (β.rowLen_anti s (s + 1) (by omega)))).trans
          (hadj s c hc)
  let T : SemistandardYoungTableau β :=
    { entry := f
      zeros' := by
        intro r c hc
        apply (hf r).1
        rw [hsum]
        simpa only [YoungDiagram.mem_iff_lt_rowLen, not_lt] using hc
      row_weak' := by
        intro r c d hcd hd
        have hd' := YoungDiagram.mem_iff_lt_rowLen.mp hd
        have hc := hcd.trans hd'
        have ht := (hthreshold r d (f r d + 1) hd').mp (Nat.lt_succ_self _)
        have hl := (hthreshold r c (f r d + 1) hc).mpr (hcd.trans ht)
        omega
      col_strict' := by
        intro r s c hrs hc
        exact hcolumns r s c hrs (YoungDiagram.mem_iff_lt_rowLen.mp hc) }
  refine ⟨⟨T, ?_⟩, ?_⟩
  · intro r c hc
    apply (hf r).2.1
    rw [hsum]
    exact YoungDiagram.mem_iff_lt_rowLen.mp hc
  · intro r j
    rw [rowCount_eq_card]
    change ((Finset.range (β.rowLen r)).filter (fun c => f r c = j)).card = m r j
    rw [← hsum]
    exact (hf r).2.2.2 j

end SymmetricFunction.FiniteAlphabet.LittlewoodRichardson
