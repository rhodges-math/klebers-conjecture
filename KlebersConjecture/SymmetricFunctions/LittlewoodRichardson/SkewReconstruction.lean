import KlebersConjecture.SymmetricFunctions.LittlewoodRichardson.TransposeCounts
import KlebersConjecture.Partitions.Skew.Cutoffs
import KlebersConjecture.Partitions.Skew.LatticeWord

/-! # Skew tableaux reconstructed from straight lattice tableaux

Transposing the matrix of row multiplicities reconstructs a positive skew tableau.
The straight lattice inequalities give its strict columns, and straight strict columns
give its lattice reading word.

## Main results

* `exists_skew_rows_of_straight` reconstructs weak rows with transposed counts.
* `exists_skew_of_straight` reconstructs an LR skew tableau with transposed row counts.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction.FiniteAlphabet.LittlewoodRichardson

open SemistandardYoungTableau

/-- Transposed straight row counts determine weakly increasing skew rows. -/
theorem exists_skew_rows_of_straight (α β ν : YoungDiagram) (n : ℕ)
    (hα : α.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n) (T : TauCeti.BoundedSSYT n β)
    (hw : (fun i : Fin n => (α.rowLen i.val : ℤ)) + weightVec T =
      (fun i : Fin n => (ν.rowLen i.val : ℤ))) :
    ∃ U : YoungDiagram.SkewFilling α ν,
      (∀ p q : YoungDiagram.skewCells α ν,
        p.val.1 = q.val.1 → p.val.2 ≤ q.val.2 → U p ≤ U q) ∧
      ∀ r i, YoungDiagram.skewRowCount U r i = rowCount T.val i r := by
  classical
  have hαν : α ≤ ν := by
    apply YoungDiagram.le_of_forall_rowLen_le
    intro r
    by_cases hr : r < n
    · have he := congrFun hw ⟨r, hr⟩
      change (α.rowLen r : ℤ) + (content T.val r : ℤ) = (ν.rowLen r : ℤ) at he
      omega
    · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (hα.trans (Nat.not_lt.mp hr))]
      exact Nat.zero_le _
  have htotal (r : ℕ) :
      (∑ i ∈ Finset.range (β.colLen 0), rowCount T.val i r) =
        ν.rowLen r - α.rowLen r := by
    change countBelow T.val (β.colLen 0) r = _
    rw [← content_eq_countBelow, content_of_weight_eq T α ν hν hw]
  choose f hf using fun r => exists_row_of_counts (fun i => rowCount T.val i r)
    (β.colLen 0) (fun i hi => rowCount_eq_zero_of_colLen_le T.val hi r)
  have hthreshold (r c i : ℕ) (hc : c < ν.rowLen r - α.rowLen r) :
      f r c < i ↔ c < ∑ j ∈ Finset.range i, rowCount T.val j r := by
    apply (hf r).2.2.1
    rwa [htotal]
  have hweak (r c d : ℕ) (hcd : c ≤ d) (hd : d < ν.rowLen r - α.rowLen r) :
      f r c ≤ f r d := by
    have hd' := (hthreshold r d (f r d + 1) hd).mp (Nat.lt_succ_self _)
    have hc := (hthreshold r c (f r d + 1) (hcd.trans_lt hd)).mpr (hcd.trans_lt hd')
    omega
  let U : YoungDiagram.SkewFilling α ν := fun p =>
    Nat.succPNat (f p.val.1 (p.val.2 - α.rowLen p.val.1))
  have hentry (r c : ℕ) (hc : (r, c) ∈ YoungDiagram.skewCells α ν) :
      YoungDiagram.skewEntry U r c = Nat.succPNat (f r (c - α.rowLen r)) :=
    YoungDiagram.skewEntry_cell U ⟨(r, c), hc⟩
  have hrow : ∀ p q : YoungDiagram.skewCells α ν,
      p.val.1 = q.val.1 → p.val.2 ≤ q.val.2 → U p ≤ U q := by
    intro p q he hcols
    change Nat.succPNat (f p.val.1 (p.val.2 - α.rowLen p.val.1)) ≤
      Nat.succPNat (f q.val.1 (q.val.2 - α.rowLen q.val.1))
    rw [← he]
    apply Nat.succPNat_mono
    have hq := (YoungDiagram.mem_skewCells α ν q.val.1 q.val.2).mp q.property
    rw [← he] at hq
    exact hweak p.val.1 _ _ (Nat.sub_le_sub_right hcols _) (by omega)
  have hcounts (r i : ℕ) : YoungDiagram.skewRowCount U r i = rowCount T.val i r := by
    rw [YoungDiagram.skewRowCount_eq_card]
    have he : (((Finset.range (ν.rowLen r)).filter fun c =>
        α.rowLen r ≤ c ∧ YoungDiagram.skewEntry U r c = Nat.succPNat i).card) =
        (((Finset.range (ν.rowLen r - α.rowLen r)).filter fun d => f r d = i).card) := by
      apply Finset.card_bij (fun c _ => c - α.rowLen r)
      · intro c hc
        obtain ⟨hcν, hcα, hci⟩ := Finset.mem_filter.mp hc
        have hcell : (r, c) ∈ YoungDiagram.skewCells α ν :=
          (YoungDiagram.mem_skewCells α ν r c).mpr ⟨hcα, Finset.mem_range.mp hcν⟩
        rw [hentry r c hcell] at hci
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hcν
          omega), Nat.succPNat_injective hci⟩
      · intro c hc d hd he
        have hca := (Finset.mem_filter.mp hc).2.1
        have hda := (Finset.mem_filter.mp hd).2.1
        omega
      · intro d hd
        obtain ⟨hdν, hdi⟩ := Finset.mem_filter.mp hd
        have hr := YoungDiagram.rowLen_le_of_le hαν r
        have hd' := Finset.mem_range.mp hdν
        have hcell : (r, d + α.rowLen r) ∈ YoungDiagram.skewCells α ν :=
          (YoungDiagram.mem_skewCells α ν r _).mpr ⟨by omega, by omega⟩
        refine ⟨d + α.rowLen r, ?_, Nat.add_sub_cancel _ _⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr (by omega), by omega, ?_⟩
        rw [hentry _ _ hcell, Nat.add_sub_cancel, hdi]
    rw [he, ← htotal]
    exact (hf r).2.2.2 i
  exact ⟨U, hrow, hcounts⟩

/-- A bounded straight lattice tableau determines an LR skew tableau with transposed counts. -/
theorem exists_skew_of_straight (α β ν : YoungDiagram) (n : ℕ)
    (hα : α.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n) (T : TauCeti.BoundedSSYT n β)
    (hlat : IsLattice (fun i : Fin n => (α.rowLen i.val : ℤ)) T.val)
    (hw : (fun i : Fin n => (α.rowLen i.val : ℤ)) + weightVec T =
      (fun i : Fin n => (ν.rowLen i.val : ℤ))) :
    ∃ U : YoungDiagram.LRTableau α β ν,
      ∀ r i, YoungDiagram.skewRowCount U.val r i = rowCount T.val i r := by
  classical
  have hαν : α ≤ ν := by
    apply YoungDiagram.le_of_forall_rowLen_le
    intro r
    by_cases hr : r < n
    · have he := congrFun hw ⟨r, hr⟩
      change (α.rowLen r : ℤ) + (content T.val r : ℤ) = (ν.rowLen r : ℤ) at he
      omega
    · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (hα.trans (Nat.not_lt.mp hr))]
      exact Nat.zero_le _
  obtain ⟨U, hrow, hcounts⟩ := exists_skew_rows_of_straight α β ν n hα hν T hw
  have hcutoff (r i : ℕ) :
      YoungDiagram.skewCutoff U r i = α.rowLen r + countBelow T.val i r := by
    simp only [YoungDiagram.skewCutoff, YoungDiagram.skewCountLt, hcounts, countBelow]
  have hsemi : YoungDiagram.SkewSemistandard U := by
    apply (YoungDiagram.skewSemistandard_iff_cutoffs U hαν hrow).mpr
    intro r i
    by_cases hr : r + 1 < n
    · rw [hcutoff, hcutoff]
      have hh := hlat i r hr
      rw [weightAt_of_lt _ hr, weightAt_of_lt _ (by omega : r < n)] at hh
      change (α.rowLen (r + 1) : ℤ) + (countBelow T.val (i + 1) (r + 1) : ℤ) ≤
        (α.rowLen r : ℤ) + (countBelow T.val i r : ℤ) at hh
      exact_mod_cast hh
    · have hb := YoungDiagram.skewCutoff_le_outer U hαν (r + 1) (i + 1)
      rw [YoungDiagram.rowLen_eq_zero_of_colLen_le
        (hν.trans (Nat.not_lt.mp hr))] at hb
      exact hb.trans (Nat.zero_le _)
  have hcontent (i : ℕ) : YoungDiagram.skewContent U (Nat.succPNat i) = β.rowLen i := by
    rw [YoungDiagram.skewContent_eq_sum_rows]
    simp only [hcounts]
    exact sum_rowCount_target T α ν hν hw i
  have hlattice : YoungDiagram.IsLatticeWord (YoungDiagram.skewReadingWord U) := by
    apply (YoungDiagram.isLatticeWord_iff_skewRowCount U hsemi).mpr
    intro r i
    simp only [hcounts, sum_rowCount]
    exact T.val.rowCountLt_succ_le i r
  refine ⟨⟨U, hαν, hsemi, ?_, hlattice⟩, hcounts⟩
  intro x
  change YoungDiagram.skewContent U x = β.rowLen x.natPred
  simpa only [PNat.succPNat_natPred] using hcontent x.natPred

end SymmetricFunction.FiniteAlphabet.LittlewoodRichardson
