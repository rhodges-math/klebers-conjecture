import KlebersConjecture.Partitions.Skew.RowCounts
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Cutoffs in weakly increasing skew rows

Counts of labels below a threshold determine the column where that threshold starts.

## Main results

* `skewEntry_lt_iff_prefix` identifies a weak row's threshold interval.
* `skewEntry_eq_iff_cutoff` gives the columns occupied by each positive label.
* `skewFilling_eq_of_rowCounts` recovers a weak filling from its row multiplicities.
* `skewSemistandard_iff_cutoffs` expresses strict columns by adjacent cutoff inequalities.

## Implementation notes

Cutoffs are column coordinates including the inner-row offset. They are not truncated
to the preceding row, so adjacent inequalities retain the semistandard boundary cases.
-/

noncomputable section

namespace YoungDiagram

variable {α ν : YoungDiagram}

/-- The number of entries whose zero-based label index is below i in skew row r. -/
def skewCountLt (T : SkewFilling α ν) (r i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, skewRowCount T r j

/-- The first column in a skew row whose label is at least i+1. -/
def skewCutoff (T : SkewFilling α ν) (r i : ℕ) : ℕ :=
  α.rowLen r + skewCountLt T r i

/-- Threshold zero starts at the inner boundary. -/
theorem skewCutoff_zero (T : SkewFilling α ν) (r : ℕ) :
    skewCutoff T r 0 = α.rowLen r := by
  simp only [skewCutoff, skewCountLt, Finset.range_zero, Finset.sum_empty, Nat.add_zero]

/-- Consecutive thresholds differ by the multiplicity of their label. -/
theorem skewCutoff_succ (T : SkewFilling α ν) (r i : ℕ) :
    skewCutoff T r (i + 1) = skewCutoff T r i + skewRowCount T r i := by
  simp only [skewCutoff, skewCountLt, Finset.sum_range_succ, Nat.add_assoc]

/-- A skew cutoff is never before its inner boundary. -/
theorem inner_le_skewCutoff (T : SkewFilling α ν) (r i : ℕ) :
    α.rowLen r ≤ skewCutoff T r i := Nat.le_add_right _ _

/-- The cumulative row count counts the cells below its positive-label threshold. -/
theorem skewCountLt_eq_card (T : SkewFilling α ν) (r i : ℕ) :
    skewCountLt T r i = ((Finset.range (ν.rowLen r)).filter fun c =>
      α.rowLen r ≤ c ∧ skewEntry T r c < Nat.succPNat i).card := by
  classical
  let S := (Finset.range (ν.rowLen r)).filter fun c => α.rowLen r ≤ c
  have hf (j : ℕ) : (S.filter fun c => (skewEntry T r c).natPred = j) =
      (Finset.range (ν.rowLen r)).filter (fun c =>
        α.rowLen r ≤ c ∧ skewEntry T r c = Nat.succPNat j) := by
    ext c
    simp only [S, Finset.mem_filter]
    have he : (skewEntry T r c).natPred = j ↔ skewEntry T r c = Nat.succPNat j := by
      constructor
      · intro h
        simpa only [PNat.succPNat_natPred] using congrArg Nat.succPNat h
      · intro h
        simpa only [Nat.natPred_succPNat] using congrArg PNat.natPred h
    tauto
  simp only [skewCountLt, skewRowCount_eq_card, ← hf]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  apply congrArg Finset.card
  ext c
  have he : (skewEntry T r c).natPred < i ↔ skewEntry T r c < Nat.succPNat i := by
    simpa only [Nat.natPred_succPNat] using
      (PNat.natPred_lt_natPred (m := skewEntry T r c) (n := Nat.succPNat i))
  simp only [S, Finset.mem_filter, Finset.mem_range]
  tauto

/-- Under containment, every cutoff lies within its outer row boundary. -/
theorem skewCutoff_le_outer (T : SkewFilling α ν) (hαν : α ≤ ν) (r i : ℕ) :
    skewCutoff T r i ≤ ν.rowLen r := by
  rw [skewCutoff, skewCountLt_eq_card]
  have hs : ((Finset.range (ν.rowLen r)).filter fun c =>
      α.rowLen r ≤ c ∧ skewEntry T r c < Nat.succPNat i) ⊆
      Finset.Ico (α.rowLen r) (ν.rowLen r) := by
    intro c hc
    obtain ⟨hc, hl, _⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_Ico.mpr ⟨hl, Finset.mem_range.mp hc⟩
  have hb := Finset.card_le_card hs
  rw [Nat.card_Ico] at hb
  have hrow := YoungDiagram.rowLen_le_of_le hαν r
  omega

private theorem row_le_entries (T : SkewFilling α ν)
    (hrow : ∀ p q : skewCells α ν, p.val.1 = q.val.1 → p.val.2 ≤ q.val.2 → T p ≤ T q)
    {r c d : ℕ} (hc : (r, c) ∈ skewCells α ν) (hd : (r, d) ∈ skewCells α ν)
    (hcd : c ≤ d) : skewEntry T r c ≤ skewEntry T r d := by
  have he := hrow ⟨(r, c), hc⟩ ⟨(r, d), hd⟩ rfl hcd
  simpa only [← skewEntry_cell T ⟨(r, c), hc⟩,
    ← skewEntry_cell T ⟨(r, d), hd⟩] using he

/-- A weakly increasing skew row starts a threshold after precisely its smaller labels. -/
theorem skewEntry_lt_iff_prefix (T : SkewFilling α ν)
    (hrow : ∀ p q : skewCells α ν, p.val.1 = q.val.1 → p.val.2 ≤ q.val.2 → T p ≤ T q)
    (r c i : ℕ) (hc : (r, c) ∈ skewCells α ν) :
    skewEntry T r c < Nat.succPNat i ↔ c < α.rowLen r +
      ((Finset.range (ν.rowLen r)).filter fun d =>
        α.rowLen r ≤ d ∧ skewEntry T r d < Nat.succPNat i).card := by
  classical
  let S := (Finset.range (ν.rowLen r)).filter fun d =>
    α.rowLen r ≤ d ∧ skewEntry T r d < Nat.succPNat i
  have hcell := (mem_skewCells α ν r c).mp hc
  constructor
  · intro hlt
    have hs : Finset.Ico (α.rowLen r) (c + 1) ⊆ S := by
      intro d hd
      have hd' := Finset.mem_Ico.mp hd
      have hdcell : (r, d) ∈ skewCells α ν :=
        (mem_skewCells α ν r d).mpr ⟨hd'.1, by omega⟩
      have he := (row_le_entries T hrow hdcell hc (by omega)).trans_lt hlt
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hd'.1, he⟩
    have hb := Finset.card_le_card hs
    rw [Nat.card_Ico] at hb
    change c < α.rowLen r + S.card
    omega
  · intro hlt
    by_contra hn
    have hs : S ⊆ Finset.Ico (α.rowLen r) c := by
      intro d hd
      obtain ⟨hdν, hdα, hdi⟩ := Finset.mem_filter.mp hd
      have hdcell : (r, d) ∈ skewCells α ν :=
        (mem_skewCells α ν r d).mpr ⟨hdα, Finset.mem_range.mp hdν⟩
      have hdc : d < c := by
        by_contra h
        have he := row_le_entries T hrow hc hdcell (by omega)
        exact hn (he.trans_lt hdi)
      exact Finset.mem_Ico.mpr ⟨hdα, hdc⟩
    have hb := Finset.card_le_card hs
    rw [Nat.card_Ico] at hb
    change c < α.rowLen r + S.card at hlt
    omega

/-- Labels below i+1 occupy exactly the columns before cutoff i. -/
theorem skewEntry_lt_iff_cutoff (T : SkewFilling α ν)
    (hrow : ∀ p q : skewCells α ν, p.val.1 = q.val.1 → p.val.2 ≤ q.val.2 → T p ≤ T q)
    (r c i : ℕ) (hc : (r, c) ∈ skewCells α ν) :
    skewEntry T r c < Nat.succPNat i ↔ c < skewCutoff T r i := by
  rw [skewCutoff, skewCountLt_eq_card]
  exact skewEntry_lt_iff_prefix T hrow r c i hc

/-- Label i+1 occupies the interval between its two consecutive cutoffs. -/
theorem skewEntry_eq_iff_cutoff (T : SkewFilling α ν)
    (hrow : ∀ p q : skewCells α ν, p.val.1 = q.val.1 → p.val.2 ≤ q.val.2 → T p ≤ T q)
    (r c i : ℕ) (hc : (r, c) ∈ skewCells α ν) :
    skewEntry T r c = Nat.succPNat i ↔
      skewCutoff T r i ≤ c ∧ c < skewCutoff T r (i + 1) := by
  have hlow := skewEntry_lt_iff_cutoff T hrow r c i hc
  have hhigh := skewEntry_lt_iff_cutoff T hrow r c (i + 1) hc
  constructor
  · intro he
    constructor
    · apply Nat.le_of_not_gt
      intro h
      have hh := hlow.mpr h
      rw [he] at hh
      exact (lt_irrefl _ hh)
    · apply hhigh.mp
      rw [he, Nat.succPNat_lt_succPNat]
      exact Nat.lt_succ_self i
  · rintro ⟨hl, hh⟩
    have hge : ¬skewEntry T r c < Nat.succPNat i :=
      fun h => (Nat.not_lt_of_ge hl) (hlow.mp h)
    have hlt := hhigh.mpr hh
    apply Subtype.ext
    change (skewEntry T r c).val = i + 1
    change ¬(skewEntry T r c).val < i + 1 at hge
    change (skewEntry T r c).val < i + 1 + 1 at hlt
    omega

/-- Weakly increasing skew fillings with the same row multiplicities agree. -/
theorem skewFilling_eq_of_rowCounts (T U : SkewFilling α ν)
    (hT : ∀ p q : skewCells α ν, p.val.1 = q.val.1 → p.val.2 ≤ q.val.2 → T p ≤ T q)
    (hU : ∀ p q : skewCells α ν, p.val.1 = q.val.1 → p.val.2 ≤ q.val.2 → U p ≤ U q)
    (hcounts : ∀ r i, skewRowCount T r i = skewRowCount U r i) : T = U := by
  funext p
  have he (r i : ℕ) : skewCutoff T r i = skewCutoff U r i := by
    simp only [skewCutoff, skewCountLt, hcounts]
  let i := (T p).natPred
  have ht : skewEntry T p.val.1 p.val.2 = Nat.succPNat i := by
    rw [skewEntry_cell, PNat.succPNat_natPred]
  have hc := (skewEntry_eq_iff_cutoff T hT _ _ i p.property).mp ht
  rw [he, he] at hc
  have hu := (skewEntry_eq_iff_cutoff U hU _ _ i p.property).mpr hc
  rw [skewEntry_cell] at hu
  exact (PNat.succPNat_natPred (T p)).symm.trans hu.symm

/-- Under weak rows, strict columns are exactly the shifted adjacent cutoff inequalities. -/
theorem skewColumns_iff_cutoffs (T : SkewFilling α ν) (hαν : α ≤ ν)
    (hrow : ∀ p q : skewCells α ν, p.val.1 = q.val.1 → p.val.2 ≤ q.val.2 → T p ≤ T q) :
    (∀ p q : skewCells α ν, p.val.2 = q.val.2 → p.val.1 < q.val.1 → T p < T q) ↔
      ∀ r i : ℕ, skewCutoff T (r + 1) (i + 1) ≤ skewCutoff T r i := by
  constructor
  · intro hcol r i
    by_contra hn
    have hlo : skewCutoff T r i < skewCutoff T (r + 1) (i + 1) := by omega
    let c := skewCutoff T (r + 1) (i + 1) - 1
    have hp := inner_le_skewCutoff T r i
    have hq := inner_le_skewCutoff T (r + 1) (i + 1)
    have hbound := skewCutoff_le_outer T hαν (r + 1) (i + 1)
    have ha := α.rowLen_anti r (r + 1) (Nat.le_succ r)
    have hv := ν.rowLen_anti r (r + 1) (Nat.le_succ r)
    have hpc : (r, c) ∈ skewCells α ν :=
      (mem_skewCells α ν r c).mpr ⟨by dsimp only [c]; omega, by dsimp only [c]; omega⟩
    have hqc : (r + 1, c) ∈ skewCells α ν :=
      (mem_skewCells α ν (r + 1) c).mpr
        ⟨by dsimp only [c]; omega, by dsimp only [c]; omega⟩
    have hlower := (skewEntry_lt_iff_cutoff T hrow (r + 1) c (i + 1) hqc).mpr
      (show c < skewCutoff T (r + 1) (i + 1) by dsimp only [c]; omega)
    have hstrict := hcol ⟨(r, c), hpc⟩ ⟨(r + 1, c), hqc⟩ rfl (Nat.lt_succ_self r)
    have hstrict' : skewEntry T r c < skewEntry T (r + 1) c := by
      simpa only [← skewEntry_cell T ⟨(r, c), hpc⟩,
        ← skewEntry_cell T ⟨(r + 1, c), hqc⟩] using hstrict
    have hupper : skewEntry T r c < Nat.succPNat i := by
      change (skewEntry T r c).val < i + 1
      change (skewEntry T (r + 1) c).val < i + 1 + 1 at hlower
      change (skewEntry T r c).val < (skewEntry T (r + 1) c).val at hstrict'
      omega
    have hh := (skewEntry_lt_iff_cutoff T hrow r c i hpc).mp hupper
    dsimp only [c] at hh
    omega
  · intro hcut
    have hadj (r c : ℕ) (hp : (r, c) ∈ skewCells α ν)
        (hq : (r + 1, c) ∈ skewCells α ν) :
        skewEntry T r c < skewEntry T (r + 1) c := by
      let i := (skewEntry T (r + 1) c).natPred
      have he : skewEntry T (r + 1) c = Nat.succPNat i :=
        (PNat.succPNat_natPred _).symm
      have hlt : skewEntry T (r + 1) c < Nat.succPNat (i + 1) := by
        rw [he, Nat.succPNat_lt_succPNat]
        exact Nat.lt_succ_self i
      have hc := (skewEntry_lt_iff_cutoff T hrow (r + 1) c (i + 1) hq).mp hlt
      have hh := hc.trans_le (hcut r i)
      have hu := (skewEntry_lt_iff_cutoff T hrow r c i hp).mpr hh
      rw [← he] at hu
      exact hu
    have hchain (r c : ℕ) (hr : (r, c) ∈ skewCells α ν) :
        ∀ s : ℕ, r < s → (s, c) ∈ skewCells α ν → skewEntry T r c < skewEntry T s c := by
      intro s
      induction s with
      | zero => intro h; omega
      | succ s ih =>
        intro hrs hs
        by_cases he : r = s
        · subst r
          exact hadj s c hr hs
        · have hmid : (s, c) ∈ skewCells α ν := by
            have hr' := (mem_skewCells α ν r c).mp hr
            have hs' := (mem_skewCells α ν (s + 1) c).mp hs
            exact (mem_skewCells α ν s c).mpr
              ⟨(α.rowLen_anti r s (by omega)).trans hr'.1,
                hs'.2.trans_le (ν.rowLen_anti s (s + 1) (Nat.le_succ s))⟩
          exact (ih (by omega) hmid).trans (hadj s c hmid hs)
    intro p q hcol hrows
    have hq : (q.val.1, p.val.2) ∈ skewCells α ν := by
      simpa only [hcol] using q.property
    have hh := hchain p.val.1 p.val.2 p.property q.val.1 hrows hq
    have he : skewEntry T q.val.1 p.val.2 = T q := by
      rw [hcol]
      exact skewEntry_cell T q
    rw [skewEntry_cell T p, he] at hh
    exact hh

/-- Once rows are weak, the cutoff inequalities characterize skew semistandardness. -/
theorem skewSemistandard_iff_cutoffs (T : SkewFilling α ν) (hαν : α ≤ ν)
    (hrow : ∀ p q : skewCells α ν, p.val.1 = q.val.1 → p.val.2 ≤ q.val.2 → T p ≤ T q) :
    SkewSemistandard T ↔
      ∀ r i : ℕ, skewCutoff T (r + 1) (i + 1) ≤ skewCutoff T r i := by
  exact and_iff_right hrow |>.trans (skewColumns_iff_cutoffs T hαν hrow)

end YoungDiagram
