import KlebersConjecture.SymmetricFunctions.LittlewoodRichardson.FiniteAlphabet.RowCount

/-! # First lattice violations and recutting bounds

The first failed lattice inequality determines a cut suitable for tableau recutting.

## Main results

* `exists_isFirstViolation`: every failure has a first violating row and label.
* `isCut_lrCut`: the cut associated to that violation satisfies the recutting bounds.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction.FiniteAlphabet.LittlewoodRichardson

open SemistandardYoungTableau

variable {d : ℕ} {ν : YoungDiagram} {κ : IntWeight d}
  {T : SemistandardYoungTableau ν} {r i : ℕ}

/-- Adjacent values of a weakly decreasing weight decrease inside its alphabet. -/
theorem weightAt_succ_le (hκ : Antitone κ) {i : ℕ} (hi : i + 1 < d) :
    weightAt κ (i + 1) ≤ weightAt κ i := by
  rw [weightAt_of_lt κ hi, weightAt_of_lt κ (by omega)]
  exact hκ (Fin.mk_le_mk.mpr (Nat.le_succ i))

/-- `(r, i)` is the **first violation** of the lattice condition: the condition fails at row `r`
and letter `i`, holds at all earlier rows, and holds at row `r` for all larger letters. -/
structure IsFirstViolation (κ : IntWeight d) (T : SemistandardYoungTableau ν) (r i : ℕ) :
    Prop where
  lt : i + 1 < d
  viol : weightAt κ i + countBelow T r i < weightAt κ (i + 1) + countBelow T (r + 1) (i + 1)
  row_min : ∀ r' < r, ∀ j, j + 1 < d →
    weightAt κ (j + 1) + countBelow T (r' + 1) (j + 1) ≤ weightAt κ j + countBelow T r' j
  letter_max : ∀ j, i < j → j + 1 < d →
    weightAt κ (j + 1) + countBelow T (r + 1) (j + 1) ≤ weightAt κ j + countBelow T r j

/-- A first violation witnesses failure of the lattice inequalities. -/
theorem IsFirstViolation.not_isLattice (h : IsFirstViolation κ T r i) : ¬ IsLattice κ T :=
  fun hl => absurd (hl r i h.lt) (not_le.mpr h.viol)

/-- The first violation is unique. -/
theorem IsFirstViolation.unique {r' i' : ℕ} (h : IsFirstViolation κ T r i)
    (h' : IsFirstViolation κ T r' i') : r = r' ∧ i = i' := by
  have hr : r = r' := by
    rcases lt_trichotomy r r' with hlt | heq | hgt
    · exact absurd (h'.row_min r hlt i h.lt) (not_le.mpr h.viol)
    · exact heq
    · exact absurd (h.row_min r' hgt i' h'.lt) (not_le.mpr h'.viol)
  subst hr
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd (h.letter_max i' hlt h'.lt) (not_le.mpr h'.viol)
  · exact heq
  · exact absurd (h'.letter_max i hgt h.lt) (not_le.mpr h.viol)

/-- A tableau that is not lattice has a first violation. -/
theorem exists_isFirstViolation (h : ¬ IsLattice κ T) : ∃ r i, IsFirstViolation κ T r i := by
  classical
  have hex : ∃ r, ∃ i, i + 1 < d ∧
      weightAt κ i + countBelow T r i < weightAt κ (i + 1) + countBelow T (r + 1) (i + 1) := by
    simp only [IsLattice, not_forall, not_le] at h
    obtain ⟨r, i, hi, hv⟩ := h
    exact ⟨r, i, hi, hv⟩
  obtain ⟨i₀, hi₀, hv₀⟩ := Nat.find_spec hex
  set S := (Finset.range d).filter fun i => i + 1 < d ∧
    weightAt κ i + countBelow T (Nat.find hex) i <
      weightAt κ (i + 1) + countBelow T (Nat.find hex + 1) (i + 1) with hSdef
  have hS : S.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hi₀, hv₀⟩⟩
  have hi := Finset.mem_filter.mp (S.max'_mem hS)
  refine ⟨Nat.find hex, S.max' hS, ⟨hi.2.1, hi.2.2, fun r' hr' j hj => ?_, fun j hij hj => ?_⟩⟩
  · by_contra hc
    exact Nat.find_min hex hr' ⟨j, hj, not_le.mp hc⟩
  · by_contra hc
    have hjS : j ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hj, not_le.mp hc⟩
    exact absurd (S.le_max' j hjS) (not_le.mpr hij)

/-- The balance between the letters `i` and `i + 1` before row `r`: `κ_i − κ_{i+1} + #i(rows <
r) − #(i+1)(rows < r)`. -/
def balance (κ : IntWeight d) (T : SemistandardYoungTableau ν) (r i : ℕ) : ℤ :=
  weightAt κ i - weightAt κ (i + 1) + countBelow T r i - countBelow T r (i + 1)

/-- After a row without violation, the balance is at least the number of `i`s of that row. -/
theorem rowCount_le_balance {k : ℕ} (h : IsFirstViolation κ T (k + 1) i) :
    (rowCount T k i : ℤ) ≤ balance κ T (k + 1) i := by
  have h1 := h.row_min k (Nat.lt_succ_self k) i h.lt
  rw [balance, countBelow_succ T k i]
  push_cast
  linarith

/-- The balance before the first violation is nonnegative. -/
theorem balance_nonneg (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    0 ≤ balance κ T r i := by
  cases r with
  | zero =>
    have := weightAt_succ_le hκ h.lt
    simp only [balance, countBelow_zero, Nat.cast_zero, add_zero, sub_zero]
    linarith
  | succ k => exact le_trans (Nat.cast_nonneg _) (rowCount_le_balance h)

/-- The violating letter count strictly exceeds the balance. -/
theorem balance_lt_rowCount (h : IsFirstViolation κ T r i) :
    balance κ T r i < rowCount T r (i + 1) := by
  have h1 := h.viol
  rw [countBelow_succ T r (i + 1)] at h1
  rw [balance]
  push_cast at h1
  linarith

/-- The balance, as a natural number. -/
def balanceNat (κ : IntWeight d) (T : SemistandardYoungTableau ν) (r i : ℕ) : ℕ :=
  (balance κ T r i).toNat

/-- Casting the natural balance recovers the integer balance. -/
theorem balanceNat_eq (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    (balanceNat κ T r i : ℤ) = balance κ T r i :=
  Int.toNat_of_nonneg (balance_nonneg hκ h)

/-- The column of the violating cell: the `(E + 1)`-st `i + 1` of row `r`, from the right. -/
def violationColumn (κ : IntWeight d) (T : SemistandardYoungTableau ν) (r i : ℕ) : ℕ :=
  rowCountLt T r (i + 2) - balanceNat κ T r i - 1

/-- The violating cell carries `i + 1`: it lies between the last `i` and the last `i + 1`. -/
theorem balanceNat_add_lt (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    rowCountLt T r (i + 1) + balanceNat κ T r i + 1 ≤ rowCountLt T r (i + 2) := by
  have h1 := balance_lt_rowCount h
  rw [← balanceNat_eq hκ h] at h1
  have h2 : rowCountLt T r (i + 1) ≤ rowCountLt T r (i + 2) := T.rowCountLt_mono r (by omega)
  have h3 : (balanceNat κ T r i : ℤ) <
      (rowCountLt T r (i + 1 + 1) - rowCountLt T r (i + 1) : ℕ) := h1
  have h4 : balanceNat κ T r i < rowCountLt T r (i + 2) - rowCountLt T r (i + 1) := by
    exact_mod_cast h3
  omega

/-- **The boundary lemma**: the violating cell lies strictly left of the first `i` of the row
above, so no `i + 1` of row `r` up to the violating column sits below an `i`. -/
theorem violationColumn_lt {k : ℕ} (hκ : Antitone κ) (h : IsFirstViolation κ T (k + 1) i) :
    violationColumn κ T (k + 1) i + 1 ≤ rowCountLt T k i := by
  have h1 := rowCount_le_balance h
  rw [← balanceNat_eq hκ h] at h1
  have h2 : rowCount T k i ≤ balanceNat κ T (k + 1) i := by exact_mod_cast h1
  have h3 := balanceNat_add_lt hκ h
  have h4 : rowCountLt T (k + 1) (i + 2) ≤ rowCountLt T k (i + 1) := T.rowCountLt_succ_le k (i + 1)
  have h5 : rowCountLt T k i ≤ rowCountLt T k (i + 1) := T.rowCountLt_mono k (by omega)
  simp only [rowCount] at h2
  simp only [violationColumn]
  omega

/-- The lower end of the Bender–Knuth interval of row `k` at the letter `v`. -/
def lowerCut (T : SemistandardYoungTableau ν) (v k : ℕ) : ℕ :=
  max (rowCountLt T k v) (rowCountLt T (k + 1) (v + 2))

/-- The upper end of the Bender–Knuth interval of a row `k ≥ 1` at the letter `v`. -/
def upperCut (T : SemistandardYoungTableau ν) (v k : ℕ) : ℕ :=
  min (rowCountLt T k (v + 2)) (rowCountLt T (k - 1) v)

/-- **The splitting points of the involution**: the own ones above row `r`, the reflection in
`[max(a_r, b_{r+1}), c₀]` in row `r`, and the Bender–Knuth reflection below. -/
def lrCut (κ : IntWeight d) (T : SemistandardYoungTableau ν) (r i k : ℕ) : ℕ :=
  if k < r then rowCountLt T k (i + 1)
  else if k = r then lowerCut T i r + violationColumn κ T r i - rowCountLt T r (i + 1)
  else lowerCut T i k + upperCut T i k - rowCountLt T k (i + 1)

/-- The row-count inequalities of a semistandard tableau used throughout. -/
theorem rowCountLt_chain (T : SemistandardYoungTableau ν) (i k : ℕ) :
    rowCountLt T k i ≤ rowCountLt T k (i + 1) ∧ rowCountLt T k (i + 1) ≤ rowCountLt T k (i + 2) ∧
      rowCountLt T (k + 1) (i + 2) ≤ rowCountLt T k (i + 1) ∧
      rowCountLt T (k + 1) (i + 1) ≤ rowCountLt T k i :=
  ⟨T.rowCountLt_mono k (by omega), T.rowCountLt_mono k (by omega), T.rowCountLt_succ_le k (i + 1),
    T.rowCountLt_succ_le k i⟩

/-- Above the violating row, the cut is the unchanged cumulative count. -/
theorem lrCut_of_lt {k : ℕ} (hk : k < r) : lrCut κ T r i k = rowCountLt T k (i + 1) := by
  simp [lrCut, hk]

/-- In the violating row, the cut reflects about the violating cell. -/
theorem lrCut_self : lrCut κ T r i r =
    lowerCut T i r + violationColumn κ T r i - rowCountLt T r (i + 1) := by
  simp [lrCut]

/-- Below the violating row, the cut is the Bender--Knuth reflection. -/
theorem lrCut_of_gt {k : ℕ} (hk : r < k) :
    lrCut κ T r i k = lowerCut T i k + upperCut T i k - rowCountLt T k (i + 1) := by
  simp [lrCut, not_lt.mpr hk.le, hk.ne']

/-- Below the violating row, the Bender–Knuth interval contains the own splitting point. -/
theorem lowerCut_le_le_upperCut (T : SemistandardYoungTableau ν) (i : ℕ) {k : ℕ}
    (hk : 1 ≤ k) :
    lowerCut T i k ≤ rowCountLt T k (i + 1) ∧ rowCountLt T k (i + 1) ≤ upperCut T i k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  obtain ⟨h1, h2, h3, h4⟩ := rowCountLt_chain T i (m + 1)
  obtain ⟨_, _, _, h8⟩ := rowCountLt_chain T i m
  simp only [lowerCut, upperCut, Nat.add_sub_cancel]
  omega

/-- **The splitting points of the involution are admissible.** -/
theorem isCut_lrCut (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    IsCut T i (lrCut κ T r i) := by
  have hr := balanceNat_add_lt hκ h
  have hr' : lowerCut T i r ≤ rowCountLt T r (i + 1) := by
    obtain ⟨h1, -, h3, -⟩ := rowCountLt_chain T i r
    simp only [lowerCut]
    omega
  have hc : rowCountLt T r (i + 1) ≤ violationColumn κ T r i ∧
      violationColumn κ T r i < rowCountLt T r (i + 2) := by
    simp only [violationColumn]
    omega
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := rowCountLt_chain T i k
    rcases lt_trichotomy k r with hk | rfl | hk
    · rw [lrCut_of_lt hk]
      exact h1
    · rw [lrCut_self]
      simp only [lowerCut] at hr' ⊢
      omega
    · rw [lrCut_of_gt hk]
      have := lowerCut_le_le_upperCut T i (k := k) (by omega)
      simp only [lowerCut] at this ⊢
      omega
  · obtain ⟨h1, h2, h3, h4⟩ := rowCountLt_chain T i k
    rcases lt_trichotomy k r with hk | rfl | hk
    · rw [lrCut_of_lt hk]
      exact h2
    · rw [lrCut_self]
      omega
    · rw [lrCut_of_gt hk]
      have := lowerCut_le_le_upperCut T i (k := k) (by omega)
      have hU : upperCut T i k ≤ rowCountLt T k (i + 2) := min_le_left _ _
      omega
  · obtain ⟨h1, h2, h3, h4⟩ := rowCountLt_chain T i k
    rcases lt_trichotomy k r with hk | rfl | hk
    · rw [lrCut_of_lt hk]
      exact h3
    · rw [lrCut_self]
      simp only [lowerCut] at hr' ⊢
      omega
    · rw [lrCut_of_gt hk]
      have := lowerCut_le_le_upperCut T i (k := k) (by omega)
      have hL : rowCountLt T (k + 1) (i + 2) ≤ lowerCut T i k := le_max_right _ _
      omega
  · obtain ⟨h1, h2, h3, h4⟩ := rowCountLt_chain T i k
    rcases lt_trichotomy (k + 1) r with hk | hk | hk
    · rw [lrCut_of_lt hk]
      exact h4
    · subst hk
      rw [lrCut_self]
      have hkey := violationColumn_lt hκ h
      omega
    · rw [lrCut_of_gt hk]
      have := lowerCut_le_le_upperCut T i (k := k + 1) (by omega)
      have hU : upperCut T i (k + 1) ≤ rowCountLt T k i := by
        simp only [upperCut, Nat.add_sub_cancel]
        exact min_le_right _ _

      omega

end SymmetricFunction.FiniteAlphabet.LittlewoodRichardson

end
