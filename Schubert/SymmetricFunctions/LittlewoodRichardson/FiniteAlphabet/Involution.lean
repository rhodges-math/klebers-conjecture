import Schubert.SymmetricFunctions.LittlewoodRichardson.FiniteAlphabet.ViolationCut

/-! # Lattice tableau recutting involution

Recutting at the first lattice violation exchanges the two affected content coordinates.

## Main results

* `isFirstViolation_lrSwap`: recutting preserves the first violation.
* `lrSwap_lrSwap`: applying the recutting operation twice restores the tableau.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction.FiniteAlphabet.LittlewoodRichardson

open SemistandardYoungTableau

variable {d : ℕ} {ν : YoungDiagram} {κ : IntWeight d}
  {T : SemistandardYoungTableau ν} {r i : ℕ}

/-- **The Littlewood–Richardson involution**: the recut of `T` at the letter `i` with the
splitting points `SymmetricFunction.FiniteAlphabet.LittlewoodRichardson.lrCut`. -/
def lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) : SemistandardYoungTableau ν :=
  recut T i (lrCut κ T r i) (isCut_lrCut hκ h)

/-- Recutting preserves cumulative row counts away from the changed cutoff. -/
theorem rowCountLt_lrSwap_of_ne (hκ : Antitone κ) (h : IsFirstViolation κ T r i) (k : ℕ)
    {x : ℕ} (hx : x ≠ i + 1) : rowCountLt (lrSwap hκ h) k x = rowCountLt T k x := by
  rcases le_or_gt x i with hxi | hxi
  · exact rowCountLt_recut_of_le _ k hxi
  · exact rowCountLt_recut_of_ge _ k (by omega)

/-- The changed cumulative row count equals the prescribed cut. -/
theorem rowCountLt_lrSwap_succ (hκ : Antitone κ) (h : IsFirstViolation κ T r i) (k : ℕ) :
    rowCountLt (lrSwap hκ h) k (i + 1) = lrCut κ T r i k :=
  rowCountLt_recut_succ _ k

/-- Above the violating row, nothing changes. -/
theorem rowCountLt_lrSwap_of_lt (hκ : Antitone κ) (h : IsFirstViolation κ T r i) {k : ℕ}
    (hk : k < r) (x : ℕ) : rowCountLt (lrSwap hκ h) k x = rowCountLt T k x := by
  by_cases hx : x = i + 1
  · subst hx
    rw [rowCountLt_lrSwap_succ, lrCut_of_lt hk]
  · exact rowCountLt_lrSwap_of_ne hκ h k hx

/-- Recutting preserves row multiplicities outside the affected rows or letters. -/
theorem rowCount_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) (k x : ℕ)
    (hkx : k < r ∨ (x ≠ i ∧ x ≠ i + 1)) : rowCount (lrSwap hκ h) k x = rowCount T k x := by
  rcases hkx with hk | ⟨hx, hx'⟩
  · simp only [rowCount, rowCountLt_lrSwap_of_lt hκ h hk]
  · simp only [rowCount]
    rw [rowCountLt_lrSwap_of_ne hκ h k (by omega), rowCountLt_lrSwap_of_ne hκ h k hx']

/-- Recutting preserves prefix multiplicities outside the affected rows or letters. -/
theorem countBelow_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) (R x : ℕ)
    (hRx : R ≤ r ∨ (x ≠ i ∧ x ≠ i + 1)) : countBelow (lrSwap hκ h) R x = countBelow T R x := by
  refine Finset.sum_congr rfl fun k hk => rowCount_lrSwap hκ h k x ?_
  rcases hRx with hR | hx
  · exact Or.inl (lt_of_lt_of_le (Finset.mem_range.mp hk) hR)
  · exact Or.inr hx

/-- The cut in the violating row does not pass its violating cell. -/
theorem lrCut_self_le (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    lrCut κ T r i r ≤ violationColumn κ T r i := by
  have hr := balanceNat_add_lt hκ h
  obtain ⟨h1, -, h3, -⟩ := rowCountLt_chain T i r
  rw [lrCut_self]
  simp only [lowerCut, violationColumn] at *
  omega

/-- **The involution keeps the first violation.** -/
theorem isFirstViolation_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    IsFirstViolation κ (lrSwap hκ h) r i where
  lt := h.lt
  viol := by
    have hb := balance_lt_rowCount h
    have hcut := lrCut_self_le hκ h
    have hr := balanceNat_add_lt hκ h
    have he := balanceNat_eq hκ h
    rw [countBelow_lrSwap hκ h r i (Or.inl le_rfl), countBelow_succ,
      countBelow_lrSwap hκ h r (i + 1) (Or.inl le_rfl)]
    have hrc : rowCount (lrSwap hκ h) r (i + 1) = rowCountLt T r (i + 2) - lrCut κ T r i r := by
      simp only [rowCount]
      rw [rowCountLt_lrSwap_of_ne hκ h r (by omega), rowCountLt_lrSwap_succ]
    have hlt : balanceNat κ T r i < rowCount (lrSwap hκ h) r (i + 1) := by
      rw [hrc]
      simp only [violationColumn] at hcut
      omega
    have hlt' : (balanceNat κ T r i : ℤ) < rowCount (lrSwap hκ h) r (i + 1) := by exact_mod_cast hlt
    rw [he, balance] at hlt'
    push_cast
    linarith
  row_min r' hr' j hj := by
    rw [countBelow_lrSwap hκ h (r' + 1) (j + 1) (Or.inl hr'),
      countBelow_lrSwap hκ h r' j (Or.inl hr'.le)]
    exact h.row_min r' hr' j hj
  letter_max j hij hj := by
    rw [countBelow_lrSwap hκ h (r + 1) (j + 1) (Or.inr ⟨by omega, by omega⟩),
      countBelow_lrSwap hκ h r j (Or.inl le_rfl)]
    exact h.letter_max j hij hj

/-- Recutting preserves the balance before the first violating row. -/
theorem balance_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    balance κ (lrSwap hκ h) r i = balance κ T r i := by
  simp only [balance, countBelow_lrSwap hκ h r _ (Or.inl le_rfl)]

/-- Recutting preserves the column of the first violating cell. -/
theorem violationColumn_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    violationColumn κ (lrSwap hκ h) r i = violationColumn κ T r i := by
  simp only [violationColumn, balanceNat, balance_lrSwap hκ h,
    rowCountLt_lrSwap_of_ne hκ h r (by omega :
    i + 2 ≠ i + 1)]

/-- Recutting preserves the lower Bender--Knuth boundary. -/
theorem lowerCut_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) (k : ℕ) :
    lowerCut (lrSwap hκ h) i k = lowerCut T i k := by
  simp only [lowerCut, rowCountLt_lrSwap_of_ne hκ h _ (by omega : i ≠ i + 1),
    rowCountLt_lrSwap_of_ne hκ h _ (by omega : i + 2 ≠ i + 1)]

/-- Recutting preserves the upper Bender--Knuth boundary. -/
theorem upperCut_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) (k : ℕ) :
    upperCut (lrSwap hκ h) i k = upperCut T i k := by
  simp only [upperCut, rowCountLt_lrSwap_of_ne hκ h _ (by omega : i ≠ i + 1),
    rowCountLt_lrSwap_of_ne hκ h _ (by omega : i + 2 ≠ i + 1)]

/-- The splitting points of the involution, computed on the image, are the own ones of `T`. -/
theorem lrCut_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    lrCut κ (lrSwap hκ h) r i = fun k => rowCountLt T k (i + 1) := by
  funext k
  rcases lt_trichotomy k r with hk | rfl | hk
  · rw [lrCut_of_lt hk, rowCountLt_lrSwap_succ, lrCut_of_lt hk]
  · have hr := balanceNat_add_lt hκ h
    obtain ⟨h1, -, h3, -⟩ := rowCountLt_chain T i k
    rw [lrCut_self, lowerCut_lrSwap, violationColumn_lrSwap, rowCountLt_lrSwap_succ, lrCut_self]
    simp only [lowerCut, violationColumn] at *
    omega
  · have := lowerCut_le_le_upperCut T i (k := k) (by omega)
    rw [lrCut_of_gt hk, lowerCut_lrSwap, upperCut_lrSwap, rowCountLt_lrSwap_succ, lrCut_of_gt hk]
    omega

/-- Equal cut functions determine equal recut tableaux. -/
theorem recut_congr {v : ℕ} {cut cut' : ℕ → ℕ} (hc : IsCut T v cut) (hc' : IsCut T v cut')
    (h : cut = cut') : recut T v cut hc = recut T v cut' hc' := by
  subst h
  rfl

/-- **The involution is an involution.** -/
theorem lrSwap_lrSwap (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    lrSwap hκ (isFirstViolation_lrSwap hκ h) = T := by
  have hcut := isCut_lrCut hκ h
  have hown := isCut_rowCountLt T i
  calc lrSwap hκ (isFirstViolation_lrSwap hκ h)
      = recut (recut T i (lrCut κ T r i) hcut) i (fun k => rowCountLt T k (i + 1))
          (hcut.recut hown) :=
        recut_congr _ _ (lrCut_lrSwap hκ h)
    _ = recut T i (fun k => rowCountLt T k (i + 1)) hown := recut_recut hcut hown
    _ = T := recut_rowCountLt T i

/-- The violating row is a row of the shape. -/
theorem lt_colLen (hκ : Antitone κ) (h : IsFirstViolation κ T r i) : r < ν.colLen 0 := by
  by_contra hc
  have := balanceNat_add_lt hκ h
  simp only [rowCountLt_eq_zero_of_colLen_le T (not_lt.mp hc)] at this
  omega

/-- Recutting preserves the content of every unaffected letter. -/
theorem content_lrSwap_of_ne (hκ : Antitone κ) (h : IsFirstViolation κ T r i) {x : ℕ}
    (hx : x ≠ i) (hx' : x ≠ i + 1) : content (lrSwap hκ h) x = content T x :=
  content_recut_of_ne _ hx hx'

/-- Recutting preserves the total content of the two affected letters. -/
theorem content_lrSwap_pair (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    content (lrSwap hκ h) i + content (lrSwap hκ h) (i + 1) = content T i + content T (i + 1) :=
  content_recut_add _

/-- The telescoping identity of the Bender–Knuth reflection below the violating row. -/
theorem sum_Ico_lrCut (κ : IntWeight d) (T : SemistandardYoungTableau ν) (r i m : ℕ) :
    ∑ k ∈ Finset.Ico (r + 1) (r + 1 + m), (lrCut κ T r i k - rowCountLt T k i) +
        (rowCountLt T (r + 1) (i + 2) - upperCut T i (r + 1)) =
      (rowCountLt T (r + 1 + m) (i + 2) - upperCut T i (r + 1 + m)) +
        ∑ k ∈ Finset.Ico (r + 1) (r + 1 + m),
          (rowCountLt T k (i + 2) - rowCountLt T k (i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show r + 1 + (m + 1) = r + 1 + m + 1 by omega, Finset.sum_Ico_succ_top (by omega),
      Finset.sum_Ico_succ_top (by omega)]
    have hk : r < r + 1 + m := by omega
    have hfac := lowerCut_le_le_upperCut T i (k := r + 1 + m) (by omega)
    have hUb : upperCut T i (r + 1 + m) ≤ rowCountLt T (r + 1 + m) (i + 2) := min_le_left _ _
    obtain ⟨h1, h2, h3, h4⟩ := rowCountLt_chain T i (r + 1 + m)
    have hU : upperCut T i (r + 1 + m + 1) =
        min (rowCountLt T (r + 1 + m + 1) (i + 2)) (rowCountLt T (r + 1 + m) i) := by
      simp [upperCut]
    rw [lrCut_of_gt hk, hU]
    simp only [lowerCut] at hfac ⊢
    omega

/-- **The involution exchanges the letters `i` and `i + 1` on the cells read after the
violation**: `#i(T*) = #(i+1)(T) + κ_{i+1} − κ_i − 1`, in the additive form `#i(T*) + E + 1
+ #(i+1)(rows < r) = #(i+1)(T) + #i(rows < r)`. -/
theorem content_lrSwap_add (hκ : Antitone κ) (h : IsFirstViolation κ T r i) :
    content (lrSwap hκ h) i + balanceNat κ T r i + 1 + countBelow T r (i + 1) =
      content T (i + 1) + countBelow T r i := by
  have hM := lt_colLen hκ h
  set M := ν.colLen 0 with hMdef
  have h1 : content (lrSwap hκ h) i = ∑ k ∈ Finset.range M, (lrCut κ T r i k - rowCountLt T k i) :=
    content_recut _
  have h2 : content T (i + 1) =
      ∑ k ∈ Finset.range M, (rowCountLt T k (i + 2) - rowCountLt T k (i + 1)) :=
    content_succ_eq_sum T i
  have hsplit : ∀ f : ℕ → ℕ, ∑ k ∈ Finset.range M, f k =
      ∑ k ∈ Finset.range r, f k + f r + ∑ k ∈ Finset.Ico (r + 1) (r + 1 + (M - (r + 1))), f k := by
    intro f
    have hM' : r + 1 + (M - (r + 1)) = M := by omega
    rw [hM', Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive f (Nat.zero_le r) hM.le,
      Finset.sum_eq_sum_Ico_succ_bot hM, ← add_assoc, Finset.range_eq_Ico]
  have htel := sum_Ico_lrCut κ T r i (M - (r + 1))
  have hzero : rowCountLt T (r + 1 + (M - (r + 1))) (i + 2) = 0 :=
    rowCountLt_eq_zero_of_colLen_le T (by omega) _
  have habove : ∑ k ∈ Finset.range r, (lrCut κ T r i k - rowCountLt T k i) = countBelow T r i :=
    Finset.sum_congr rfl fun k hk => by rw [lrCut_of_lt (Finset.mem_range.mp hk)]; rfl
  have habove' : ∑ k ∈ Finset.range r, (rowCountLt T k (i + 2) - rowCountLt T k (i + 1)) =
      countBelow T r (i + 1) := rfl
  have hr := balanceNat_add_lt hκ h
  obtain ⟨g1, g2, g3, g4⟩ := rowCountLt_chain T i r
  have hrow : lrCut κ T r i r - rowCountLt T r i =
      (rowCountLt T (r + 1) (i + 2) - upperCut T i (r + 1)) +
        (violationColumn κ T r i - rowCountLt T r (i + 1)) := by
    rw [lrCut_self]
    simp only [lowerCut, upperCut, violationColumn, Nat.add_sub_cancel]
    omega
  rw [h1, h2, hsplit, hsplit, habove, habove', hrow]
  rw [hzero, Nat.zero_sub, zero_add] at htel
  simp only [violationColumn] at *
  omega

end SymmetricFunction.FiniteAlphabet.LittlewoodRichardson

end
