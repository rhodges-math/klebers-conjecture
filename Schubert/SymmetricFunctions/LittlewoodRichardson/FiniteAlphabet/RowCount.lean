import Schubert.SymmetricFunctions.LittlewoodRichardson.FiniteAlphabet.Laurent
import TauCeti.Combinatorics.Young.BenderKnuth
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic

/-! # Tableau row counts and lattice words

Row and prefix counts describe the lattice inequalities for semistandard tableaux.

## Main results

* `content_eq_countBelow`: total prefix counts recover tableau content.
* `antitone_add_weightVec`: lattice inequalities make the shifted content decreasing.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction.FiniteAlphabet.LittlewoodRichardson

open SemistandardYoungTableau

variable {ν : YoungDiagram}

/-- The number of occurrences of a letter in a tableau row. -/
def rowCount (T : SemistandardYoungTableau ν) (r x : ℕ) : ℕ :=
  rowCountLt T r (x + 1) - rowCountLt T r x

/-- The number of entries `x` in the rows `0, …, R − 1` of a tableau. -/
def countBelow (T : SemistandardYoungTableau ν) (R x : ℕ) : ℕ :=
  ∑ r ∈ Finset.range R, rowCount T r x

/-- There are no entries in the empty row prefix. -/
@[simp]
theorem countBelow_zero (T : SemistandardYoungTableau ν) (x : ℕ) : countBelow T 0 x = 0 := by
  simp [countBelow]

/-- Adding a row adds its multiplicity to the row-prefix count. -/
theorem countBelow_succ (T : SemistandardYoungTableau ν) (R x : ℕ) :
    countBelow T (R + 1) x = countBelow T R x + rowCount T R x :=
  Finset.sum_range_succ _ _

/-- Row-prefix multiplicities increase with the prefix length. -/
theorem countBelow_mono (T : SemistandardYoungTableau ν) (x : ℕ) {R R' : ℕ}
    (h : R ≤ R') : countBelow T R x ≤ countBelow T R' x :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- A row beyond the height has zero multiplicity. -/
theorem rowCount_eq_zero_of_colLen_le (T : SemistandardYoungTableau ν) {r : ℕ}
    (hr : ν.colLen 0 ≤ r) (x : ℕ) : rowCount T r x = 0 := by
  simp [rowCount, rowCountLt_eq_zero_of_colLen_le T hr]

/-- Below the last row, the counts no longer change. -/
theorem countBelow_of_colLen_le (T : SemistandardYoungTableau ν) (x : ℕ) {R : ℕ}
    (hR : ν.colLen 0 ≤ R) : countBelow T R x = countBelow T (ν.colLen 0) x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hR
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← add_assoc, countBelow_succ, ih (Nat.le_add_right _ _),
      rowCount_eq_zero_of_colLen_le T (Nat.le_add_right _ _), add_zero]

/-- **The content counts row by row.** -/
theorem content_eq_countBelow (T : SemistandardYoungTableau ν) (x : ℕ) :
    content T x = countBelow T (ν.colLen 0) x :=
  content_eq_sum T x

/-- A prefix containing every row recovers tableau content. -/
theorem content_eq_countBelow_of_le (T : SemistandardYoungTableau ν) (x : ℕ) {R : ℕ}
    (hR : ν.colLen 0 ≤ R) : content T x = countBelow T R x := by
  rw [content_eq_countBelow, countBelow_of_colLen_le T x hR]

/-- Every row-prefix multiplicity is bounded by total content. -/
theorem countBelow_le_content (T : SemistandardYoungTableau ν) (R x : ℕ) :
    countBelow T R x ≤ content T x := by
  rcases le_total R (ν.colLen 0) with h | h
  · rw [content_eq_countBelow]
    exact countBelow_mono T x h
  · rw [content_eq_countBelow_of_le T x h]

variable {d : ℕ}

/-- An integer weight, read as a function of the letter (zero beyond the alphabet). -/
def weightAt (κ : IntWeight d) (i : ℕ) : ℤ := if h : i < d then κ ⟨i, h⟩ else 0

/-- Inside the alphabet, extension by zero agrees with the weight. -/
theorem weightAt_of_lt (κ : IntWeight d) {i : ℕ} (h : i < d) : weightAt κ i = κ ⟨i, h⟩ := by
  simp [weightAt, h]

/-- A finite weight is unchanged at its own finite indices. -/
@[simp]
theorem weightAt_val (κ : IntWeight d) (i : Fin d) : weightAt κ i = κ i := by
  rw [weightAt_of_lt κ i.isLt]

/-- **The lattice condition, row-count form**: for every row `r` and every letter `i` with `i +
1 < d`, `κ_{i+1} + #{i + 1 in rows ≤ r} ≤ κ_i + #{i in rows < r}`. This is the condition
that `κ` plus the content of every prefix of the reverse row word stays weakly decreasing
(`SymmetricFunction.FiniteAlphabet.LittlewoodRichardson.isLatticeFrom_iff`). -/
def IsLattice (κ : IntWeight d) (T : SemistandardYoungTableau ν) : Prop :=
  ∀ r i : ℕ, i + 1 < d → weightAt κ (i + 1) + countBelow T (r + 1) (i + 1) ≤
    weightAt κ i + countBelow T r i

/-- It suffices to check the rows up to the height of the shape. -/
theorem isLattice_iff_le (κ : IntWeight d) (T : SemistandardYoungTableau ν) :
    IsLattice κ T ↔ ∀ r ≤ ν.colLen 0, ∀ i < d, i + 1 < d →
      weightAt κ (i + 1) + countBelow T (r + 1) (i + 1) ≤
    weightAt κ i + countBelow T r i := by
  refine ⟨fun h r _ i _ hi => h r i hi, fun h r i hi => ?_⟩
  rcases le_total r (ν.colLen 0) with hr | hr
  · exact h r hr i (by omega) hi
  · have h' := h (ν.colLen 0) le_rfl i (by omega) hi
    rwa [countBelow_of_colLen_le T _ (by omega : ν.colLen 0 ≤ r + 1),
      countBelow_of_colLen_le T _ hr, ← countBelow_of_colLen_le T _ (by omega :
        ν.colLen 0 ≤ ν.colLen 0 + 1)]

/-- The lattice inequalities of a finite tableau are decidable. -/
instance instDecidablePredIsLattice (κ : IntWeight d) :
    DecidablePred (IsLattice (ν := ν) κ) := fun T =>
  decidable_of_iff _ (isLattice_iff_le κ T).symm

/-- The content of a bounded tableau, as an integer weight. -/
def weightVec (T : TauCeti.BoundedSSYT d ν) : IntWeight d := fun i => (content T.1 i : ℤ)

/-- **A lattice tableau ends at a weakly decreasing weight.** -/
theorem antitone_add_weightVec {κ : IntWeight d} {T : TauCeti.BoundedSSYT d ν}
    (h : IsLattice κ T.1) : Antitone (κ + weightVec T) := by
  have hstep : ∀ i : ℕ, ∀ hi : i + 1 < d,
      (κ + weightVec T) ⟨i + 1, hi⟩ ≤ (κ + weightVec T) ⟨i, by omega⟩ := by
    intro i hi
    have h1 := h (ν.colLen 0) i hi
    rw [countBelow_of_colLen_le T.1 _ (Nat.le_succ _), ← content_eq_countBelow,
      ← content_eq_countBelow, weightAt_of_lt κ hi, weightAt_of_lt κ (by omega)] at h1
    simpa [weightVec] using h1
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Fin.mk_le_mk] at hab
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    exact (hstep (a + m) (by omega)).trans (ih (by omega) (by omega))

end SymmetricFunction.FiniteAlphabet.LittlewoodRichardson

end
