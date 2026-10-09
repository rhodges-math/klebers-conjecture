import KlebersConjecture.SymmetricFunctions.Bases.SchurBasis
import KlebersConjecture.Partitions.Rows
import Mathlib.Data.Finset.Lattice.Fold

/-!
# First-row support and projections

The largest first row in the Schur-coordinate support is zero for the zero function.
First-row projections select a specified integer first row and delete it on Schur vectors.

## Main results

* `topRow_le_iff`: the support characterization of a first-row bound.
* `firstRowProjection_schur`: the defining action on Schur functions.
* `firstRowProjection_eq_zero_of_topRow_lt`: projection above the support bound vanishes.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommRing R]

/-- The largest first row in Schur-coordinate support, with value zero for empty support. -/
def topRow (f : SymmetricFunction R) : ℕ :=
  ((schurBasis R).repr f).support.sup (fun μ => μ.rowLen 0)

/-- The zero symmetric function has first-row support bound zero. -/
@[simp]
theorem topRow_zero : topRow (0 : SymmetricFunction R) = 0 := by
  simp only [topRow, map_zero, Finsupp.support_zero, Finset.sup_empty, bot_eq_zero]

/-- Every nonzero Schur coordinate has first row at most the support bound. -/
theorem rowLen_le_topRow {f : SymmetricFunction R} {μ : YoungDiagram}
    (hμ : (schurBasis R).repr f μ ≠ 0) : μ.rowLen 0 ≤ topRow f := by
  unfold topRow
  exact Finset.le_sup (f := fun ν : YoungDiagram => ν.rowLen 0)
    (Finsupp.mem_support_iff.mpr hμ)

/-- A first-row bound is exactly a bound on all nonzero Schur coordinates. -/
theorem topRow_le_iff (f : SymmetricFunction R) (n : ℕ) :
    topRow f ≤ n ↔ ∀ μ, (schurBasis R).repr f μ ≠ 0 → μ.rowLen 0 ≤ n := by
  simp only [topRow, Finset.sup_le_iff, Finsupp.mem_support_iff]

/-- Coordinates above the first-row support bound vanish. -/
theorem schurCoordinate_eq_zero {f : SymmetricFunction R} {μ : YoungDiagram}
    (hμ : topRow f < μ.rowLen 0) : (schurBasis R).repr f μ = 0 := by
  by_contra h
  exact (not_le_of_gt hμ) (rowLen_le_topRow h)

/-- Schur-coordinate support is nonempty precisely for a nonzero symmetric function. -/
theorem schurSupport_nonempty_iff (f : SymmetricFunction R) :
    ((schurBasis R).repr f).support.Nonempty ↔ f ≠ 0 := by
  rw [Finsupp.support_nonempty_iff]
  exact (schurBasis R).repr.map_ne_zero_iff

/-- Select the integer first-row length on Schur vectors and delete that row linearly. -/
def firstRowProjection (R : Type*) [CommRing R] (n : ℤ) :
    SymmetricFunction R →ₗ[R] SymmetricFunction R :=
  (schurBasis R).constr R (fun μ =>
    if (μ.rowLen 0 : ℤ) = n then schur R (μ.dropRows 1) else 0)

/-- First-row projection selects and deletes the first row of a Schur vector. -/
@[simp]
theorem firstRowProjection_schur (n : ℤ) (μ : YoungDiagram) :
    firstRowProjection R n (schur R μ) =
      if (μ.rowLen 0 : ℤ) = n then schur R (μ.dropRows 1) else 0 := by
  rw [← schurBasis_apply μ]
  exact Module.Basis.constr_basis _ _ _ _

/-- Projection is the finite Schur-coordinate sum of the selected row deletions. -/
theorem firstRowProjection_apply (n : ℤ) (f : SymmetricFunction R) :
    firstRowProjection R n f = ((schurBasis R).repr f).sum
      (fun μ r => r • if (μ.rowLen 0 : ℤ) = n then schur R (μ.dropRows 1) else 0) :=
  Module.Basis.constr_apply _ _ _ _

/-- A negative integer selects no first row, so its projection is the zero linear map. -/
theorem firstRowProjection_neg {n : ℤ} (hn : n < 0) : firstRowProjection R n = 0 := by
  apply (schurBasis R).ext
  intro μ
  rw [schurBasis_apply, firstRowProjection_schur, LinearMap.zero_apply]
  have hne : (μ.rowLen 0 : ℤ) ≠ n := by omega
  exact ite_eq_right hne

/-- Projection above the largest supported first row vanishes. -/
theorem firstRowProjection_eq_zero_of_topRow_lt (f : SymmetricFunction R) {n : ℤ}
    (hn : (topRow f : ℤ) < n) : firstRowProjection R n f = 0 := by
  classical
  rw [firstRowProjection_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro μ hμ
  have hle := rowLen_le_topRow (Finsupp.mem_support_iff.mp hμ)
  have hne : (μ.rowLen 0 : ℤ) ≠ n := by omega
  simp only [ite_eq_right hne, smul_zero]

end SymmetricFunction
