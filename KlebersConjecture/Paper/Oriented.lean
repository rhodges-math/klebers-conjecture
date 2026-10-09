import KlebersConjecture.Paper.Indices
import KlebersConjecture.Partitions.Rows
import KlebersConjecture.SymmetricFunctions.Map
import KlebersConjecture.SymmetricFunctions.Families.Schur

/-! # Ordered derivative-reduced splittings

Ordered splittings with a prescribed first hook select a nonempty second diagram.
The associated product uses first-row and first-column deletion on that diagram.

## Main results

* `mem_orientedSplittings` gives the sum, nonempty and hook-index conditions.
* `orientedSplittings_of_neg` gives the empty family at negative indices.
* `map_orientedPairProduct` preserves products under coefficient-ring maps.
-/

noncomputable section

open scoped Classical

namespace ComplementaryProducts

/-- Ordered splittings whose nonempty second member has first hook equal to the integer `n`. -/
def orientedSplittings (θ : YoungDiagram) (n : ℤ) :
    Finset (YoungDiagram × YoungDiagram) :=
  ((YoungDiagram.finite_Iic θ).toFinset.product
    (YoungDiagram.finite_Iic θ).toFinset).filter
      (fun q => q.1 + q.2 = θ ∧ q.2 ≠ ⊥ ∧
        ((q.2.rowLen 0 + q.2.colLen 0 - 1 : ℕ) : ℤ) = n)

/-- Ordered membership records exactly the splitting and prescribed positive hook conditions. -/
theorem mem_orientedSplittings (θ : YoungDiagram) (n : ℤ)
    (q : YoungDiagram × YoungDiagram) :
    q ∈ orientedSplittings θ n ↔ q.1 + q.2 = θ ∧ q.2 ≠ ⊥ ∧
      ((q.2.rowLen 0 + q.2.colLen 0 - 1 : ℕ) : ℤ) = n := by
  constructor
  · intro hq
    exact (Finset.mem_filter.mp hq).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    apply Finset.mem_product.mpr
    constructor
    · simpa only [Set.Finite.mem_toFinset, Set.mem_Iic] using
        (h.1 ▸ YoungDiagram.le_self_add q.1 q.2)
    · simpa only [Set.Finite.mem_toFinset, Set.mem_Iic] using
        (h.1 ▸ YoungDiagram.le_add_self q.1 q.2)

/-- Each first member is contained in the splitting target. -/
theorem left_le_of_mem_oriented {θ : YoungDiagram} {n : ℤ}
    {q : YoungDiagram × YoungDiagram} (hq : q ∈ orientedSplittings θ n) : q.1 ≤ θ :=
  ((mem_orientedSplittings θ n q).mp hq).1 ▸ YoungDiagram.le_self_add q.1 q.2

/-- Each second member is contained in the splitting target. -/
theorem right_le_of_mem_oriented {θ : YoungDiagram} {n : ℤ}
    {q : YoungDiagram × YoungDiagram} (hq : q ∈ orientedSplittings θ n) : q.2 ≤ θ :=
  ((mem_orientedSplittings θ n q).mp hq).1 ▸ YoungDiagram.le_add_self q.1 q.2

/-- Forgetting the order gives a member of the unordered splitting family. -/
theorem mk_mem_splittings_of_oriented {θ : YoungDiagram} {n : ℤ}
    {q : YoungDiagram × YoungDiagram} (hq : q ∈ orientedSplittings θ n) :
    s(q.1, q.2) ∈ splittings θ :=
  (mk_mem_splittings θ q.1 q.2).mpr ((mem_orientedSplittings θ n q).mp hq).1

/-- A negative integer cannot be the hook index of an ordered splitting. -/
theorem orientedSplittings_of_neg (θ : YoungDiagram) {n : ℤ} (hn : n < 0) :
    orientedSplittings θ n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have h := ((mem_orientedSplittings θ n q).mp hq).2.2
  have hnonneg := Int.natCast_nonneg (q.2.rowLen 0 + q.2.colLen 0 - 1)
  omega

/-- The empty target has no splitting with a nonempty second diagram. -/
theorem orientedSplittings_bot (n : ℤ) : orientedSplittings ⊥ n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hbot : q.2 = ⊥ := le_bot_iff.mp (right_le_of_mem_oriented hq)
  exact ((mem_orientedSplittings ⊥ n q).mp hq).2.1 hbot

/-- The first Schur function multiplied by the second diagram's corner-deleted Schur function. -/
def orientedPairProduct (R : Type*) [CommRing R]
    (q : YoungDiagram × YoungDiagram) : SymmetricFunction R :=
  SymmetricFunction.schur R q.1 * SymmetricFunction.schur R q.2.removeFirstRowCol

/-- The ordered product evaluates to its two prescribed Schur factors. -/
theorem orientedPairProduct_apply (R : Type*) [CommRing R]
    (q : YoungDiagram × YoungDiagram) :
    orientedPairProduct R q =
      SymmetricFunction.schur R q.1 * SymmetricFunction.schur R q.2.removeFirstRowCol := rfl

/-- Coefficient-ring maps preserve the ordered corner-deleted product. -/
theorem map_orientedPairProduct {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (q : YoungDiagram × YoungDiagram) :
    SymmetricFunction.map f (orientedPairProduct R q) = orientedPairProduct S q := by
  rw [orientedPairProduct_apply, map_mul, SymmetricFunction.map_schur,
    SymmetricFunction.map_schur, orientedPairProduct_apply]

end ComplementaryProducts
