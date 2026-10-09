import KlebersConjecture.SymmetricFunctions.Projection.FirstRowProjection
import KlebersConjecture.SymmetricFunctions.LittlewoodRichardson.RowRemoval

/-! # First-row projections of Schur products

The largest possible first row is the sum of the input first rows. At that row,
Littlewood--Richardson row removal identifies the projection with the product of the tails.

## Main results

* `topRow_schur_mul_schur` gives the maximal supported row over a nonzero ring.
* `firstRowProjection_schur_mul_schur` projects a product at its top row.
* `firstRowProjection_product_sum` gives the projection at the explicit row sum.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommRing R]

/-- Schur product support is bounded by the sum of the input first rows over every ring. -/
theorem topRow_product_le (α β : YoungDiagram) :
    topRow (schur R α * schur R β) ≤ α.rowLen 0 + β.rowLen 0 := by
  rw [topRow_le_iff]
  intro ν hν
  rw [schurBasis_repr_schur_mul_schur] at hν
  apply rowLen_zero_le_of_lrCoeff_ne_zero α β ν
  intro h
  exact hν (by rw [h, Nat.cast_zero])

/-- Over a nonzero ring, the maximal supported first row is the input first-row sum. -/
theorem topRow_schur_mul_schur [Nontrivial R] (α β : YoungDiagram) :
    topRow (schur R α * schur R β) = α.rowLen 0 + β.rowLen 0 := by
  apply le_antisymm (topRow_product_le α β)
  have h : (schurBasis R).repr (schur R α * schur R β) (α + β) ≠ 0 := by
    rw [schurBasis_repr_schur_mul_schur, lrCoeff_add_eq_one, Nat.cast_one]
    exact one_ne_zero
  simpa only [YoungDiagram.rowLen_add] using rowLen_le_topRow h

/-- Projection strictly above the explicit input first-row sum vanishes over every ring. -/
theorem firstRowProjection_product_above (α β : YoungDiagram) {n : ℤ}
    (hn : ((α.rowLen 0 + β.rowLen 0 : ℕ) : ℤ) < n) :
    firstRowProjection R n (schur R α * schur R β) = 0 := by
  apply firstRowProjection_eq_zero_of_topRow_lt
  have h := topRow_product_le (R := R) α β
  omega

private theorem exists_firstRow (n : ℕ) (ν : YoungDiagram) (hν : ν.rowLen 0 ≤ n) :
    ∃ μ : YoungDiagram, μ.rowLen 0 = n ∧ μ.dropRows 1 = ν := by
  let rows : Fin (ν.colLen 0 + 1) → ℕ := fun i =>
    if i.val = 0 then n else ν.rowLen (i.val - 1)
  have ha : Antitone rows := by
    intro i j hij
    unfold rows
    split_ifs with hi hj
    · exact le_rfl
    · have hij' : i.val ≤ j.val := hij
      omega
    · exact (ν.rowLen_anti 0 (j.val - 1) (Nat.zero_le _)).trans hν
    · exact ν.rowLen_anti _ _ (Nat.sub_le_sub_right hij 1)
  let μ := YoungDiagram.ofRowLensFin rows ha
  refine ⟨μ, ?_, ?_⟩
  · exact YoungDiagram.rowLen_ofRowLensFin rows ha ⟨0, by omega⟩
  · apply YoungDiagram.rowLen_injective
    funext i
    rw [YoungDiagram.rowLen_dropRows]
    by_cases hi : i < ν.colLen 0
    · rw [YoungDiagram.rowLen_ofRowLensFin rows ha ⟨1 + i, by omega⟩]
      simp only [rows, Nat.add_eq_zero_iff, one_ne_zero, false_and, ite_false]
      congr 1
      omega
    · rw [YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le rows ha (by omega),
        YoungDiagram.rowLen_eq_zero_of_colLen_le (Nat.not_lt.mp hi)]

private theorem eq_of_firstRow_tail {μ ρ : YoungDiagram}
    (hrow : μ.rowLen 0 = ρ.rowLen 0) (ht : μ.dropRows 1 = ρ.dropRows 1) : μ = ρ := by
  apply YoungDiagram.rowLen_injective
  funext i
  cases i with
  | zero => exact hrow
  | succ i =>
    have h := congrArg (fun ξ : YoungDiagram => ξ.rowLen i) ht
    simpa only [YoungDiagram.rowLen_dropRows, Nat.add_comm 1] using h

/-- Projection at the explicit first-row sum is the Schur product of the row-deleted inputs. -/
theorem firstRowProjection_product_sum (α β : YoungDiagram) :
    firstRowProjection R ((α.rowLen 0 + β.rowLen 0 : ℕ) : ℤ)
      (schur R α * schur R β) =
        schur R (α.dropRows 1) * schur R (β.dropRows 1) := by
  classical
  let n := α.rowLen 0 + β.rowLen 0
  let c := (schurBasis R).repr (schur R α * schur R β)
  apply (schurBasis R).repr.injective
  apply Finsupp.ext
  intro ν
  have hterm (μ : YoungDiagram) (r : R) :
      (schurBasis R).repr
        (r • if (μ.rowLen 0 : ℤ) = n then schur R (μ.dropRows 1) else 0) ν =
      if μ.rowLen 0 = n ∧ μ.dropRows 1 = ν then r else 0 := by
    by_cases hm : μ.rowLen 0 = n
    · have hm' : (μ.rowLen 0 : ℤ) = n := by exact_mod_cast hm
      rw [ite_eq_left hm', map_smul, ← schurBasis_apply, Module.Basis.repr_self]
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
        mul_ite, mul_one, mul_zero, hm, true_and, eq_comm]
    · have hm' : (μ.rowLen 0 : ℤ) ≠ n := by exact_mod_cast hm
      simp only [ite_eq_right hm', smul_zero, map_zero, Finsupp.zero_apply,
        hm, false_and, ite_false]
  rw [firstRowProjection_apply, Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
  change (∑ μ ∈ c.support, (schurBasis R).repr
    (c μ • if (μ.rowLen 0 : ℤ) = (n : ℤ) then schur R (μ.dropRows 1) else 0) ν) = _
  simp_rw [hterm]
  rw [schurBasis_repr_schur_mul_schur]
  by_cases hν : ν.rowLen 0 ≤ n
  · obtain ⟨ρ, hρ, ht⟩ := exists_firstRow n ν hν
    have hc (μ : YoungDiagram) : μ.rowLen 0 = n ∧ μ.dropRows 1 = ν ↔ μ = ρ := by
      constructor
      · rintro ⟨hr, hd⟩
        exact eq_of_firstRow_tail (hr.trans hρ.symm) (hd.trans ht.symm)
      · rintro rfl
        exact ⟨hρ, ht⟩
    simp_rw [hc]
    have he : (∑ μ ∈ c.support, if μ = ρ then c μ else 0) = c ρ := by
      rw [Finset.sum_ite_eq']
      split_ifs with hmem
      · rfl
      · exact (Finsupp.notMem_support_iff.mp hmem).symm
    rw [he]
    change (schurBasis R).repr (schur R α * schur R β) ρ = _
    rw [schurBasis_repr_schur_mul_schur, lrCoeff_eq_lrCoeff_dropRows α β ρ hρ, ht]
  · have hz : lrCoeff (α.dropRows 1) (β.dropRows 1) ν = 0 := by
      by_contra h
      have hb := rowLen_zero_le_of_lrCoeff_ne_zero (α.dropRows 1) (β.dropRows 1) ν h
      simp only [YoungDiagram.rowLen_dropRows, Nat.add_zero] at hb
      have ha := α.rowLen_anti 0 1 (by omega)
      have hb' := β.rowLen_anti 0 1 (by omega)
      omega
    rw [hz, Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro μ _
    have hne : ¬(μ.rowLen 0 = n ∧ μ.dropRows 1 = ν) := by
      rintro ⟨hr, ht⟩
      have he := congrArg (fun ξ : YoungDiagram => ξ.rowLen 0) ht
      rw [YoungDiagram.rowLen_dropRows, Nat.add_zero] at he
      have ha := μ.rowLen_anti 0 1 (by omega)
      omega
    exact ite_eq_right hne

/-- Projection at the product's top row is the product of its first-row deletions. -/
theorem firstRowProjection_schur_mul_schur (α β : YoungDiagram) :
    firstRowProjection R (topRow (schur R α * schur R β) : ℤ)
      (schur R α * schur R β) =
        schur R (α.dropRows 1) * schur R (β.dropRows 1) := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
    have := h
    apply ext
    intro e
    exact Subsingleton.elim _ _
  | inr h =>
    have := h
    rw [topRow_schur_mul_schur]
    exact firstRowProjection_product_sum α β

end SymmetricFunction
