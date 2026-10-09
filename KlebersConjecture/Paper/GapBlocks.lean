import KlebersConjecture.Paper.GapProjection
import KlebersConjecture.Paper.GapTails
import KlebersConjecture.SymmetricFunctions.Projection.RowProjectionFolds

/-! # Projection of rectangular gap blocks

The row-sum projections of a complementary pair delete the first half of the rows.
A lexicographically larger gap selects a row beyond the support at the first differing index.

## Main results

* `gapProjection_of_gap_eq` computes the projection in a fixed gap block.
* `gapProjection_of_gap_lt` annihilates every lexicographically smaller gap block.
-/

noncomputable section

namespace ComplementaryProducts

open SymmetricFunction

/-- The first-half row sum of a complementary pair is width plus the corresponding gap. -/
theorem rowLen_sum_complement (a b : ℕ) (μ : YoungDiagram)
    (hμ : μ ≤ YoungDiagram.rectangle a b) (i : Fin (a / 2)) :
    μ.rowLen i.val + (YoungDiagram.rectComplement a b μ).rowLen i.val = b + gap a μ i := by
  have hi : i.val < a := by have := i.isLt; omega
  rw [YoungDiagram.rowLen_rectComplement, ite_eq_left hi, gap_apply]
  have hb := YoungDiagram.rowLen_le_of_le_rectangle hμ (a - 1 - i.val)
  have hr := μ.rowLen_anti i.val (a - 1 - i.val) (by have := i.isLt; omega)
  omega

/-- A fixed gap projects to the tail product and the prescribed componentwise splitting. -/
theorem gapProjection_of_gap_eq (R : Type*) [CommRing R] (a b : ℕ)
    (g : Fin (a / 2) → ℕ) (hg : ValidGap a b g) (μ : YoungDiagram)
    (hμ : μ ≤ YoungDiagram.rectangle a b) (hgap : gap a μ = g) :
    gapProjection R a b g (schur R μ * schur R (YoungDiagram.rectComplement a b μ)) =
        schur R (μ.dropRows (a / 2)) *
          schur R ((YoungDiagram.rectComplement a b μ).dropRows (a / 2)) ∧
      s(μ.dropRows (a / 2), (YoungDiagram.rectComplement a b μ).dropRows (a / 2)) ∈
        splittings (gapShape a b g hg) := by
  constructor
  · rw [gapProjection_apply]
    apply firstRowProjection_fold_product
    intro i
    rw [rowLen_sum_complement a b μ hμ i, hgap]
  · rw [mk_mem_splittings]
    exact dropRows_add_dropRows_complement a b g hg μ hμ hgap

/-- Projection at a lexicographically larger gap annihilates a complementary Schur product. -/
theorem gapProjection_of_gap_lt (R : Type*) [CommRing R] (a b : ℕ)
    (g : Fin (a / 2) → ℕ) (μ : YoungDiagram) (hμ : μ ≤ YoungDiagram.rectangle a b)
    (hlt : toLex (gap a μ) < toLex g) :
    gapProjection R a b g (schur R μ * schur R (YoungDiagram.rectComplement a b μ)) = 0 := by
  obtain ⟨t, hbefore, hlarge⟩ := hlt
  change ∀ j, j < t → gap a μ j = g j at hbefore
  change gap a μ t < g t at hlarge
  rw [gapProjection_apply]
  apply firstRowProjection_fold_eq_zero (a / 2) _ μ
    (YoungDiagram.rectComplement a b μ) t
  · intro i hi
    rw [rowLen_sum_complement a b μ hμ i, hbefore i hi]
  · rw [rowLen_sum_complement a b μ hμ t]
    exact_mod_cast Nat.add_lt_add_left hlarge b

end ComplementaryProducts
