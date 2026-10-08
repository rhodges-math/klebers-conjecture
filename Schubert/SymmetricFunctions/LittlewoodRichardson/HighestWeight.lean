import Schubert.SymmetricFunctions.LittlewoodRichardson.Coefficients
import Schubert.Partitions.Basic

/-! # Highest-weight tableaux and the maximal Schur coefficient

The tableau with its row index in every cell is the unique tableau of its shape's content.
It contributes the coefficient one at the componentwise sum of two diagrams.

## Main results

* `lrCoeff_eq_tableau_count` expresses stable coefficients as finite tableau counts.
* `lrCoeff_add_eq_one` identifies the coefficient at the componentwise sum.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction

open FiniteAlphabet.LittlewoodRichardson SemistandardYoungTableau

/-- A sufficiently large finite alphabet counts the stable natural Schur coefficient. -/
theorem lrCoeff_eq_tableau_count (α β γ : YoungDiagram) (n : ℕ)
    (hα : α.colLen 0 ≤ n) (hγ : γ.colLen 0 ≤ n)
    (hf : ∀ ν ∈ ((schurBasis ℤ).repr (schur ℤ α * schur ℤ β)).support,
      ν.colLen 0 ≤ n) :
    lrCoeff α β γ =
      (Finset.univ.filter fun T : TauCeti.BoundedSSYT n β =>
        IsLattice (fun i : Fin n => (α.rowLen i : ℤ)) T.1 ∧
          (fun i : Fin n => (α.rowLen i : ℤ)) + weightVec T =
            (fun i : Fin n => (γ.rowLen i : ℤ))).card := by
  apply Int.ofNat_inj.mp
  rw [intCast_lrCoeff]
  exact schurBasis_repr_mul_eq_count α β γ n hα hγ hf

private theorem rowCount_highestWeight (β : YoungDiagram) (r x : ℕ) :
    rowCount (highestWeight β) r x = if r = x then β.rowLen r else 0 := by
  classical
  have h (y : ℕ) : rowCountLt (highestWeight β) r y =
      if r < y then β.rowLen r else 0 := by
    unfold rowCountLt
    have he : (Finset.range (β.rowLen r)).filter (fun c => highestWeight β r c < y) =
        (Finset.range (β.rowLen r)).filter (fun _ => r < y) := by
      apply Finset.filter_congr
      intro c hc
      rw [highestWeight_apply, ite_eq_left
        (YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_range.mp hc))]
    rw [he]
    by_cases hr : r < y <;> simp [hr]
  rw [rowCount, h (x + 1), h x]
  split_ifs <;> omega

private theorem countBelow_highestWeight (β : YoungDiagram) (r x : ℕ) :
    countBelow (highestWeight β) r x = if x < r then β.rowLen x else 0 := by
  simp only [countBelow, rowCount_highestWeight]
  rw [Finset.sum_ite_eq']
  simp

/-- The highest-weight tableau satisfies the lattice condition from any partition weight. -/
theorem isLattice_highestWeight (α β : YoungDiagram) (n : ℕ) :
    IsLattice (fun i : Fin n => (α.rowLen i : ℤ)) (highestWeight β) := by
  intro r i hi
  rw [weightAt_of_lt _ hi, weightAt_of_lt _ (by omega)]
  simp only [countBelow_highestWeight]
  have ha := α.rowLen_anti i (i + 1) (by omega)
  have hb := β.rowLen_anti i (i + 1) (by omega)
  split_ifs <;> omega

private theorem content_eq_rows_of_weight (α β : YoungDiagram) (n : ℕ)
    (hβ : β.colLen 0 ≤ n) (T : TauCeti.BoundedSSYT n β)
    (hw : (fun i : Fin n => (α.rowLen i : ℤ)) + weightVec T =
      (fun i : Fin n => ((α + β).rowLen i : ℤ))) :
    ⇑(content T.1) = β.rowLen := by
  funext i
  by_cases hi : i < n
  · have h := congrFun hw ⟨i, hi⟩
    simp only [Pi.add_apply, weightVec, YoungDiagram.rowLen_add, Nat.cast_add] at h
    omega
  · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (hβ.trans (Nat.not_lt.mp hi))]
    rw [content_apply]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    obtain ⟨hc, he⟩ := Finset.mem_filter.mp hc
    have hb := T.entry_lt hc
    omega

/-- The coefficient of the componentwise sum of two diagrams is one. -/
theorem lrCoeff_add_eq_one (α β : YoungDiagram) : lrCoeff α β (α + β) = 1 := by
  classical
  obtain ⟨n, hα, hab, hf⟩ := exists_lr_alphabet_bound α β (α + β)
  have hβ : β.colLen 0 ≤ n := by
    rw [YoungDiagram.colLen_add] at hab
    exact (le_max_right _ _).trans hab
  rw [lrCoeff_eq_tableau_count α β (α + β) n hα hab hf]
  let T : TauCeti.BoundedSSYT n β := ⟨highestWeight β, by
    intro i c hc
    rw [highestWeight_apply, ite_eq_left hc]
    exact (YoungDiagram.mem_iff_lt_colLen.mp hc).trans_le
      ((β.colLen_anti 0 c (Nat.zero_le c)).trans hβ)⟩
  have hT : IsLattice (fun i : Fin n => (α.rowLen i : ℤ)) T.1 ∧
      (fun i : Fin n => (α.rowLen i : ℤ)) + weightVec T =
        (fun i : Fin n => ((α + β).rowLen i : ℤ)) := by
    refine ⟨isLattice_highestWeight α β n, ?_⟩
    funext i
    change (α.rowLen i : ℤ) + (content (highestWeight β) i : ℤ) = _
    rw [content_highestWeight, YoungDiagram.rowLen_add, Nat.cast_add]
  have he : (Finset.univ.filter fun U : TauCeti.BoundedSSYT n β =>
      IsLattice (fun i : Fin n => (α.rowLen i : ℤ)) U.1 ∧
        (fun i : Fin n => (α.rowLen i : ℤ)) + weightVec U =
          (fun i : Fin n => ((α + β).rowLen i : ℤ))) = {T} := by
    apply Finset.ext
    intro U
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hU
      apply Subtype.ext
      exact eq_highestWeight_of_content_eq_rowLen
        (content_eq_rows_of_weight α β n hβ U hU.2)
    · rintro rfl
      exact hT
  rw [he, Finset.card_singleton]

end SymmetricFunction
