import KlebersConjecture.SymmetricFunctions.ForMathlib.FiniteMonomialWeights
import KlebersConjecture.SymmetricFunctions.Families.Monomial

/-! # Labelled row weights of monomial symmetric functions

## Main results

* `sum_injective_row_weights` gives the row-multiplicity normalization.
-/

noncomputable section

namespace SymmetricFunction

variable {R σ : Type*} [CommSemiring R] [Fintype σ] [DecidableEq σ]

private theorem rowWeight_multiset (μ : YoungDiagram) :
    Finset.univ.val.map (TauCeti.rowLenWeight (μ.colLen 0) μ) = (μ.rowLens : Multiset ℕ) := by
  rw [Fin.univ_val_map]
  have he : List.ofFn (fun i : Fin (μ.colLen 0) =>
      TauCeti.rowLenWeight (μ.colLen 0) μ i) = μ.rowLens := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, YoungDiagram.length_rowLens]
    · intro i hi hj
      simp only [List.getElem_ofFn, TauCeti.rowLenWeight_apply, YoungDiagram.get_rowLens]
  rw [he]

/-- Labelled injective row assignments count each finite monomial by row multiplicity factorials. -/
theorem sum_injective_row_weights (μ : YoungDiagram) :
    (∑ f : Fin (μ.colLen 0) ↪ σ, ∏ i, MvPolynomial.X (f i) ^ μ.rowLen i.val :
      MvPolynomial σ R) =
      (∏ r ∈ μ.rowLens.toFinset, (μ.rowLens.count r).factorial : ℕ) •
        MvPolynomial.msymm σ R (TauCeti.shapePartition μ) := by
  classical
  let w := TauCeti.rowLenWeight (μ.colLen 0) μ
  have hw : w.support = Finset.univ := by
    ext i
    simp only [Finsupp.mem_support_iff, Finset.mem_univ, iff_true, w,
      TauCeti.rowLenWeight_apply]
    have hm : (i.val, 0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr i.isLt
    exact (YoungDiagram.mem_iff_lt_rowLen.mp hm).ne'
  have hrows : Finset.univ.val.map w = (μ.rowLens : Multiset ℕ) := rowWeight_multiset μ
  have he := MvPolynomial.sum_embeddings_eq_msymm_of_parts (R := R) (σ := σ) w hw
    (TauCeti.shapePartition μ) (by rw [TauCeti.shapePartition_parts]; exact hrows.symm)
  have himage : Finset.univ.image w = μ.rowLens.toFinset := by
    have h := congrArg Multiset.toFinset hrows
    rw [Fin.univ_image_def]
    simpa only [Fin.univ_val_map, List.toFinset_coe] using h
  have hc (r : ℕ) : Fintype.card {i : Fin (μ.colLen 0) // w i = r} = μ.rowLens.count r := by
    rw [Fintype.card_weightFiber, hrows]
    exact Multiset.coe_count _ _
  rw [himage] at he
  simp_rw [hc] at he
  simpa only [w, TauCeti.rowLenWeight_apply] using he

end SymmetricFunction
