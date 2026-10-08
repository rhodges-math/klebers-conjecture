import Schubert.SymmetricFunctions.JacobiTrudi.JacobiTrudi
import Schubert.SymmetricFunctions.Presentations.CompleteCalculus
import Schubert.SymmetricFunctions.ForMathlib.GeneratorDeterminant
import Schubert.SymmetricFunctions.Bases.SchurBasis
import Schubert.Partitions.Rows

/-!
# Complete-generator calculus of Schur functions

The maximal complete index occurs only in the upper right Jacobi--Trudi entry.

## Main results

* `completeCoeff_schur` extracts the signed corner-deleted Schur function.
* `degreeOf_schur` gives exact degree one over a nonzero coefficient ring.
* `completeDerivation_schur` differentiates at and above the maximal complete index.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommRing R]

private theorem complete_degree_zero (n : ℕ+) (k : ℤ) (hk : k < (n.val : ℤ)) :
    ((completePresentation R).symm (complete R k)).degreeOf n = 0 := by
  by_cases hn : k < 0
  · rw [complete_neg k hn, map_zero, MvPolynomial.degreeOf_zero]
  by_cases hz : k = 0
  · subst k
    rw [complete_zero, map_one, MvPolynomial.degreeOf_one]
  let m : ℕ+ := ⟨k.toNat, by omega⟩
  have hm : (m.val : ℤ) = k := by dsimp [m]; omega
  rw [← hm, completePresentation_symm_complete]
  apply MvPolynomial.degreeOf_X_of_ne
  intro he
  have := congrArg (fun x : ℕ+ => (x.val : ℤ)) he
  omega

private theorem det_degree_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ+) (A : Matrix ι ι (SymmetricFunction R))
    (h : ∀ i j, ((completePresentation R).symm (A i j)).degreeOf n = 0) :
    ((completePresentation R).symm A.det).degreeOf n = 0 := by
  change ((completePresentation R).symm.toRingHom A.det).degreeOf n = 0
  rw [(completePresentation R).symm.toRingHom.map_det]
  exact MvPolynomial.degreeOf_det_eq_zero n _ h

private theorem minor_degree_zero (τ : YoungDiagram) (L : ℕ) (hh : τ.colLen 0 = L + 1)
    (n : ℕ+) (hn : n.val = τ.rowLen 0 + τ.colLen 0 - 1) (j : Fin (L + 1)) :
    ((completePresentation R).symm
      ((jacobiTrudiMatrix R τ (L + 1)).submatrix Fin.succ j.succAbove).det).degreeOf n = 0 := by
  apply det_degree_zero
  intro i k
  rw [Matrix.submatrix_apply, jacobiTrudiMatrix_apply]
  apply complete_degree_zero
  have hr := τ.rowLen_anti 0 (i.val + 1) (by omega)
  have hj := (j.succAbove k).isLt
  simp only [Fin.val_succ]
  omega

private theorem corner_minor (τ : YoungDiagram) (L : ℕ) (hh : τ.colLen 0 = L + 1) :
    ((jacobiTrudiMatrix R τ (L + 1)).submatrix Fin.succ (Fin.last L).succAbove).det =
      schur R τ.removeFirstRowCol := by
  have hm : (jacobiTrudiMatrix R τ (L + 1)).submatrix Fin.succ (Fin.last L).succAbove =
      jacobiTrudiMatrix R τ.removeFirstRowCol L := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply, Fin.succAbove_last, jacobiTrudiMatrix_apply,
      Fin.val_succ, Fin.val_castSucc, YoungDiagram.rowLen_removeFirstRowCol]
    have hp : 0 < τ.rowLen (i.val + 1) := by
      apply YoungDiagram.mem_iff_lt_rowLen.mp
      apply YoungDiagram.mem_iff_lt_colLen.mpr
      omega
    congr 1
    omega
  rw [hm, ← schur_eq_det_jacobiTrudiMatrix R τ.removeFirstRowCol L]
  rw [YoungDiagram.colLen_removeFirstRowCol]
  simp only [zero_add]
  have := τ.colLen_anti 0 1 (by omega)
  omega

/-- Extracting the maximal complete generator gives the signed corner-deleted Schur function. -/
theorem completeCoeff_schur (τ : YoungDiagram) (hτ : τ ≠ ⊥) (n : ℕ+)
    (hn : n.val = τ.rowLen 0 + τ.colLen 0 - 1) :
    completeCoeff R n 1 (schur R τ) =
      (-1 : R) ^ (τ.colLen 0 - 1) • schur R τ.removeFirstRowCol := by
  classical
  have hp : 0 < τ.colLen 0 := by
    have := (YoungDiagram.eq_bot_iff_colLen_zero τ).not.mp hτ
    omega
  obtain ⟨L, hh⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : τ.colLen 0 ≠ 0)
  rw [schur_eq_det_jacobiTrudiMatrix R τ (L + 1) (by omega), Matrix.det_succ_row_zero,
    map_sum]
  have ht (j : Fin (L + 1)) :
      completeCoeff R n 1
        ((-1 : SymmetricFunction R) ^ j.val * jacobiTrudiMatrix R τ (L + 1) 0 j *
          ((jacobiTrudiMatrix R τ (L + 1)).submatrix Fin.succ j.succAbove).det) =
        if j = Fin.last L then (-1 : R) ^ L • schur R τ.removeFirstRowCol else 0 := by
    have hs : (-1 : SymmetricFunction R) ^ j.val =
        algebraMap R (SymmetricFunction R) ((-1 : R) ^ j.val) := by simp
    rw [hs, mul_assoc, ← Algebra.smul_def, completeCoeff_smul,
      completeCoeff_mul_of_degreeOf_eq_zero n 1 _ _ (minor_degree_zero τ L hh n hn j)]
    by_cases hj : j = Fin.last L
    · subst j
      have he : jacobiTrudiMatrix R τ (L + 1) 0 (Fin.last L) =
          complete R (n.val : ℤ) := by
        rw [jacobiTrudiMatrix_apply]
        congr 1
        simp only [Fin.val_zero, Fin.val_last]
        omega
      rw [he, ← pow_one (complete R (n.val : ℤ)), completeCoeff_generator_pow]
      simp only [ite_true, one_mul, Fin.val_last, corner_minor τ L hh]
    · have hz : completeCoeff R n 1 (jacobiTrudiMatrix R τ (L + 1) 0 j) = 0 := by
        apply completeCoeff_pos_of_degreeOf_eq_zero n _ _ (by omega)
        rw [completeDegree_apply, jacobiTrudiMatrix_apply]
        apply complete_degree_zero
        have hlt : j.val < L := by
          have := j.isLt
          have hne : j.val ≠ L := by intro he; apply hj; exact Fin.ext he
          omega
        simp only [Fin.val_zero]
        omega
      rw [hz, zero_mul, smul_zero, ite_eq_right hj]
  simp_rw [ht]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hh]
  simp

private theorem complete_degree_le_one (n : ℕ+) (k : ℤ) (hk : k ≤ (n.val : ℤ)) :
    ((completePresentation R).symm (complete R k)).degreeOf n ≤ 1 := by
  rcases lt_or_eq_of_le hk with hlt | rfl
  · rw [complete_degree_zero n k hlt]
    omega
  · rw [completePresentation_symm_complete]
    simpa only [one_mul, MvPolynomial.degreeOf_one, zero_add] using
      MvPolynomial.degreeOf_mul_X_self n (1 : MvPolynomial ℕ+ R)

/-- A Schur function has degree at most one in its maximal complete generator over any ring. -/
theorem degreeOf_schur_le_one (τ : YoungDiagram) (hτ : τ ≠ ⊥) (n : ℕ+)
    (hn : n.val = τ.rowLen 0 + τ.colLen 0 - 1) :
    ((completePresentation R).symm (schur R τ)).degreeOf n ≤ 1 := by
  classical
  have hp : τ.colLen 0 ≠ 0 := (YoungDiagram.eq_bot_iff_colLen_zero τ).not.mp hτ
  obtain ⟨L, hh⟩ := Nat.exists_eq_succ_of_ne_zero hp
  rw [schur_eq_det_jacobiTrudiMatrix R τ (L + 1) (by omega), Matrix.det_succ_row_zero,
    map_sum]
  apply (MvPolynomial.degreeOf_sum_le n _ _).trans
  apply Finset.sup_le
  intro j _
  rw [map_mul, map_mul]
  have hs : (completePresentation R).symm ((-1 : SymmetricFunction R) ^ j.val) =
      MvPolynomial.C ((-1 : R) ^ j.val) := by
    have he : (-1 : SymmetricFunction R) ^ j.val =
        algebraMap R (SymmetricFunction R) ((-1 : R) ^ j.val) := by simp
    rw [he, AlgEquiv.commutes]
    rfl
  have he : ((completePresentation R).symm
      (jacobiTrudiMatrix R τ (L + 1) 0 j)).degreeOf n ≤ 1 := by
    rw [jacobiTrudiMatrix_apply]
    apply complete_degree_le_one
    have := j.isLt
    simp only [Fin.val_zero]
    omega
  have hm := minor_degree_zero (R := R) τ L hh n hn j
  apply (MvPolynomial.degreeOf_mul_le n _ _).trans
  rw [hm, add_zero, hs]
  exact (MvPolynomial.degreeOf_C_mul_le _ n _).trans he

/-- A nonempty Schur function has degree one in its maximal complete generator. -/
theorem degreeOf_schur [Nontrivial R] (τ : YoungDiagram) (hτ : τ ≠ ⊥) (n : ℕ+)
    (hn : n.val = τ.rowLen 0 + τ.colLen 0 - 1) :
    ((completePresentation R).symm (schur R τ)).degreeOf n = 1 := by
  have hle := degreeOf_schur_le_one (R := R) τ hτ n hn
  have hne : completeCoeff R n 1 (schur R τ) ≠ 0 := by
    rw [completeCoeff_schur τ hτ n hn]
    intro hz
    have hc : (schurBasis R).repr (schur R τ.removeFirstRowCol) τ.removeFirstRowCol = 1 := by
      rw [← schurBasis_apply, Module.Basis.repr_self]
      exact Finsupp.single_eq_same
    have he := congrArg (fun f => (schurBasis R).repr f τ.removeFirstRowCol) hz
    simp only [map_smul, Finsupp.smul_apply, hc, smul_eq_mul, mul_one, map_zero,
      Finsupp.zero_apply] at he
    exact (isUnit_neg_one.pow (τ.colLen 0 - 1)).ne_zero he
  have hp : 0 < ((completePresentation R).symm (schur R τ)).degreeOf n := by
    by_contra hz
    apply hne
    apply completeCoeff_pos_of_degreeOf_eq_zero n _ _ (by omega)
    change ((completePresentation R).symm (schur R τ)).degreeOf n = 0
    omega
  omega

/-- A Schur function omits complete generators above its maximal complete index. -/
theorem degreeOf_schur_above (τ : YoungDiagram) (m : ℕ+)
    (hm : τ.rowLen 0 + τ.colLen 0 - 1 < m.val) :
    ((completePresentation R).symm (schur R τ)).degreeOf m = 0 := by
  rw [schur_eq_det_jacobiTrudiMatrix R τ (τ.colLen 0) le_rfl]
  apply det_degree_zero
  intro i j
  rw [jacobiTrudiMatrix_apply]
  apply complete_degree_zero
  have hr := τ.rowLen_anti 0 i.val (by omega)
  have hj := j.isLt
  omega

/-- Derivatives at and above the maximal complete index have the prescribed two values. -/
theorem completeDerivation_schur (τ : YoungDiagram) (hτ : τ ≠ ⊥) (n : ℕ+)
    (hn : n.val = τ.rowLen 0 + τ.colLen 0 - 1) (k : ℤ) (hk : (n.val : ℤ) ≤ k) :
    completeDerivation R (⟨k.toNat, by have := n.pos; omega⟩ : ℕ+) (schur R τ) =
      if k = (n.val : ℤ) then
        (-1 : R) ^ (τ.colLen 0 - 1) • schur R τ.removeFirstRowCol else 0 := by
  classical
  let m : ℕ+ := ⟨k.toNat, by have := n.pos; omega⟩
  change completeDerivation R m (schur R τ) = _
  by_cases he : k = (n.val : ℤ)
  · have hmn : m = n := by
      apply Subtype.ext
      change k.toNat = n.val
      rw [he, Int.toNat_natCast]
    rw [hmn, ite_eq_left he, completeDerivation_eq_coeff_one n _
      (degreeOf_schur_le_one τ hτ n hn), completeCoeff_schur τ hτ n hn]
  · rw [ite_eq_right he, completeDerivation_apply]
    have hd := degreeOf_schur_above (R := R) τ m (by dsimp [m]; omega)
    rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars, map_zero]
    simpa only [MvPolynomial.mem_vars_iff_degreeOf_ne_zero, not_not] using hd

end SymmetricFunction
