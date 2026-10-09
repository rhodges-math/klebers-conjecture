import KlebersConjecture.SymmetricFunctions.ForMathlib.InterpolationComplete
import KlebersConjecture.SymmetricFunctions.ForMathlib.InterpolationDeterminant
import KlebersConjecture.SymmetricFunctions.ForMathlib.AlternantRegularity
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Finite Jacobi--Trudi identity

Interpolation proves the determinant identity in the fraction field of integral polynomials.
Injectivity and regularity descend the identity to integral coefficients, and coefficient maps
give the formula over every commutative ring.

## Main results

* `SymmetricFunction.FiniteAlphabet.diagramSchurPoly_eq_det_hsymm` gives the finite
  Jacobi--Trudi identity.
-/

noncomputable section

namespace SymmetricFunction.FiniteAlphabet

open TauCeti

private theorem map_hsymm_eval {F : Type*} [Field F] {N : ℕ}
    (φ : MvPolynomial (Fin N) ℤ →+* F) (k : ℕ) :
    φ (MvPolynomial.hsymm (Fin N) ℤ k) =
      MvPolynomial.eval (φ ∘ MvPolynomial.X) (MvPolynomial.hsymm (Fin N) F k) := by
  rw [← MvPolynomial.eval₂Hom_X (Int.castRingHom F) φ,
    MvPolynomial.eval₂_eq_eval_map, MvPolynomial.map_hsymm]

private theorem map_complete_entry {F : Type*} [Field F] {N : ℕ}
    (φ : MvPolynomial (Fin N) ℤ →+* F)
    (hx : Function.Injective (φ ∘ MvPolynomial.X)) (μ : YoungDiagram) (i j : Fin N) :
    φ (if 0 ≤ (μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ) then
        MvPolynomial.hsymm (Fin N) ℤ
          (((μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ)).toNat) else 0) =
      ∑ a : Fin N, (φ (MvPolynomial.X a)) ^ (μ.betaNumber N i.val + j.val) /
        ∏ b ∈ Finset.univ.erase a, (φ (MvPolynomial.X a) - φ (MvPolynomial.X b)) := by
  have hN : 0 < N := by have := i.isLt; omega
  by_cases hm : 0 ≤ (μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ)
  · rw [ite_eq_left hm, map_hsymm_eval, Lagrange.eval_hsymm_eq_moment hN _ hx]
    have he : (((μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ)).toNat) + N - 1 =
        μ.betaNumber N i.val + j.val := by
      have := Int.toNat_of_nonneg hm
      have := i.isLt
      rw [YoungDiagram.betaNumber_def]
      omega
    simp only [he, Function.comp_apply]
  · rw [ite_eq_right hm, map_zero]
    have ht : μ.betaNumber N i.val + j.val < N := by
      rw [YoungDiagram.betaNumber_def]
      have := i.isLt
      omega
    have he : μ.betaNumber N i.val + j.val ≠ N - 1 := by
      rw [YoungDiagram.betaNumber_def]
      have := i.isLt
      omega
    have h := Lagrange.sum_pow_div_prod_sub Finset.univ (φ ∘ MvPolynomial.X)
      hx.injOn _ (by simpa using ht)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    rw [ite_eq_right he] at h
    exact h.symm

private theorem map_alternant_transpose {F : Type*} [CommRing F] {N : ℕ}
    (φ : MvPolynomial (Fin N) ℤ →+* F) (β : Fin N → ℕ) :
    φ (alternant (Fin N) ℤ β) =
      Matrix.det (Matrix.of fun i a : Fin N => φ (MvPolynomial.X a) ^ β i) := by
  rw [alternant_def, RingHom.map_det]
  rw [← Matrix.det_transpose]
  congr 1
  apply Matrix.ext
  intro i j
  simp

private theorem integral_det_complete (N : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ N) :
    diagramSchurPoly N ℤ μ =
      Matrix.det (Matrix.of fun i j : Fin N =>
        if 0 ≤ (μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ) then
          MvPolynomial.hsymm (Fin N) ℤ
            (((μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ)).toNat) else 0) := by
  let P := MvPolynomial (Fin N) ℤ
  let K := FractionRing P
  let φ : P →+* K := algebraMap P K
  have hφ : Function.Injective φ := IsFractionRing.injective P K
  have hx : Function.Injective (φ ∘ MvPolynomial.X) := hφ.comp MvPolynomial.X_injective
  have hd := Lagrange.det_pow_moments_mul (φ ∘ MvPolynomial.X) hx
    (fun i : Fin N => μ.betaNumber N i.val)
  apply (isRegular_alternant_staircase ℤ N).right
  dsimp only
  rw [diagramSchurPoly_mul_alternant N μ hμ]
  apply hφ
  rw [map_mul, RingHom.map_det]
  rw [map_alternant_transpose, map_alternant_transpose]
  have he : (Matrix.of fun i j : Fin N =>
      if 0 ≤ (μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ) then
        MvPolynomial.hsymm (Fin N) ℤ
          (((μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ)).toNat) else 0).map φ =
        Matrix.of fun i j : Fin N => ∑ a : Fin N,
          φ (MvPolynomial.X a) ^ (μ.betaNumber N i.val + j.val) /
            ∏ b ∈ Finset.univ.erase a, (φ (MvPolynomial.X a) - φ (MvPolynomial.X b)) := by
    apply Matrix.ext
    intro i j
    exact map_complete_entry φ hx μ i j
  rw [RingHom.mapMatrix_apply, he]
  exact hd.symm

/-- The finite Schur polynomial is the determinant of signed complete symmetric entries. -/
theorem diagramSchurPoly_eq_det_hsymm (R : Type*) [CommRing R] (N : ℕ)
    (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ N) :
    diagramSchurPoly N R μ =
      Matrix.det (Matrix.of fun i j : Fin N =>
        if 0 ≤ (μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ) then
          MvPolynomial.hsymm (Fin N) R
            (((μ.rowLen i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ)).toNat) else 0) := by
  have h := congrArg (MvPolynomial.map (Int.castRingHom R)) (integral_det_complete N μ hμ)
  rw [map_diagramSchurPoly, RingHom.map_det] at h
  convert h using 1
  congr 1
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp only [MvPolynomial.map_hsymm, map_zero]

end SymmetricFunction.FiniteAlphabet
