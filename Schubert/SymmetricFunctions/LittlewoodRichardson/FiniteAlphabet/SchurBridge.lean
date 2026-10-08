import Schubert.SymmetricFunctions.LittlewoodRichardson.FiniteAlphabet.Alternant
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric
import Schubert.SymmetricFunctions.Families.Schur

/-! # Finite Schur polynomials and Laurent alternants

The Laurent embedding preserves permutation symmetry and the finite Schur bialternant identity.

## Main results

* `isSymmetric_toLaurent`: symmetric polynomials give symmetric Laurent polynomials.
* `alternant_mul_schur`: the staircase alternant times Schur is the shifted alternant.
* `rename_restrict_schur`: the inverse-renamed stable restriction is the diagram polynomial.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction.FiniteAlphabet.Alternants

open Equiv

variable {d : ℕ}

/-- A polynomial variable embeds as its unit Laurent exponent. -/
theorem toLaurent_X (i : Fin d) :
    toLaurent (MvPolynomial.X i : IntPolynomial d) = AddMonoidAlgebra.single (Pi.single i 1) 1 := by
  rw [MvPolynomial.X, toLaurent_monomial]
  congr 1
  funext k
  simp only [exponentWeight, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finsupp.single_apply,
    Pi.single_apply, eq_comm]
  split_ifs <;> rfl

/-- The Laurent embedding commutes with permutation of variables. -/
theorem permute_toLaurent (σ : Perm (Fin d)) (p : IntPolynomial d) :
    permute σ (toLaurent p) = toLaurent (MvPolynomial.rename σ p) := by
  have h : (permute σ : IntLaurent d →+* IntLaurent d).comp toLaurent =
      toLaurent.comp (MvPolynomial.rename σ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro z
      show permute σ (toLaurent (MvPolynomial.C z)) =
        toLaurent (MvPolynomial.rename σ (MvPolynomial.C z))
      rw [MvPolynomial.rename_C, MvPolynomial.C_apply, toLaurent_monomial, permute_single,
        map_zero]
      rfl
    · intro i
      simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.toRingHom_eq_coe,
        MvPolynomial.rename_X, toLaurent_X, permute_single]
      congr 1
      funext k
      simp only [Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq]
  exact congrArg (fun φ : IntPolynomial d →+* IntLaurent d => φ p) h

/-- The Laurent embedding preserves permutation symmetry. -/
theorem isSymmetric_toLaurent {p : IntPolynomial d} (hp : p.IsSymmetric) :
    IsSymmetric (toLaurent p) := fun σ => by rw [permute_toLaurent, hp σ]

/-- **Jacobi's bialternant formula** in `IntLaurent d`: `a_δ s_ν = a_{ν + δ}` for a Young diagram
with at most `d` rows. -/
theorem alternant_mul_schur (ν : YoungDiagram) (hν : ν.colLen 0 ≤ d) :
    alternant (staircase d) * toLaurent (TauCeti.diagramSchurPoly d ℤ ν) =
      alternant (fun i => (ν.rowLen i : ℤ) + staircase d i) := by
  have h := congrArg toLaurent (TauCeti.diagramSchurPoly_mul_alternant (R := ℤ) d ν hν)
  rw [map_mul, toLaurent_alternant, toLaurent_alternant, mul_comm] at h
  have hst : (fun i : Fin d => ((d - 1 - (i : ℕ) : ℕ) : ℤ)) = staircase d := by
    funext i
    simp only [staircase]
    have := i.isLt
    omega
  have hbeta : (fun i : Fin d => ((ν.betaNumber d i : ℕ) : ℤ)) =
      fun i : Fin d => (ν.rowLen i : ℤ) + staircase d i := by
    funext i
    simp only [YoungDiagram.betaNumber_def, staircase]
    have := i.isLt
    omega

  rw [hst, hbeta] at h
  exact h

end SymmetricFunction.FiniteAlphabet.Alternants

end

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommSemiring R]

/-- Inverse renaming of restriction recovers the finite diagram Schur polynomial. -/
theorem rename_restrict_schur (n : ℕ) (μ : YoungDiagram) :
    MvPolynomial.rename (Fintype.equivFin (Fin n)) (restrict R n (schur R μ)) =
      TauCeti.diagramSchurPoly (Fintype.card (Fin n)) R μ := by
  rw [restrict_schur, TauCeti.schurPoly_eq_rename, TauCeti.diagramOf_shapePartition,
    MvPolynomial.rename_rename]
  simp

end SymmetricFunction
