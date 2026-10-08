import Schubert.SetPartitions.WeightedSums
import Schubert.SetPartitions.Moebius
import Schubert.SymmetricFunctions.Monomial.Weights

/-!
# Integer incidence expansion of labelled monomial weights

Weighted kernel decomposition and Möbius inversion express injective assignments as
integer linear combinations of products of power sums of block weights.

## Main results

* `Finpartition.sum_embeddings_eq_sum_mu_powerSums` gives the finite integer expansion.
-/

noncomputable section

namespace Finpartition

/-- Möbius inversion expands labelled injective monomials into block power sums over integers. -/
theorem sum_embeddings_eq_sum_mu_powerSums {k : ℕ} {σ : Type*} [Fintype σ]
    (a : Fin k → ℕ) :
    (∑ f : Fin k ↪ σ, ∏ i, MvPolynomial.X (f i) ^ a i : MvPolynomial σ ℤ) =
      ∑ P : Finpartition (Finset.univ : Finset (Fin k)),
        IncidenceAlgebra.mu ℤ ⊥ P •
          ∏ B ∈ P.parts, MvPolynomial.psum σ ℤ (∑ i ∈ B, a i) := by
  classical
  let X (P : Finpartition (Finset.univ : Finset (Fin k))) : MvPolynomial σ ℤ :=
    ∑ f : {f : Fin k → σ // kernelPartition f = P},
      ∏ i, MvPolynomial.X (f.val i) ^ a i
  let Y (P : Finpartition (Finset.univ : Finset (Fin k))) : MvPolynomial σ ℤ :=
    ∏ B ∈ P.parts, MvPolynomial.psum σ ℤ (∑ i ∈ B, a i)
  have hY (P : Finpartition (Finset.univ : Finset (Fin k))) :
      Y P = ∑ f : {f : Fin k → σ // P ≤ kernelPartition f},
        ∏ i, MvPolynomial.X (f.val i) ^ a i := by
    have he := sum_blockConstant_prod P (fun (i : Fin k) (x : σ) =>
      (MvPolynomial.X x : MvPolynomial σ ℤ) ^ a i)
    simpa only [Y, MvPolynomial.psum, Finset.prod_pow_eq_pow_sum] using he.symm
  have hXY (P : Finpartition (Finset.univ : Finset (Fin k))) :
      Y P = ∑ Q ∈ Finset.Ici P, X Q := by
    rw [hY]
    have he := sum_blockConstant_eq_kernels P (fun f : Fin k → σ =>
      ∏ i, (MvPolynomial.X (f i) : MvPolynomial σ ℤ) ^ a i)
    exact he.trans (Finset.sum_subtype (Finset.Ici P) (fun Q => Finset.mem_Ici) X).symm
  have hb : X ⊥ = ∑ f : Fin k ↪ σ, ∏ i, MvPolynomial.X (f i) ^ a i := by
    exact Fintype.sum_equiv discreteKernelEquiv _ _ (fun _ => rfl)
  rw [← hb]
  apply MvPolynomial.ext
  intro d
  have hi := IncidenceAlgebra.moebius_inversion_top
    (fun P => (X P).coeff d) (fun P => (Y P).coeff d)
    (fun P => by rw [hXY, MvPolynomial.coeff_sum]) ⊥
  have hu : Finset.Ici (⊥ : Finpartition (Finset.univ : Finset (Fin k))) = Finset.univ := by
    ext P
    simp
  rw [hu] at hi
  simpa only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul, Y] using hi

/-- Changing coefficient rings preserves the integer Möbius expansion of labelled weights. -/
theorem sum_embeddings_mu_powerSums (R : Type*) [CommRing R] {k : ℕ} {σ : Type*}
    [Fintype σ] (a : Fin k → ℕ) :
    (∑ f : Fin k ↪ σ, ∏ i, MvPolynomial.X (f i) ^ a i : MvPolynomial σ R) =
      ∑ P : Finpartition (Finset.univ : Finset (Fin k)),
        IncidenceAlgebra.mu ℤ ⊥ P •
          ∏ B ∈ P.parts, MvPolynomial.psum σ R (∑ i ∈ B, a i) := by
  have he := congrArg (MvPolynomial.map (Int.castRingHom R))
    (sum_embeddings_eq_sum_mu_powerSums (σ := σ) a)
  simpa only [map_sum, map_prod, map_pow, MvPolynomial.map_X, map_zsmul,
    MvPolynomial.psum] using he

end Finpartition
