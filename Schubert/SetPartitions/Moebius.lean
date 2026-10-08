import Schubert.SetPartitions.Blocks
import Schubert.SetPartitions.Counting
import Schubert.SetPartitions.ForMathlib.Pochhammer
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Roots

/-!
# Möbius coefficients of finite set partitions

Counting maps by their kernels gives a descending-factorial identity. Möbius inversion and
comparison of polynomial coefficients determine the value between the discrete and indiscrete
partitions.

## Main definitions

The upstream `IncidenceAlgebra.mu` supplies the Möbius function.
This module identifies its discrete-to-indiscrete value with the integer
formula `(-1) ^ (k - 1) * (k - 1)!`; no alternative Möbius function is introduced.

## Main results

* `Finpartition.descPochhammer_eq_sum_mu`: the partition-lattice polynomial identity.
* `Finpartition.coeff_one_descPochhammer_eq_mu`: the linear coefficient is the top Möbius value.
* `Finpartition.mu_bot_top`: the signed-factorial value on a nonempty finite set.

## Implementation notes

Partitions are ordered by refinement: finer partitions lie below coarser partitions.
The general finite-type formula is specialized to `Fin k` without changing the indexed
corollary. The empty-set value is one; the signed-factorial formula requires positive size.
## References

* R. P. Stanley, *Enumerative Combinatorics*, Volume 1, Example 3.10.4.
-/

namespace Finpartition

open scoped Classical
open IncidenceAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integer count of constant maps is the sum of exact-kernel counts over coarsenings. -/
theorem pow_eq_sum_descFactorial_int
    (P : Finpartition (Finset.univ : Finset (ι))) (x : ℕ) :
    (x : ℤ) ^ P.parts.card =
      ∑ Q ∈ Finset.Ici P, (x.descFactorial Q.parts.card : ℤ) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (pow_eq_sum_descFactorial P x)
  simp only [Nat.cast_pow, Nat.cast_sum] at h
  rw [← Finset.sum_subtype (Finset.Ici P) (fun Q => Finset.mem_Ici)
    (fun Q => (x.descFactorial Q.parts.card : ℤ))] at h
  exact h

/-- Inverting the coarsening count expresses a descending factorial by Möbius-weighted powers. -/
theorem descFactorial_eq_sum_mu_pow (ι : Type*) [Fintype ι] [DecidableEq ι] (x : ℕ) :
    (x.descFactorial (Fintype.card ι) : ℤ) =
      ∑ P ∈ Finset.Ici (⊥ : Finpartition (Finset.univ : Finset (ι))),
        mu ℤ ⊥ P * (x : ℤ) ^ P.parts.card := by
  simpa only [card_parts_bot_univ] using
    moebius_inversion_top
      (fun P : Finpartition (Finset.univ : Finset (ι)) =>
        (x.descFactorial P.parts.card : ℤ))
      (fun P => (x : ℤ) ^ P.parts.card)
      (fun P => pow_eq_sum_descFactorial_int P x) ⊥

/-- The descending Pochhammer polynomial is the Möbius-weighted block-count polynomial. -/
theorem descPochhammer_eq_sum_mu (ι : Type*) [Fintype ι] [DecidableEq ι] :
    descPochhammer ℤ (Fintype.card ι) =
      ∑ P ∈ Finset.Ici (⊥ : Finpartition (Finset.univ : Finset (ι))),
        Polynomial.C (mu ℤ ⊥ P) * Polynomial.X ^ P.parts.card := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hInf : Set.Infinite (Set.range fun x : ℕ => (x : ℤ)) :=
    Set.infinite_range_of_injective Nat.cast_injective
  apply hInf.mono
  rintro z ⟨x, rfl⟩
  change (descPochhammer ℤ (Fintype.card ι)).eval (x : ℤ) = _
  rw [descPochhammer_eval_eq_descFactorial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  exact descFactorial_eq_sum_mu_pow ι x

/-- For a nonempty set, the linear coefficient selects the unique one-block partition. -/
theorem coeff_one_descPochhammer_eq_mu (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hk : 0 < Fintype.card ι) :
    (descPochhammer ℤ (Fintype.card ι)).coeff 1 =
      mu ℤ (⊥ : Finpartition (Finset.univ : Finset (ι))) ⊤ := by
  have h := congrArg (fun p : Polynomial ℤ => p.coeff 1) (descPochhammer_eq_sum_mu ι)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at h
  rw [Finset.sum_eq_single ⊤] at h
  · simpa only [card_parts_top_univ hk, ite_true] using h
  · intro P _ hP
    have hn : ¬ 1 = P.parts.card := fun he =>
      hP ((card_parts_eq_one_iff hk P).mp he.symm)
    simp only [hn, ite_false]
  · intro htop
    exact (htop (Finset.mem_Ici.mpr bot_le)).elim

/-- The discrete-to-indiscrete Möbius value for a nonempty set is a signed factorial. -/
theorem mu_bot_top_fintype (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hk : 0 < Fintype.card ι) :
    mu ℤ (⊥ : Finpartition (Finset.univ : Finset (ι))) ⊤ =
      (-1 : ℤ) ^ (Fintype.card ι - 1) * ((Fintype.card ι - 1).factorial : ℤ) := by
  rw [← coeff_one_descPochhammer_eq_mu ι hk]
  exact Polynomial.coeff_one_descPochhammer ℤ (Fintype.card ι) hk

/-- The signed-factorial formula on the standard finite set of size k. -/
theorem mu_bot_top (k : ℕ) (hk : 0 < k) :
    mu ℤ (⊥ : Finpartition (Finset.univ : Finset (Fin k))) ⊤ =
      (-1 : ℤ) ^ (k - 1) * ((k - 1).factorial : ℤ) := by
  simpa only [Fintype.card_fin] using
    mu_bot_top_fintype (Fin k) (by simpa only [Fintype.card_fin] using hk)

/-- The discrete-to-indiscrete Möbius value on any empty index type is one. -/
@[simp] theorem mu_bot_top_of_isEmpty [IsEmpty ι] :
    mu ℤ (⊥ : Finpartition (Finset.univ : Finset ι)) ⊤ = 1 := by
  rw [eq_bot_univ_of_isEmpty (⊤ : Finpartition (Finset.univ : Finset ι))]
  exact mu_self ⊥

/-- On the empty set the discrete-to-indiscrete Möbius value is one. -/
@[simp high] theorem mu_bot_top_zero :
    mu ℤ (⊥ : Finpartition (Finset.univ : Finset (Fin 0))) ⊤ = 1 :=
  mu_bot_top_of_isEmpty

end Finpartition
