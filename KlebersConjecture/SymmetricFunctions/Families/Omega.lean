import KlebersConjecture.SymmetricFunctions.Presentations.CompletePresentation
import KlebersConjecture.SymmetricFunctions.Families.Products
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Commute

/-!
# The elementary--complete involution

Evaluation in elementary functions through complete coordinates gives the standard omega
involution. The signed convolution proves its inverse integrally over any commutative ring.

## Main results

* `omega_complete_nat` and `omega_elementary`: omega exchanges the standard generators.
* `omega_involutive`: omega is an involution.
* `omega_completeProd` and `omega_elementaryProd`: omega exchanges row products.
-/

noncomputable section

namespace SymmetricFunction

variable (R : Type*) [CommRing R]

/-- Elementary evaluation in complete-generator coordinates. -/
private def omegaHom : SymmetricFunction R →ₐ[R] SymmetricFunction R :=
  (MvPolynomial.aeval (fun n : ℕ+ => elementary R n.val)).comp
    (completePresentation R).symm.toAlgHom

private theorem omegaHom_complete (n : ℕ) :
    omegaHom R (complete R (n : ℤ)) = elementary R n := by
  by_cases hn : 0 < n
  · change MvPolynomial.aeval (fun k : ℕ+ => elementary R k.val)
      ((completePresentation R).symm (complete R (n : ℤ))) = _
    have he : (completePresentation R).symm (complete R (n : ℤ)) =
        MvPolynomial.X (⟨n, hn⟩ : ℕ+) := completePresentation_symm_complete R ⟨n, hn⟩
    exact (congrArg (MvPolynomial.aeval (fun k : ℕ+ => elementary R k.val)) he).trans
      (MvPolynomial.aeval_X (fun k : ℕ+ => elementary R k.val) (⟨n, hn⟩ : ℕ+))
  · have hz : n = 0 := by omega
    subst n
    change omegaHom R (complete R 0) = elementary R 0
    rw [complete_zero, elementary_zero, map_one]

private theorem reflected_sign (n i : ℕ) (hi : i ≤ n) :
    (-1 : R) ^ n * (-1 : R) ^ i = (-1 : R) ^ (n - i) := by
  have he : n = n - i + i := by omega
  calc
    _ = (-1 : R) ^ (n - i) * ((-1 : R) ^ i * (-1 : R) ^ i) := by
      conv_lhs => rw [he, pow_add]
      ring
    _ = _ := by
      rw [← pow_add, Even.neg_one_pow (show Even (i + i) from ⟨i, rfl⟩), mul_one]

private theorem swapped_convolution (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range (n + 1), (-1 : R) ^ i •
      (complete R (i : ℤ) * elementary R (n - i))) = 0 := by
  have h := congrArg (fun f : SymmetricFunction R => (-1 : R) ^ n • f)
    (sum_signed_elementary_complete R n hn)
  rw [smul_zero, Finset.smul_sum] at h
  rw [← Finset.sum_range_reflect
    (fun i => (-1 : R) ^ i • (complete R (i : ℤ) * elementary R (n - i))) (n + 1)]
  simp only [Nat.add_sub_cancel]
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
  rw [smul_smul, reflected_sign R n i hin, Nat.sub_sub_self hin, mul_comm]

private theorem omegaHom_elementary (n : ℕ) :
    omegaHom R (elementary R n) = complete R (n : ℤ) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : 0 < n
    · have hf := congrArg (omegaHom R) (sum_signed_elementary_complete R n hn)
      simp only [map_sum, map_smul, map_mul, map_zero, omegaHom_complete] at hf
      have hs : (-1 : R) ^ n •
          (omegaHom R (elementary R n) - complete R (n : ℤ)) = 0 := by
        calc
          _ = ∑ i ∈ Finset.range (n + 1), (-1 : R) ^ i •
              (omegaHom R (elementary R i) * elementary R (n - i) -
                complete R (i : ℤ) * elementary R (n - i)) := by
            symm
            rw [Finset.sum_eq_single n]
            · rw [Nat.sub_self, elementary_zero, mul_one, mul_one]
            · intro i hi hin
              have hlt : i < n := by have := Finset.mem_range.mp hi; omega
              rw [ih i hlt, sub_self, smul_zero]
            · intro hnot
              exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_self n)))
          _ = (∑ i ∈ Finset.range (n + 1), (-1 : R) ^ i •
              (omegaHom R (elementary R i) * elementary R (n - i))) -
              ∑ i ∈ Finset.range (n + 1), (-1 : R) ^ i •
                (complete R (i : ℤ) * elementary R (n - i)) := by
            simp only [Finset.sum_sub_distrib, smul_sub]
          _ = 0 := by rw [hf, swapped_convolution R n hn, sub_self]
      apply sub_eq_zero.mp
      apply (neg_one_pow_mul_eq_zero_iff (n := n)).mp
      simpa only [Algebra.smul_def, map_pow, map_neg, map_one] using hs
    · have hz : n = 0 := by omega
      subst n
      change omegaHom R (elementary R 0) = complete R 0
      rw [elementary_zero, complete_zero, map_one]

private theorem omegaHom_comp : (omegaHom R).comp (omegaHom R) = AlgHom.id R _ := by
  have h : ((omegaHom R).comp (omegaHom R)).comp (completePresentation R).toAlgHom =
      (completePresentation R).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro n
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, completePresentation_apply_X,
      omegaHom_complete, omegaHom_elementary]
  apply DFunLike.ext
  intro f
  obtain ⟨p, rfl⟩ := (completePresentation R).surjective f
  exact AlgHom.congr_fun h p

/-- The standard algebra involution exchanging complete and elementary symmetric functions. -/
def omega : SymmetricFunction R ≃ₐ[R] SymmetricFunction R :=
  AlgEquiv.ofAlgHom (omegaHom R) (omegaHom R) (omegaHom_comp R) (omegaHom_comp R)

/-- Omega sends every nonnegative complete function to its elementary function. -/
@[simp↓]
theorem omega_complete_nat (n : ℕ) : omega R (complete R (n : ℤ)) = elementary R n :=
  omegaHom_complete R n

/-- Omega sends every elementary function to its complete function. -/
@[simp]
theorem omega_elementary (n : ℕ) : omega R (elementary R n) = complete R (n : ℤ) :=
  omegaHom_elementary R n

/-- A negative complete function remains zero under omega. -/
theorem omega_complete_neg {n : ℤ} (hn : n < 0) : omega R (complete R n) = 0 := by
  rw [complete_neg n hn, map_zero]

/-- The inverse of omega is omega itself. -/
theorem omega_symm : (omega R).symm = omega R := rfl

/-- Applying omega twice fixes every symmetric function. -/
theorem omega_involutive : Function.Involutive (omega R) := by
  intro f
  exact (omega R).symm_apply_apply f

/-- Omega exchanges complete row products with elementary row products. -/
@[simp]
theorem omega_completeProd (μ : YoungDiagram) :
    omega R (completeProd R μ) = elementaryProd R μ := by
  simp only [completeProd, elementaryProd, map_list_prod, List.map_map, Function.comp_def,
    omega_complete_nat]

/-- Omega exchanges elementary row products with complete row products. -/
@[simp]
theorem omega_elementaryProd (μ : YoungDiagram) :
    omega R (elementaryProd R μ) = completeProd R μ := by
  simp only [completeProd, elementaryProd, map_list_prod, List.map_map, Function.comp_def,
    omega_elementary]

end SymmetricFunction
