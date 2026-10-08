import Schubert.SymmetricFunctions.Families.Families
import Schubert.SymmetricFunctions.Transfer
import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Inverse identities for elementary and complete functions

The elementary and complete generating series are multiplicative inverses after alternating
the elementary signs.

## Main results

* `sum_signed_elementary_complete` is the generating-series inverse identity.
* `complete_nat_eq_signed_elementary` isolates a complete generator.
-/

noncomputable section

namespace SymmetricFunction

open Finset

variable {R σ : Type*} [CommRing R]

private theorem coeff_prod_one_sub (s : Finset σ) (d : σ →₀ ℕ)
    (H : MvPowerSeries σ R) (hH : ∀ e, MvPowerSeries.coeff e H = 1) :
    MvPowerSeries.coeff d ((∏ i ∈ s, (1 - MvPowerSeries.X i)) * H) =
      if ∀ i ∈ s, d i = 0 then 1 else 0 := by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty => simp [hH]
  | @insert a s ha ih =>
    rw [prod_insert ha, mul_assoc, sub_mul, one_mul, map_sub, ih]
    rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul, one_mul]
    have hle : Finsupp.single a 1 ≤ d ↔ 0 < d a := by
      rw [Finsupp.single_le_iff]
      omega
    have hother : (∀ i ∈ s, (d - (Finsupp.single a 1 : σ →₀ ℕ)) i = 0) ↔
        ∀ i ∈ s, d i = 0 := by
      apply forall_congr'
      intro i
      apply forall_congr'
      intro hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      simp [Finsupp.single_eq_of_ne hia]
    simp only [hle, ih, hother]
    by_cases hs : ∀ i ∈ s, d i = 0 <;> by_cases hd : 0 < d a
    · simp [hd, hd.ne']
    · have hz : d a = 0 := by omega
      simp [hz]
    · simp [hs, hd]
    · simp [hs, hd]

private theorem prod_one_sub_mul [Fintype σ] (H : MvPowerSeries σ R)
    (hH : ∀ d, MvPowerSeries.coeff d H = 1) :
    (∏ i : σ, (1 - MvPowerSeries.X i)) * H = 1 := by
  classical
  apply MvPowerSeries.ext
  intro d
  rw [coeff_prod_one_sub Finset.univ d H hH, MvPowerSeries.coeff_one]
  have h : (∀ i ∈ (Finset.univ : Finset σ), d i = 0) ↔ d = 0 := by
    constructor
    · intro hd
      exact Finsupp.ext fun i => hd i (Finset.mem_univ i)
    · rintro rfl
      simp
  simp only [h]

private theorem signed_esymm_sum [Fintype σ] :
    (∏ i : σ, (1 - MvPolynomial.X i : MvPolynomial σ R)) =
      ∑ k ∈ Finset.range (Fintype.card σ + 1),
        MvPolynomial.C ((-1 : R) ^ k) * MvPolynomial.esymm σ R k := by
  classical
  simp_rw [sub_eq_add_neg, add_comm (1 : MvPolynomial σ R)]
  rw [Finset.prod_add]
  simp only [Finset.prod_const_one, mul_one, Finset.prod_neg]
  rw [Finset.sum_powerset]
  apply Finset.sum_congr (by simp)
  intro k _
  rw [MvPolynomial.esymm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [(Finset.mem_powersetCard.mp hs).2]
  simp

private theorem coeff_signed_prod [Fintype σ] (d : σ →₀ ℕ)
    (hd : d.degree ≤ Fintype.card σ) :
    (∏ i : σ, (1 - MvPolynomial.X i : MvPolynomial σ R)).coeff d =
      (-1 : R) ^ d.degree * (MvPolynomial.esymm σ R d.degree).coeff d := by
  classical
  rw [signed_esymm_sum, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_C_mul]
  apply Finset.sum_eq_single d.degree
  · intro k _ hk
    rw [(MvPolynomial.isHomogeneous_esymm (R := R) k).coeff_eq_zero hk.symm, mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

private theorem finite_convolution (N n : ℕ) (hn : n ≤ N) (hnpos : 0 < n) :
    (∑ i ∈ Finset.range (n + 1), (-1 : R) ^ i •
      (MvPolynomial.esymm (Fin N) R i * MvPolynomial.hsymm (Fin N) R (n - i))) = 0 := by
  classical
  let E : MvPolynomial (Fin N) R := ∏ i : Fin N, (1 - MvPolynomial.X i)
  let H : MvPowerSeries (Fin N) R := fun _ => 1
  have hH (d : Fin N →₀ ℕ) : MvPowerSeries.coeff d H = 1 := rfl
  have hInv : (E : MvPowerSeries (Fin N) R) * H = 1 := by
    have h := prod_one_sub_mul H hH
    change MvPolynomial.coeToMvPowerSeries.ringHom E * H = 1
    simpa only [E, map_prod, map_sub, map_one,
      MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X] using h
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_sum, AddMonoidAlgebra.coeff_zero]
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_mul]
  simp_rw [MvPolynomial.coeff_hsymm]
  by_cases hd : d.degree = n
  · have hdz : d ≠ 0 := by
      intro h
      simp only [h, map_zero] at hd
      omega
    have hcoef := congrArg (MvPowerSeries.coeff d) hInv
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_one, ite_eq_right hdz] at hcoef
    simp only [hH, mul_one, MvPolynomial.coeff_coe] at hcoef
    change _ = 0
    apply Eq.trans ?_ hcoef
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    have hdeg : p.1.degree + p.2.degree = n := by
      simpa only [map_add, hd] using
        congrArg Finsupp.degree (Finset.mem_antidiagonal.mp hp)
    rw [show E.coeff p.1 = (-1 : R) ^ p.1.degree *
        (MvPolynomial.esymm (Fin N) R p.1.degree).coeff p.1 from
      coeff_signed_prod p.1 (by simp only [Fintype.card_fin]; omega)]
    rw [Finset.sum_eq_single p.1.degree]
    · have hsub : p.2.degree = n - p.1.degree := by omega
      simp only [hsub, ite_true, mul_one]
    · intro i _ hi
      rw [(MvPolynomial.isHomogeneous_esymm (R := R) i).coeff_eq_zero hi.symm]
      simp
    · intro hi
      exact (hi (Finset.mem_range.mpr (by omega))).elim
  · apply Finset.sum_eq_zero
    intro i hi
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro p hp
    have hdeg : p.1.degree + p.2.degree = d.degree := by
      simpa only [map_add] using congrArg Finsupp.degree (Finset.mem_antidiagonal.mp hp)
    by_cases he : p.2.degree = n - i
    · have hne : p.1.degree ≠ i := by
        have := Finset.mem_range.mp hi
        omega
      rw [(MvPolynomial.isHomogeneous_esymm (R := R) i).coeff_eq_zero hne, zero_mul]
    · simp only [he, ite_false, mul_zero]

/-- The positive-degree coefficient of the inverse elementary and complete generating series
vanishes. -/
theorem sum_signed_elementary_complete (R : Type*) [CommRing R] (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range (n + 1), (-1 : R) ^ i •
      (elementary R i * complete R ((n - i : ℕ) : ℤ))) = 0 := by
  classical
  refine restrict_inj_of_degreeBound (R := R) (n := n) ?_
    ((degreeFiltration R n).zero_mem) ?_
  · apply IsHomogeneous.mem_degreeFiltration
    apply IsHomogeneous.sum
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hdeg : i + (n - i) = n := Nat.add_sub_of_le hi'
    have hhom : IsHomogeneous (((-1 : R) ^ i) •
        (elementary R i * complete R ((n - i : ℕ) : ℤ))) (i + (n - i)) :=
      IsHomogeneous.smul
        (IsHomogeneous.mul (isHomogeneous_elementary (R := R) i)
          (isHomogeneous_complete_nat (R := R) (n - i))) ((-1 : R) ^ i)
    rw [isHomogeneous_iff_component] at hhom ⊢
    simpa only [hdeg] using hhom
  · rw [map_sum, map_zero]
    simp_rw [map_smul, map_mul, restrict_elementary, restrict_complete_nat]
    exact finite_convolution n n le_rfl hn

/-- A positive complete function is its signed elementary term plus products in lower degrees. -/
theorem complete_nat_eq_signed_elementary (R : Type*) [CommRing R]
    (n : ℕ) (hn : 0 < n) :
    complete R (n : ℤ) = (-1 : R) ^ (n + 1) • elementary R n -
      ∑ i ∈ Finset.Ico 1 n, (-1 : R) ^ i •
        (elementary R i * complete R ((n - i : ℕ) : ℤ)) := by
  classical
  have h := sum_signed_elementary_complete R n hn
  rw [Finset.sum_range_succ] at h
  have hs : Finset.range n = insert 0 (Finset.Ico 1 n) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [hs, Finset.sum_insert (by simp)] at h
  simp only [pow_zero, one_smul, elementary_zero, one_mul, Nat.sub_zero,
    Nat.sub_self, Nat.cast_zero, complete_zero, mul_one] at h
  have hsign : (-1 : R) ^ (n + 1) • elementary R n =
      -((-1 : R) ^ n • elementary R n) := by
    rw [pow_succ, mul_smul, neg_one_smul, smul_neg]
  rw [eq_sub_iff_add_eq, hsign]
  exact eq_neg_of_add_eq_zero_left h

end SymmetricFunction





