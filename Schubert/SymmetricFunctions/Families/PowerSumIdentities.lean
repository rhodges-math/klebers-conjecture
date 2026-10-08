import Schubert.SymmetricFunctions.Families.Families
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# Stable Newton identities

Restriction to every finite alphabet lifts the polynomial Newton identity to symmetric functions.

## Main results

* `powerSum_newton`: a positive power sum is a signed multiple of the elementary function
  plus products with smaller positive indices.
* `powerSum_one_sq`: the identity `p_1^2 = p_2 + 2 e_2`.
-/

noncomputable section

namespace SymmetricFunction

variable (R : Type*) [CommRing R]

/-- Newton's identity with all power-sum indices restricted to positive integers. -/
theorem powerSum_newton (n : ℕ+) :
    powerSum R n = (-1) ^ (n.val + 1) * (n.val : SymmetricFunction R) *
      elementary R n.val -
      ∑ a ∈ Finset.antidiagonal n.val with a.1 ∈ Set.Ioo 0 n.val,
        (-1) ^ a.1 * elementary R a.1 *
          (if h : 0 < a.2 then powerSum R ⟨a.2, h⟩ else 0) := by
  classical
  apply ext_restrict
  intro N
  simp only [restrict_powerSum, map_sub, map_mul, map_pow, map_neg, map_one,
    map_natCast, restrict_elementary, map_sum, apply_dite, map_zero]
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin N) R n.val n.pos]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have hmem := Finset.mem_filter.mp ha
  have hsum := Finset.mem_antidiagonal.mp hmem.1
  have hpos : 0 < a.2 := by
    have hlt := hmem.2.2
    omega
  simp only [dite_eq_left hpos]
  rw [restrict_powerSum (R := R) N ⟨a.2, hpos⟩]
  rfl

/-- Newton's identity in degree two for finitely many variables: `p_1^2 = p_2 + 2 e_2`. -/
private theorem psum_one_sq (σ : Type*) [Fintype σ] :
    MvPolynomial.psum σ R 1 ^ 2 = MvPolynomial.psum σ R 2 + 2 * MvPolynomial.esymm σ R 2 := by
  have h := MvPolynomial.mul_esymm_eq_sum σ R 2
  simp only [MvPolynomial.psum, pow_one] at h ⊢
  simp only [Finset.sum_filter] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp [Finset.sum_range_succ, MvPolynomial.esymm_one] at h
  linear_combination -h

/-- Newton's identity in degree two: `p_1^2 = p_2 + 2 e_2`. -/
theorem powerSum_one_sq : powerSum R 1 ^ 2 = powerSum R 2 + 2 * elementary R 2 := by
  apply ext_restrict
  intro N
  simp only [map_pow, map_add, map_mul, map_ofNat, restrict_powerSum, restrict_elementary,
    PNat.val_ofNat]
  exact psum_one_sq R (Fin N)

end SymmetricFunction
