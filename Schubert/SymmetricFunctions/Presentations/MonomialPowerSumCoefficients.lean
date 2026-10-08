import Schubert.SymmetricFunctions.Monomial.MonomialPowerSum
import Schubert.SymmetricFunctions.Presentations.PowerSumCoefficients
import Mathlib.Algebra.Algebra.Rat

/-! # Maximal power-sum coefficients of monomials

A monomial of bounded size is linear in the largest allowed power-sum generator.

## Main results

* `monomial_linear_powerSum` separates the largest generator from its coefficient algebra.
* `powerSumCoeff_linear_product` extracts the first coefficient of two linear expressions.
* `coeff_linear_monomial_product` evaluates its coordinates away from the single row.
-/

noncomputable section

open scoped Classical

namespace SymmetricFunction

variable {F : Type*} [Field F] [CharZero F]

/-- The canonical rational algebra on a characteristic-zero field. -/
local instance : Algebra ℚ F := DivisionRing.toRatAlgebra

/-- A bounded-size monomial is linear in the largest allowed power-sum generator. -/
theorem monomial_linear_powerSum (n : ℕ+) (μ : YoungDiagram) (hμ : μ.card ≤ n.val) :
    ∃ (c : F) (Q : SymmetricFunction F),
      (c ≠ 0 ↔ μ.card = n.val) ∧ monomial F μ = c • powerSum F n + Q ∧
      ((powerSumPresentation F).symm Q).degreeOf n = 0 := by
  classical
  let S := Algebra.adjoin F ((fun j : ℕ+ => powerSum F j) '' {j | j ≠ n})
  have hlow {m : ℕ+} (hm : m.val ≤ n.val) :
      Algebra.adjoin F ((fun j : ℕ+ => powerSum F j) '' {j | j.val < m.val}) ≤ S := by
    apply Algebra.adjoin_mono
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, fun he => by subst j; exact (Nat.not_lt_of_ge hm) hj, rfl⟩
  by_cases hz : μ = ⊥
  · subst μ
    refine ⟨0, 1, ?_, ?_, ?_⟩
    · exact ⟨False.elim ∘ fun h => h rfl, fun h => by
        have hc : (⊥ : YoungDiagram).card = 0 := rfl
        rw [hc] at h
        exact (Nat.ne_of_lt n.pos h).elim⟩
    · simp only [monomial_bot, zero_smul, zero_add]
    · rw [← mem_adjoin_powerSum_iff]
      exact S.one_mem
  have hp : 0 < μ.card := by
    have hr : 0 < μ.rowLen 0 :=
      Nat.pos_of_ne_zero ((YoungDiagram.eq_bot_iff_rowLen_zero μ).not.mp hz)
    exact hr.trans_le (μ.rowLen_le_card 0)
  let m : ℕ+ := ⟨μ.card, hp⟩
  obtain ⟨c, Q, _, hc, he, hQ⟩ := monomial_eq_smul_powerSum_add F μ hz m rfl
  by_cases hn : μ.card = n.val
  · have hm : m = n := Subtype.ext hn
    rw [hm] at he
    refine ⟨c, Q, ⟨fun _ => hn, fun _ => hc⟩, he, ?_⟩
    exact (mem_adjoin_powerSum_iff n Q).mp (hlow (m := m) hμ hQ)
  · refine ⟨0, monomial F μ, ?_, by simp, ?_⟩
    · exact ⟨fun h => (h rfl).elim, fun h => (hn h).elim⟩
    · apply (mem_adjoin_powerSum_iff n _).mp
      rw [he]
      apply S.add_mem
      · apply S.smul_mem
        exact Algebra.subset_adjoin ⟨m, fun hm => hn (congrArg Subtype.val hm), rfl⟩
      · exact hlow (m := m) hμ hQ

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The first coefficient of two linear generator expressions is their cross term. -/
theorem powerSumCoeff_linear_product (n : ℕ+) (a b : R) (f g : SymmetricFunction R)
    (hf : ((powerSumPresentation R).symm f).degreeOf n = 0)
    (hg : ((powerSumPresentation R).symm g).degreeOf n = 0) :
    powerSumCoeff R n 1 ((a • powerSum R n + f) * (b • powerSum R n + g)) =
      a • g + b • f := by
  have he : (a • powerSum R n + f) * (b • powerSum R n + g) =
      (a * b) • powerSum R n ^ 2 +
        a • (powerSum R n * g) + b • (powerSum R n * f) + f * g := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, pow_two]
    rw [mul_comm f (powerSum R n)]
    rw [smul_add, smul_smul, mul_comm b a]
    abel
  rw [he]
  simp only [map_add, map_smul, powerSumCoeff_generator_pow, ite_eq_right (by decide :
    (2 : ℕ) ≠ 1), smul_zero, zero_add]
  rw [show powerSum R n = powerSum R n ^ 1 by rw [pow_one],
    powerSumCoeff_generator_mul n 1 g hg, powerSumCoeff_generator_mul n 1 f hf,
    powerSumCoeff_mul_of_degreeOf_eq_zero n 1 f g hg,
    powerSumCoeff_pos_of_degreeOf_eq_zero n f hf (by decide), zero_mul, add_zero]

/-- Away from the single row, first generator coefficients give the two monomial coordinates. -/
theorem coeff_linear_monomial_product (n : ℕ+) (α β μ : YoungDiagram)
    (a b : R) (f g : SymmetricFunction R)
    (hα : monomial R α = a • powerSum R n + f)
    (hβ : monomial R β = b • powerSum R n + g)
    (hf : ((powerSumPresentation R).symm f).degreeOf n = 0)
    (hg : ((powerSumPresentation R).symm g).degreeOf n = 0)
    (hμ : μ ≠ TauCeti.diagramOf (Nat.Partition.indiscrete n.val)) :
    coeff R (rowExponent μ) (powerSumCoeff R n 1 (monomial R α * monomial R β)) =
      a * (if μ = β then 1 else 0) + b * (if μ = α then 1 else 0) := by
  classical
  have hp : coeff R (rowExponent μ) (powerSum R n) = 0 := by
    rw [powerSum, ← YoungDiagram.diagramOf_indiscrete_eq_singleRow,
      coeff_monomial_rowExponent, ite_eq_right hμ]
  have hcf : coeff R (rowExponent μ) f = if μ = α then 1 else 0 := by
    have he := congrArg (coeff R (rowExponent μ)) hα
    simpa only [coeff_monomial_rowExponent, map_add, map_smul, hp, smul_zero, zero_add]
      using he.symm
  have hcg : coeff R (rowExponent μ) g = if μ = β then 1 else 0 := by
    have he := congrArg (coeff R (rowExponent μ)) hβ
    simpa only [coeff_monomial_rowExponent, map_add, map_smul, hp, smul_zero, zero_add]
      using he.symm
  rw [hα, hβ, powerSumCoeff_linear_product n a b f g hf hg]
  simp only [map_add, map_smul, smul_eq_mul, hcf, hcg]

end SymmetricFunction
