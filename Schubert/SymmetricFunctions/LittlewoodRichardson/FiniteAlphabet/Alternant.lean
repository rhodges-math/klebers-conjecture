import Schubert.SymmetricFunctions.LittlewoodRichardson.FiniteAlphabet.Laurent
import TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant
import Mathlib.Data.Fin.Tuple.Sort

/-! # Integral Laurent alternants

Permutation actions on integral Laurent polynomials define symmetric and antisymmetric
elements and the alternating sums associated to weights.

## Main results

* `coeff_alternant_of_strictAnti`: strictly decreasing weights distinguish alternants.
* `alternant_mul_sum_single`: multiplication distributes into shifted alternants.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction.FiniteAlphabet.Alternants

open Equiv

variable {d : ℕ}

/-- Permuting the coordinates of a weight: `w ↦ w ∘ σ⁻¹`. -/
def permWeight (σ : Perm (Fin d)) : IntWeight d ≃+ IntWeight d where
  toFun w := w ∘ σ.symm
  invFun w := w ∘ σ
  left_inv w := by ext; simp
  right_inv w := by ext; simp
  map_add' _ _ := rfl

/-- The substitution `x_i ↦ x_{σ i}` on Laurent polynomials. -/
def permute (σ : Perm (Fin d)) : IntLaurent d ≃+* IntLaurent d :=
  AddMonoidAlgebra.mapDomainRingEquiv ℤ (permWeight σ)

/-- A coordinate permutation transports a single Laurent exponent. -/
@[simp] theorem permute_single (σ : Perm (Fin d)) (w : IntWeight d) (z : ℤ) :
    permute σ (AddMonoidAlgebra.single w z) = AddMonoidAlgebra.single (w ∘ σ.symm) z :=
  AddMonoidAlgebra.mapDomainRingEquiv_single _ _ _

/-- Permuting a Laurent polynomial composes its coefficient indices. -/
theorem coeff_permute (σ : Perm (Fin d)) (f : IntLaurent d) (w : IntWeight d) :
    (permute σ f).coeff w = f.coeff (w ∘ σ) := by
  simp only [permute, AddMonoidAlgebra.coeff_mapDomainRingEquiv, Finsupp.equivMapDomain_apply]
  rfl

/-- The coefficient of a constant multiple. -/
theorem coeff_single_zero_mul (k : ℤ) (g : IntLaurent d) (w : IntWeight d) :
    (AddMonoidAlgebra.single 0 k * g).coeff w = k * g.coeff w := by
  simp

/-- `f` is symmetric: invariant under every permutation of the variables. -/
def IsSymmetric (f : IntLaurent d) : Prop := ∀ σ : Perm (Fin d), permute σ f = f

/-- `g` is antisymmetric: permuting an exponent by `σ` multiplies its coefficient by the sign of
`σ`. -/
def IsAntisymmetric (g : IntLaurent d) : Prop :=
  ∀ (σ : Perm (Fin d)) (w : IntWeight d), g.coeff (w ∘ σ) = (Perm.sign σ : ℤ) * g.coeff w

/-- Products of permutation-invariant Laurent polynomials remain invariant. -/
theorem IsSymmetric.mul {f g : IntLaurent d} (hf : IsSymmetric f) (hg : IsSymmetric g) :
    IsSymmetric (f * g) := fun σ => by rw [map_mul, hf σ, hg σ]

/-- An antisymmetric Laurent polynomial has zero coefficient at every exponent with a repeated
entry. -/
theorem IsAntisymmetric.coeff_eq_zero_of_not_injective {g : IntLaurent d} (hg : IsAntisymmetric g)
    {w : IntWeight d} (hw : ¬ Function.Injective w) : g.coeff w = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hw
  have hfix : w ∘ Equiv.swap i j = w := by
    funext k
    simp only [Function.comp_apply]
    rcases eq_or_ne k i with rfl | hki
    · simp [hij]
    rcases eq_or_ne k j with rfl | hkj
    · simp [hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h := hg (Equiv.swap i j) w
  rw [hfix, Perm.sign_swap hne] at h
  simp only [Units.val_neg, Units.val_one, neg_mul, one_mul] at h
  omega

/-- Every injective exponent vector has a strictly decreasing rearrangement. -/
theorem exists_strictAnti_comp {w : IntWeight d} (hw : Function.Injective w) :
    ∃ τ : Perm (Fin d), StrictAnti (w ∘ τ) := by
  refine ⟨Tuple.sort (fun i => -w i), ?_⟩
  have hm := Tuple.monotone_sort (fun i => -w i)
  have ha : Antitone (w ∘ Tuple.sort (fun i => -w i)) := fun i j hij => by
    have := hm hij
    simp only [Function.comp_apply] at this ⊢
    linarith
  exact ha.strictAnti_of_injective (hw.comp (Equiv.injective _))

/-- The alternant `a_α = ∑_σ sign(σ) x^{α ∘ σ⁻¹}`. -/
def alternant (α : IntWeight d) : IntLaurent d :=
  ∑ σ : Perm (Fin d), AddMonoidAlgebra.single (α ∘ σ.symm) (Perm.sign σ : ℤ)

/-- The staircase `δ = (d − 1, …, 1, 0)`. -/
def staircase (d : ℕ) : IntWeight d := fun i => (d : ℤ) - 1 - i

/-- The staircase weight is strictly decreasing. -/
theorem staircase_strictAnti (d : ℕ) : StrictAnti (staircase d) := fun i j hij => by
  simp only [staircase]
  have : (i : ℤ) < j := by exact_mod_cast hij
  linarith

/-- Alternant coefficients are the signed counts of exponent permutations. -/
theorem coeff_alternant (α β : IntWeight d) :
    (alternant α).coeff β =
      ∑ σ : Perm (Fin d), if α ∘ σ.symm = β then (Perm.sign σ : ℤ) else 0 := by
  classical
  simp only [alternant, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- Permuting an alternant multiplies it by the permutation sign. -/
theorem permute_alternant (τ : Perm (Fin d)) (α : IntWeight d) :
    permute τ (alternant α) = AddMonoidAlgebra.single 0 (Perm.sign τ : ℤ) * alternant α := by
  rw [alternant, map_sum, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  have hs : (((τ * σ).symm : Perm (Fin d)) : Fin d → Fin d) = σ.symm ∘ τ.symm := by
    rw [← Perm.inv_def, mul_inv_rev, Perm.coe_mul, Perm.inv_def, Perm.inv_def]
  have hsign : (Perm.sign τ : ℤ) * (Perm.sign (τ * σ) : ℤ) = Perm.sign σ := by
    rw [Perm.sign_mul]
    rcases Int.units_eq_one_or (Perm.sign τ) with h | h <;> simp [h]
  simp only [permute_single, Equiv.coe_mulLeft, AddMonoidAlgebra.single_mul_single, zero_add, hs,
    hsign]
  rfl

/-- An alternant times a symmetric Laurent polynomial is antisymmetric. -/
theorem isAntisymmetric_alternant_mul (α : IntWeight d) {f : IntLaurent d} (hf : IsSymmetric f) :
    IsAntisymmetric (alternant α * f) := fun σ w => by
  rw [← coeff_permute, map_mul, hf σ, permute_alternant, mul_assoc, coeff_single_zero_mul]

/-- Permuting the weight of an alternant multiplies it by the sign. -/
theorem alternant_comp_perm (α : IntWeight d) (τ : Perm (Fin d)) :
    alternant (α ∘ τ) = AddMonoidAlgebra.single 0 (Perm.sign τ : ℤ) * alternant α := by
  ext β
  rw [coeff_single_zero_mul, coeff_alternant, coeff_alternant, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight τ⁻¹) _ _ fun σ => ?_
  have hs : (((σ * τ⁻¹).symm : Perm (Fin d)) : Fin d → Fin d) = τ ∘ σ.symm := by
    rw [← Perm.inv_def, mul_inv_rev, inv_inv, Perm.coe_mul, Perm.inv_def]
  have hsign : (Perm.sign τ : ℤ) * (Perm.sign (σ * τ⁻¹) : ℤ) = Perm.sign σ := by
    rw [Perm.sign_mul, Perm.sign_inv]
    rcases Int.units_eq_one_or (Perm.sign τ) with h | h <;> simp [h]
  simp only [Equiv.coe_mulRight, hs, Function.comp_assoc]
  split_ifs
  · exact hsign.symm
  · simp

/-- For strictly decreasing `α` and `β`, the coefficient of `x^β` in `a_α` is `[α = β]`. -/
theorem coeff_alternant_of_strictAnti {α β : IntWeight d} (hα : StrictAnti α) (hβ : StrictAnti β) :
    (alternant α).coeff β = if α = β then 1 else 0 := by
  rw [coeff_alternant, Finset.sum_eq_single (1 : Perm (Fin d))]
  · have h1 : α ∘ ⇑(Equiv.symm (1 : Perm (Fin d))) = α := rfl
    simp [h1]
  · intro σ _ hσ
    split_ifs with hαβ
    · exfalso
      have hanti : Antitone (α ∘ ⇑σ.symm) := hαβ ▸ hβ.antitone
      have h1 := Tuple.unique_antitone (f := α) (σ := σ.symm) (τ := 1) hanti
        (by simpa using hα.antitone)
      apply hσ
      refine Equiv.ext fun i => ?_
      have := congrFun h1 (σ i)
      simp only [Function.comp_apply, Perm.coe_one, id_eq, Equiv.symm_apply_apply] at this
      simpa using (hα.injective this).symm
    · rfl
  · simp

/-- An alternant at a strictly decreasing weight is nonzero. -/
theorem alternant_ne_zero {α : IntWeight d} (hα : StrictAnti α) : alternant α ≠ 0 := by
  intro h
  have := coeff_alternant_of_strictAnti hα hα
  rw [h] at this
  simp at this

/-- **Alternant times a symmetric sum of monomials**: if `∑_{t ∈ S} x^{w_t}` is symmetric then
`a_α · ∑_{t ∈ S} x^{w_t} = ∑_{t ∈ S} a_{α + w_t}`. -/
theorem alternant_mul_sum_single {ι : Type*} (α : IntWeight d) (S : Finset ι) (w : ι → IntWeight d)
    (hS : IsSymmetric (∑ t ∈ S, AddMonoidAlgebra.single (w t) (1 : ℤ))) :
    alternant α * ∑ t ∈ S, AddMonoidAlgebra.single (w t) (1 : ℤ) =
      ∑ t ∈ S, alternant (α + w t) := by
  set F := ∑ t ∈ S, AddMonoidAlgebra.single (w t) (1 : ℤ)
  have hσ : ∀ σ : Perm (Fin d), AddMonoidAlgebra.single (α ∘ σ.symm) (Perm.sign σ : ℤ) * F =
      ∑ t ∈ S, AddMonoidAlgebra.single ((α + w t) ∘ σ.symm) (Perm.sign σ : ℤ) := by
    intro σ
    have h1 : AddMonoidAlgebra.single (α ∘ σ.symm) (Perm.sign σ : ℤ) * F =
        permute σ (AddMonoidAlgebra.single α (Perm.sign σ : ℤ) * F) := by
      rw [map_mul, permute_single, hS σ]
    rw [h1, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [AddMonoidAlgebra.single_mul_single, mul_one, permute_single]
  rw [alternant, Finset.sum_mul]
  simp_rw [hσ]
  rw [Finset.sum_comm]
  rfl

/-- The Tau Ceti alternant of a natural exponent vector, as a Laurent polynomial. -/
theorem toLaurent_alternant (α : Fin d → ℕ) :
    toLaurent (TauCeti.alternant (Fin d) ℤ α) = alternant (fun i => (α i : ℤ)) := by
  rw [TauCeti.alternant_eq_sum, map_sum, alternant]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hprod : (∏ i, (MvPolynomial.X (σ i) : MvPolynomial (Fin d) ℤ) ^ α i) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (α ∘ σ.symm)) 1 := by
    rw [← Equiv.prod_comp σ.symm fun i => (MvPolynomial.X (σ i) : MvPolynomial (Fin d) ℤ) ^ α i]
    simp only [Equiv.apply_symm_apply]
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod_fintype]
    · rfl
    · intro i
      simp
  have hw : exponentWeight (Finsupp.equivFunOnFinite.symm (α ∘ σ.symm)) =
      (fun i => (α i : ℤ)) ∘ σ.symm := by
    funext i
    rfl
  rw [hprod]
  rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs <;>
    simp [hs, toLaurent_monomial, hw]

/-- A weakly decreasing weight plus the staircase is strictly decreasing. -/
theorem strictAnti_add_staircase {lam : IntWeight d} (h : Antitone lam) :
    StrictAnti (lam + staircase d) :=
  h.add_strictAnti (staircase_strictAnti d)

end SymmetricFunction.FiniteAlphabet.Alternants

end
