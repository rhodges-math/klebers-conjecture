import Schubert.SymmetricFunctions.LittlewoodRichardson.Coordinates

/-! # Stable Littlewood--Richardson coefficients

Integral Schur product coordinates are nonnegative and hence define natural coefficients.
Their finite expansion transfers to every commutative coefficient semiring.

## Main results

* `lrCoeff` is the natural Schur product coordinate.
* `intCast_lrCoeff` recovers the integral coordinate.
* `lrSupport` and `mem_lrSupport` describe finite nonzero coefficient support.
* `exists_lr_alphabet_bound` supplies a common finite alphabet.
* `schur_mul_schur` expands products over any commutative semiring.
* `schurBasis_repr_schur_mul_schur` identifies the corresponding basis coordinates.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction

/-- The natural Littlewood--Richardson coefficient of a stable Schur product. -/
def lrCoeff (α β γ : YoungDiagram) : ℕ :=
  ((schurBasis ℤ).repr (schur ℤ α * schur ℤ β) γ).toNat

/-- Casting the natural coefficient back to integers recovers the Schur coordinate. -/
@[simp]
theorem intCast_lrCoeff (α β γ : YoungDiagram) :
    (lrCoeff α β γ : ℤ) = (schurBasis ℤ).repr (schur ℤ α * schur ℤ β) γ :=
  Int.toNat_of_nonneg (schurBasis_repr_mul_nonneg α β γ)

/-- Nonzero natural coefficients are exactly the integral coordinate support. -/
theorem lrCoeff_ne_zero_iff (α β γ : YoungDiagram) :
    lrCoeff α β γ ≠ 0 ↔
      γ ∈ ((schurBasis ℤ).repr (schur ℤ α * schur ℤ β)).support := by
  rw [Finsupp.mem_support_iff, ← intCast_lrCoeff]
  exact_mod_cast Iff.rfl

/-- The finite set of diagrams with nonzero Littlewood--Richardson coefficient. -/
def lrSupport (α β : YoungDiagram) : Finset YoungDiagram :=
  ((schurBasis ℤ).repr (schur ℤ α * schur ℤ β)).support

/-- Membership in the Littlewood--Richardson support is nonvanishing. -/
@[simp]
theorem mem_lrSupport (α β γ : YoungDiagram) :
    γ ∈ lrSupport α β ↔ lrCoeff α β γ ≠ 0 :=
  (lrCoeff_ne_zero_iff α β γ).symm

/-- A finite alphabet simultaneously contains the arguments and coefficient support. -/
theorem exists_lr_alphabet_bound (α β γ : YoungDiagram) :
    ∃ n, α.colLen 0 ≤ n ∧ γ.colLen 0 ≤ n ∧
      ∀ ν ∈ lrSupport α β, ν.colLen 0 ≤ n :=
  exists_schur_alphabet_bound (schur ℤ α * schur ℤ β) α γ

/-- Only finitely many diagrams have a nonzero Littlewood--Richardson coefficient. -/
theorem finite_support_lrCoeff (α β : YoungDiagram) :
    {γ | lrCoeff α β γ ≠ 0}.Finite := by
  have h : {γ | lrCoeff α β γ ≠ 0} =
      (((schurBasis ℤ).repr (schur ℤ α * schur ℤ β)).support : Set YoungDiagram) := by
    ext γ
    exact lrCoeff_ne_zero_iff α β γ
  rw [h]
  exact Finset.finite_toSet _

/-- Interchanging the two Schur factors preserves the coefficient. -/
theorem lrCoeff_comm (α β γ : YoungDiagram) : lrCoeff α β γ = lrCoeff β α γ := by
  simp only [lrCoeff, mul_comm]

/-- Natural coefficients recover the integral Schur product expansion. -/
private theorem schur_mul_schur_int (α β : YoungDiagram) :
    schur ℤ α * schur ℤ β =
      ∑ γ ∈ lrSupport α β, lrCoeff α β γ • schur ℤ γ := by
  classical
  have he := (schurBasis ℤ).linearCombination_repr (schur ℤ α * schur ℤ β)
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at he
  simp only [schurBasis_apply, ← intCast_lrCoeff, Nat.cast_smul_eq_nsmul] at he
  exact he.symm

/-- Natural coefficients give the Schur product expansion over every commutative semiring. -/
private theorem schur_mul_schur_nsmul (R : Type*) [CommSemiring R] (α β : YoungDiagram) :
    schur R α * schur R β =
      ∑ γ ∈ lrSupport α β, lrCoeff α β γ • schur R γ := by
  classical
  have hnat : schur ℕ α * schur ℕ β =
      ∑ γ ∈ lrSupport α β, lrCoeff α β γ • schur ℕ γ := by
    apply map_injective (Nat.castRingHom ℤ) Nat.cast_injective
    simp only [map_mul, map_sum, map_nsmul, map_schur]
    exact schur_mul_schur_int α β
  have he := congrArg (map (Nat.castRingHom R)) hnat
  simpa only [map_mul, map_sum, map_nsmul, map_schur] using he

/-- The Schur product has the natural structure constants over every commutative semiring. -/
theorem schur_mul_schur (R : Type*) [CommSemiring R] (α β : YoungDiagram) :
    schur R α * schur R β =
      ∑ γ ∈ lrSupport α β, (lrCoeff α β γ : R) • schur R γ := by
  simpa only [Nat.cast_smul_eq_nsmul] using schur_mul_schur_nsmul R α β

/-- The scalar-cast form of the Schur expansion has the same finite coefficient support. -/
theorem schur_mul_eq_sum_lrCoeff (R : Type*) [CommSemiring R] (α β : YoungDiagram) :
    schur R α * schur R β =
      ∑ γ ∈ ((schurBasis ℤ).repr (schur ℤ α * schur ℤ β)).support,
        (lrCoeff α β γ : R) • schur R γ := by
  simpa only [lrSupport] using schur_mul_schur R α β

/-- In every coefficient ring, the Schur product coordinate is the natural coefficient cast. -/
theorem schurBasis_repr_schur_mul_schur (R : Type*) [CommRing R] (α β γ : YoungDiagram) :
    (schurBasis R).repr (schur R α * schur R β) γ = (lrCoeff α β γ : R) := by
  classical
  rw [schur_mul_eq_sum_lrCoeff R α β]
  simp only [map_sum, map_smul, ← schurBasis_apply, Module.Basis.repr_self,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply]
  by_cases hγ : γ ∈ ((schurBasis ℤ).repr (schur ℤ α * schur ℤ β)).support
  · simp [hγ]
  · have hz : lrCoeff α β γ = 0 := by
      by_contra h
      exact hγ ((lrCoeff_ne_zero_iff α β γ).mp h)
    simp [hγ, hz]

end SymmetricFunction
