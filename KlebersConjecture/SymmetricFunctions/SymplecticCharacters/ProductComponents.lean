import KlebersConjecture.SymmetricFunctions.Components
import KlebersConjecture.SymmetricFunctions.SymplecticCharacters.Grading

/-! # Top homogeneous components of products

The component at the sum of two upper degree bounds is the product of the components
at those bounds. In particular, symplectic-character products have Schur products on top.

## Main results

* `homogeneousComponent_mul_top` multiplies components at upper degree bounds.
* `homogeneousComponent_symplectic_mul` gives the top Schur product of two characters.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommRing R]

/-- The homogeneous component at the sum of upper degree bounds multiplies the top components. -/
theorem homogeneousComponent_mul_top {f g : SymmetricFunction R} {d k : ℕ}
    (hf : f ∈ degreeFiltration R d) (hg : g ∈ degreeFiltration R k) :
    homogeneousComponent R (d + k) (f * g) =
      homogeneousComponent R d f * homogeneousComponent R k g := by
  classical
  apply ext
  intro n
  rw [coeff_homogeneousComponent]
  by_cases hn : n.degree = d + k
  · rw [ite_eq_left hn, coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    have hdeg : p.1.degree + p.2.degree = n.degree := by rw [← map_add, hsum]
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases hleft : p.1.degree = d
    · have hright : p.2.degree = k := by omega
      rw [ite_eq_left hleft, ite_eq_left hright]
    · rw [ite_eq_right hleft, zero_mul]
      by_cases hhigh : d < p.1.degree
      · have hz : coeff R p.1 f = 0 := (mem_degreeFiltration_iff d f).mp hf p.1 hhigh
        rw [hz, zero_mul]
      · have hz : coeff R p.2 g = 0 := (mem_degreeFiltration_iff k g).mp hg p.2 (by omega)
        rw [hz, mul_zero]
  · rw [ite_eq_right hn]
    have hhom : IsHomogeneous
        (homogeneousComponent R d f * homogeneousComponent R k g) (d + k) :=
      IsHomogeneous.mul (isHomogeneous_homogeneousComponent f d)
        (isHomogeneous_homogeneousComponent g k)
    exact (IsHomogeneous.coeff_eq_zero hhom hn).symm

/-- The top component of a symplectic-character product is the corresponding Schur product. -/
theorem homogeneousComponent_symplectic_mul (α β : YoungDiagram) :
    homogeneousComponent R (α.card + β.card)
      (symplecticCharacter R α * symplecticCharacter R β) = schur R α * schur R β := by
  rw [homogeneousComponent_mul_top (symplecticCharacter_mem_degreeFiltration α)
      (symplecticCharacter_mem_degreeFiltration β),
    homogeneousComponent_symplecticCharacter, homogeneousComponent_symplecticCharacter]

end SymmetricFunction
