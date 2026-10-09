import KlebersConjecture.SymmetricFunctions.HomogeneousDecomposition
import KlebersConjecture.SymmetricFunctions.Families.Monomial
import KlebersConjecture.SymmetricFunctions.Transfer
import KlebersConjecture.SymmetricFunctions.Families.Schur
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basis

/-! # Restriction of homogeneous symmetric functions

An alphabet with at least as many letters as the degree records every homogeneous symmetric
function. The finite monomial basis lifts to stable monomial functions.

## Main results

* `SymmetricFunction.IsHomogeneous.restrict` preserves homogeneous degree.
* `SymmetricFunction.exists_homogeneousRestrictEquiv` provides normalized restriction.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommSemiring R]

/-- Restricting an alphabet preserves the degree of a homogeneous symmetric function. -/
theorem IsHomogeneous.restrict {f : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) (N : ℕ) : (restrict R N f).IsHomogeneous d := by
  intro m hm
  have ht := hf (d := Finsupp.embDomain (variableEmbedding N) m)
    (by
      change coeff R (Finsupp.embDomain (variableEmbedding N) m) f ≠ 0
      rwa [← coeff_restrict N m f])
  change Finsupp.weight (fun _ : ℕ => 1) (Finsupp.embDomain (variableEmbedding N) m) = d at ht
  change Finsupp.weight (fun _ : Fin N => 1) m = d
  rw [← Finsupp.degree_eq_weight_one] at ht ⊢
  simpa only [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain] using ht

/-- Restriction on a single homogeneous submodule, with its symmetric homogeneous codomain. -/
def homogeneousRestrict (R : Type*) [CommSemiring R] (d N : ℕ) :
    (homogeneousComponent R d).range →ₗ[R]
      TauCeti.symmetricHomogeneousSubmodule (Fin N) R d :=
  ((restrict R N).toLinearMap.comp (homogeneousComponent R d).range.subtype).codRestrict
      (TauCeti.symmetricHomogeneousSubmodule (Fin N) R d) (by
        intro f
        apply TauCeti.mem_symmetricHomogeneousSubmodule.mpr
        exact ⟨isSymmetric_restrict N f.val,
          IsHomogeneous.restrict ((mem_range_homogeneousComponent d f.val).mp f.property) N⟩)

/-- Forgetting homogeneous membership recovers polynomial restriction. -/
@[simp]
theorem coe_homogeneousRestrict (d N : ℕ) (f : (homogeneousComponent R d).range) :
    (homogeneousRestrict R d N f : MvPolynomial (Fin N) R) = restrict R N f.val := rfl

/-- Every finite homogeneous symmetric polynomial lifts to a stable homogeneous function. -/
theorem homogeneousRestrict_surjective (R : Type*) [CommSemiring R] (d N : ℕ) :
    Function.Surjective (homogeneousRestrict R d N) := by
    classical
    intro p
    let b := TauCeti.msymmBasis (Fin N) R d
    let lift : {ν : d.Partition // ν.parts.card ≤ Fintype.card (Fin N)} →
        (homogeneousComponent R d).range := fun ν =>
      ⟨monomial R (TauCeti.diagramOf ν.val),
        (mem_range_homogeneousComponent d _).mpr (by
          apply isHomogeneous_iff_component.mpr
          simpa only [TauCeti.card_diagramOf] using
            (isHomogeneous_iff_component.mp
              (@isHomogeneous_monomial R _ (TauCeti.diagramOf ν.val))))⟩
    have hS : ∀ ν, homogeneousRestrict R d N (lift ν) = b ν := by
      intro ν
      apply Subtype.ext
      change restrict R N (monomial R (TauCeti.diagramOf ν.val)) = _
      rw [TauCeti.coe_msymmBasis]
      exact restrict_monomial_diagramOf N ν.val
    refine ⟨∑ ν, b.repr p ν • lift ν, ?_⟩
    simp only [map_sum, map_smul, hS]
    exact b.sum_repr p

/-- In degree at most the alphabet size, restriction is a normalized linear equivalence. -/
theorem exists_homogeneousRestrictEquiv (R : Type*) [CommSemiring R] (d N : ℕ) (hdN : d ≤ N) :
    ∃ e : (homogeneousComponent R d).range ≃ₗ[R]
        TauCeti.symmetricHomogeneousSubmodule (Fin N) R d,
      ∀ f, (e f : MvPolynomial (Fin N) R) = restrict R N f.val := by
  classical
  let S := homogeneousRestrict R d N
  have hinj : Function.Injective S := by
    intro f g h
    apply Subtype.ext
    apply restrict_inj_of_degreeBound
      ((IsHomogeneous.mem_degreeFiltration
        ((mem_range_homogeneousComponent d f.val).mp f.property)).mono hdN)
      ((IsHomogeneous.mem_degreeFiltration
        ((mem_range_homogeneousComponent d g.val).mp g.property)).mono hdN)
    exact congrArg Subtype.val h
  exact ⟨LinearEquiv.ofBijective S ⟨hinj, homogeneousRestrict_surjective R d N⟩,
    fun _ => rfl⟩

/-- Restriction identifies homogeneous functions with a sufficiently large finite alphabet. -/
def homogeneousRestrictEquiv (R : Type*) [CommSemiring R] (d N : ℕ) (hdN : d ≤ N) :
    (homogeneousComponent R d).range ≃ₗ[R]
      TauCeti.symmetricHomogeneousSubmodule (Fin N) R d :=
  (exists_homogeneousRestrictEquiv R d N hdN).choose

/-- The normalized homogeneous equivalence is polynomial restriction on underlying elements. -/
@[simp]
theorem coe_homogeneousRestrictEquiv (d N : ℕ) (hdN : d ≤ N)
    (f : (homogeneousComponent R d).range) :
    (homogeneousRestrictEquiv R d N hdN f : MvPolynomial (Fin N) R) =
      restrict R N f.val :=
  (exists_homogeneousRestrictEquiv R d N hdN).choose_spec f

/-- The linear map underlying the equivalence is the canonical homogeneous restriction. -/
theorem homogeneousRestrictEquiv_toLinearMap (d N : ℕ) (hdN : d ≤ N) :
    (homogeneousRestrictEquiv R d N hdN).toLinearMap = homogeneousRestrict R d N := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact coe_homogeneousRestrictEquiv d N hdN f

/-- Every finite symmetric polynomial is the restriction of a stable symmetric function. -/
theorem restrictSymmetric_surjective (N : ℕ) :
    Function.Surjective (restrictSymmetric R N) := by
  classical
  intro p
  let q (d : ℕ) : TauCeti.symmetricHomogeneousSubmodule (Fin N) R d :=
    ⟨MvPolynomial.homogeneousComponent d p.val,
      TauCeti.mem_symmetricHomogeneousSubmodule.mpr ⟨by
        intro e
        rw [MvPolynomial.rename_homogeneousComponent]
        exact congrArg (MvPolynomial.homogeneousComponent d) (p.property e),
        MvPolynomial.homogeneousComponent_isHomogeneous d p.val⟩⟩
  choose f hf using fun d => homogeneousRestrict_surjective R d N (q d)
  refine ⟨∑ d ∈ Finset.range (p.val.totalDegree + 1), (f d).val, ?_⟩
  apply Subtype.ext
  change restrict R N (∑ d ∈ Finset.range (p.val.totalDegree + 1), (f d).val) = p.val
  rw [map_sum]
  have h (d : ℕ) : restrict R N (f d).val = MvPolynomial.homogeneousComponent d p.val :=
    congrArg Subtype.val (hf d)
  simp_rw [h]
  exact MvPolynomial.sum_homogeneousComponent p.val

end SymmetricFunction
