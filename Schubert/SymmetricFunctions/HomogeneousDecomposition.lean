import Schubert.SymmetricFunctions.Components
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.GradedAlgebra.Basic

/-! # The direct sum of homogeneous components

The ranges of the homogeneous projections form a direct-sum decomposition of symmetric
functions. Every element has finitely many nonzero homogeneous components.

## Main results

* `SymmetricFunction.mem_range_homogeneousComponent` identifies each projection range.
* `SymmetricFunction.exists_homogeneousSumEquiv` provides the normalized linear equivalence.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommSemiring R]

/-- The range of a homogeneous projection consists exactly of functions of that degree. -/
theorem mem_range_homogeneousComponent (d : ℕ) (f : SymmetricFunction R) :
    f ∈ (homogeneousComponent R d).range ↔ IsHomogeneous f d := by
  constructor
  · rintro ⟨g, rfl⟩
    exact isHomogeneous_homogeneousComponent g d
  · intro hf
    exact ⟨f, isHomogeneous_iff_component.mp hf⟩

/-- Projecting a finite sum of homogeneous functions extracts its component of that degree. -/
theorem homogeneousComponent_lsum (d : ℕ)
    (c : Π₀ k : ℕ, (homogeneousComponent R k).range) :
    homogeneousComponent R d
        (DFinsupp.lsum R (fun k => (homogeneousComponent R k).range.subtype) c) =
      (c d).val := by
  classical
  have hmaps : (homogeneousComponent R d).comp
      (DFinsupp.lsum R (fun k => (homogeneousComponent R k).range.subtype)) =
      (homogeneousComponent R d).range.subtype.comp (DFinsupp.lapply d) := by
    apply DFinsupp.lhom_ext
    intro k x
    simp only [LinearMap.comp_apply, DFinsupp.lsum_single, DFinsupp.lapply_apply,
      Submodule.subtype_apply]
    rw [homogeneousComponent_of_isHomogeneous
      ((mem_range_homogeneousComponent k x.val).mp x.property)]
    by_cases h : d = k
    · subst k
      simp
    · simp [h, Ne.symm h]
  exact LinearMap.congr_fun hmaps c

/-- Homogeneous functions assemble into a linear equivalence normalized on single components. -/
theorem exists_homogeneousSumEquiv (R : Type*) [CommSemiring R] :
    ∃ e : (Π₀ d : ℕ, (homogeneousComponent R d).range) ≃ₗ[R] SymmetricFunction R,
      (∀ d (f : (homogeneousComponent R d).range), e (DFinsupp.single d f) = f.val) ∧
      (∀ f d, (e.symm f d).val = homogeneousComponent R d f) := by
  classical
  let S := DFinsupp.lsum R (fun d => (homogeneousComponent R d).range.subtype)
  have hinj : Function.Injective S := by
    intro c z h
    apply DFinsupp.ext
    intro d
    apply Subtype.ext
    rw [← homogeneousComponent_lsum d c, ← homogeneousComponent_lsum d z]
    exact congrArg (homogeneousComponent R d) h
  have hsurj : Function.Surjective S := by
    intro f
    obtain ⟨D, hD⟩ := exists_mem_degreeFiltration f
    refine ⟨∑ d ∈ Finset.range (D + 1), DFinsupp.single d
      ⟨homogeneousComponent R d f, ⟨f, rfl⟩⟩, ?_⟩
    dsimp only [S]
    simp only [map_sum, DFinsupp.lsum_single, Submodule.subtype_apply]
    exact sum_homogeneousComponent hD
  let e := LinearEquiv.ofBijective S ⟨hinj, hsurj⟩
  refine ⟨e, ?_, ?_⟩
  · intro d f
    change DFinsupp.lsum R (fun k => (homogeneousComponent R k).range.subtype)
      (DFinsupp.single d f) = f.val
    exact DFinsupp.lsum_single R (fun k => (homogeneousComponent R k).range.subtype) d f
  · intro f d
    rw [← homogeneousComponent_lsum d (e.symm f)]
    exact congrArg (homogeneousComponent R d) (e.apply_symm_apply f)

/-- The normalized equivalence assembling the direct sum of homogeneous components. -/
def homogeneousSumEquiv (R : Type*) [CommSemiring R] :
    (Π₀ d : ℕ, (homogeneousComponent R d).range) ≃ₗ[R] SymmetricFunction R :=
  (exists_homogeneousSumEquiv R).choose

/-- A single homogeneous component is included as its underlying symmetric function. -/
@[simp]
theorem homogeneousSumEquiv_single (d : ℕ) (f : (homogeneousComponent R d).range) :
    homogeneousSumEquiv R (DFinsupp.single d f) = f.val :=
  (exists_homogeneousSumEquiv R).choose_spec.1 d f

/-- The inverse assembly map returns each homogeneous projection. -/
@[simp]
theorem homogeneousSumEquiv_symm_apply (f : SymmetricFunction R) (d : ℕ) :
    ((homogeneousSumEquiv R).symm f d).val = homogeneousComponent R d f :=
  (exists_homogeneousSumEquiv R).choose_spec.2 f d

/-- Assembly is the canonical linear sum of the homogeneous inclusions. -/
theorem homogeneousSumEquiv_toLinearMap :
    (homogeneousSumEquiv R).toLinearMap = DirectSum.coeLinearMap (homogeneousSubmodule R) := by
  classical
  apply DFinsupp.lhom_ext
  intro d f
  change homogeneousSumEquiv R (DFinsupp.single d f) =
    DirectSum.coeLinearMap (homogeneousSubmodule R) (DirectSum.of _ d f)
  exact (homogeneousSumEquiv_single d f).trans
    (DirectSum.coeLinearMap_of (homogeneousSubmodule R) d f).symm

/-- The homogeneous submodules give the natural grading of the symmetric-function algebra. -/
instance gradedAlgebra : GradedAlgebra (homogeneousSubmodule R) := by
  classical
  let e := homogeneousSumEquiv R
  have hsum : e.toLinearMap = DirectSum.coeLinearMap (homogeneousSubmodule R) :=
    homogeneousSumEquiv_toLinearMap
  let D := DirectSum.Decomposition.ofLinearMap (homogeneousSubmodule R) e.symm.toLinearMap
    (by
      rw [← hsum]
      apply LinearMap.ext
      intro f
      exact e.apply_symm_apply f)
    (by
      rw [← hsum]
      apply LinearMap.ext
      intro c
      exact e.symm_apply_apply c)
  exact
    { D with
      one_mem := (mem_homogeneousSubmodule 0 _).mpr IsHomogeneous.one
      mul_mem := by
        intro i j f g hf hg
        exact (mem_homogeneousSubmodule _ _).mpr
          (IsHomogeneous.mul ((mem_homogeneousSubmodule _ _).mp hf)
            ((mem_homogeneousSubmodule _ _).mp hg)) }

/-- The standard graded decomposition agrees with homogeneous projection. -/
theorem decompose_apply (f : SymmetricFunction R) (d : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule R) f d).val = homogeneousComponent R d f := by
  have h := homogeneousComponent_lsum (R := R) d
    (DirectSum.decompose (homogeneousSubmodule R) f)
  exact h.symm.trans (congrArg (homogeneousComponent R d)
    ((DirectSum.decompose (homogeneousSubmodule R)).symm_apply_apply f))

end SymmetricFunction
