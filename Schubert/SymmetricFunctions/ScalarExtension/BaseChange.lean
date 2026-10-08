import Schubert.SymmetricFunctions.Bases.MonomialBasis
import Schubert.SymmetricFunctions.Families.Monomial
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Tensor scalar extension of symmetric functions

The monomial bases identify extension of scalars from the integers with coefficientwise
extension of symmetric functions. The identification preserves multiplication and constants.

## Main results

* `SymmetricFunction.exists_baseChangeEquiv` gives a normalized algebra equivalence.
* `SymmetricFunction.baseChangeEquiv` identifies tensor and coefficient scalar extension.
* `SymmetricFunction.baseChangeEquiv_tmul` gives its value on every pure tensor.

## Implementation notes

The tensor carrier uses the integer action obtained from the coefficient algebra structure.
Lean can also find an integer module structure through the additive group of symmetric functions;
these actions agree mathematically but their instance terms need not reduce to the same term.
The local priority `attribute [local instance 1100] Algebra.toModule` selects the algebra action.
Consumers of the literal tensor statements should use this priority when elaborating the carrier.
-/

noncomputable section

open scoped TensorProduct

attribute [local instance 1100] Algebra.toModule

namespace SymmetricFunction

/-- Tensor extension from the integers admits an algebra equivalence preserving monomials. -/
theorem exists_baseChangeEquiv (R : Type*) [CommRing R] :
    ∃ e : R ⊗[ℤ] SymmetricFunction ℤ ≃ₐ[R] SymmetricFunction R,
      ∀ r μ, e (r ⊗ₜ[ℤ] monomial ℤ μ) = r • monomial R μ := by
  obtain ⟨bZ, hbZ, _⟩ := exists_monomialBasis ℤ
  obtain ⟨bR, hbR, _⟩ := exists_monomialBasis R
  let c : SymmetricFunction ℤ →ₐ[ℤ] SymmetricFunction R :=
    mapAlgHom (Algebra.ofId ℤ R)
  have hc (μ : YoungDiagram) : c (monomial ℤ μ) = monomial R μ :=
    map_monomial (Algebra.ofId ℤ R).toRingHom μ
  let ψ : R ⊗[ℤ] SymmetricFunction ℤ →ₐ[R] SymmetricFunction R :=
    AlgHom.liftEquiv ℤ R (SymmetricFunction ℤ) (SymmetricFunction R) c
  let bT := bZ.baseChange R
  let L := bT.equiv bR (Equiv.refl YoungDiagram)
  have hψ : ψ.toLinearMap = L.toLinearMap := by
    apply bT.ext
    intro μ
    change ψ (bT μ) = L (bT μ)
    rw [Module.Basis.equiv_apply]
    change ψ (bZ.baseChange R μ) = bR μ
    rw [Module.Basis.baseChange_apply, hbZ, hbR]
    change (AlgHom.liftEquiv ℤ R (SymmetricFunction ℤ) (SymmetricFunction R) c)
      (1 ⊗ₜ[ℤ] monomial ℤ μ) = monomial R μ
    rw [AlgHom.liftEquiv_tmul, hc, one_smul]
  have hbij : Function.Bijective ψ := by
    change Function.Bijective ψ.toLinearMap
    rw [hψ]
    exact L.bijective
  refine ⟨AlgEquiv.ofBijective ψ hbij, ?_⟩
  intro r μ
  rw [AlgEquiv.ofBijective_apply]
  change (AlgHom.liftEquiv ℤ R (SymmetricFunction ℤ) (SymmetricFunction R) c)
    (r ⊗ₜ[ℤ] monomial ℤ μ) = r • monomial R μ
  rw [AlgHom.liftEquiv_tmul, hc]

/-- The algebra equivalence from tensor scalar extension to symmetric functions over `R`. -/
def baseChangeEquiv (R : Type*) [CommRing R] :
    R ⊗[ℤ] SymmetricFunction ℤ ≃ₐ[R] SymmetricFunction R :=
  (exists_baseChangeEquiv R).choose

/-- Pure tensors of monomial functions map to scalar multiples of the same monomials. -/
theorem baseChangeEquiv_tmul_monomial (R : Type*) [CommRing R] (r : R) (μ : YoungDiagram) :
    baseChangeEquiv R (r ⊗ₜ[ℤ] monomial ℤ μ) = r • monomial R μ :=
  (exists_baseChangeEquiv R).choose_spec r μ

/-- Scalar extension on a pure tensor is scalar multiplication after the integer coefficient map. -/
theorem baseChangeEquiv_tmul (R : Type*) [CommRing R] (r : R)
    (f : SymmetricFunction ℤ) :
    baseChangeEquiv R (r ⊗ₜ[ℤ] f) = r • map (algebraMap ℤ R) f := by
  obtain ⟨bZ, hbZ, _⟩ := exists_monomialBasis ℤ
  let c : SymmetricFunction ℤ →ₐ[ℤ] SymmetricFunction R :=
    mapAlgHom (Algebra.ofId ℤ R)
  let ψ : R ⊗[ℤ] SymmetricFunction ℤ →ₐ[R] SymmetricFunction R :=
    AlgHom.liftEquiv ℤ R (SymmetricFunction ℤ) (SymmetricFunction R) c
  have heq : (baseChangeEquiv R).toLinearMap = ψ.toLinearMap := by
    apply (bZ.baseChange R).ext
    intro μ
    change baseChangeEquiv R (bZ.baseChange R μ) = ψ (bZ.baseChange R μ)
    rw [Module.Basis.baseChange_apply, hbZ, baseChangeEquiv_tmul_monomial]
    change (1 : R) • monomial R μ =
      (AlgHom.liftEquiv ℤ R (SymmetricFunction ℤ) (SymmetricFunction R) c)
        (1 ⊗ₜ[ℤ] monomial ℤ μ)
    rw [AlgHom.liftEquiv_tmul]
    exact congrArg (fun g => (1 : R) • g)
      (map_monomial (Algebra.ofId ℤ R).toRingHom μ).symm
  have h := DFunLike.congr_fun heq (r ⊗ₜ[ℤ] f)
  change baseChangeEquiv R (r ⊗ₜ[ℤ] f) = ψ (r ⊗ₜ[ℤ] f) at h
  rw [h]
  exact AlgHom.liftEquiv_tmul c r f

/-- The inverse scalar-extension equivalence sends a monomial to its unit pure tensor. -/
theorem baseChangeEquiv_symm_monomial (R : Type*) [CommRing R] (μ : YoungDiagram) :
    (baseChangeEquiv R).symm (monomial R μ) = 1 ⊗ₜ[ℤ] monomial ℤ μ := by
  apply (baseChangeEquiv R).injective
  rw [AlgEquiv.apply_symm_apply, baseChangeEquiv_tmul_monomial, one_smul]

/-- The scalar-extension map is the natural tensor lift of the integer coefficient map. -/
theorem baseChangeEquiv_toAlgHom (R : Type*) [CommRing R] :
    (baseChangeEquiv R).toAlgHom =
      AlgHom.liftEquiv ℤ R (SymmetricFunction ℤ) (SymmetricFunction R)
        (mapAlgHom (Algebra.ofId ℤ R)) := by
  apply AlgHom.toLinearMap_injective
  apply ((monomialBasis ℤ).baseChange R).ext
  intro μ
  change baseChangeEquiv R ((monomialBasis ℤ).baseChange R μ) = _
  rw [Module.Basis.baseChange_apply, monomialBasis_apply, baseChangeEquiv_tmul]
  exact (AlgHom.liftEquiv_tmul (mapAlgHom (Algebra.ofId ℤ R)) 1 (monomial ℤ μ)).symm

/-- The tensor lift characterizes scalar extension on arbitrary tensor expressions. -/
theorem baseChangeEquiv_apply (R : Type*) [CommRing R]
    (x : R ⊗[ℤ] SymmetricFunction ℤ) :
    baseChangeEquiv R x =
      AlgHom.liftEquiv ℤ R (SymmetricFunction ℤ) (SymmetricFunction R)
        (mapAlgHom (Algebra.ofId ℤ R)) x :=
  DFunLike.congr_fun (baseChangeEquiv_toAlgHom R) x

end SymmetricFunction
