import Schubert.SymmetricFunctions.HomogeneousRestriction
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # Existence of the Schur basis

Finite homogeneous Schur bases lift through restriction. The homogeneous decomposition then
combines them into a basis of the stable symmetric-function ring.

## Main results

* `SymmetricFunction.exists_schurBasis` supplies a standard basis with Schur-function vectors.
* `SymmetricFunction.schurBasis_apply` identifies the vectors of the chosen Schur basis.
-/

noncomputable section

namespace SymmetricFunction

/-- Schur functions form a basis indexed by Young diagrams over every commutative ring. -/
theorem exists_schurBasis (R : Type*) [CommRing R] :
    ∃ b : Module.Basis YoungDiagram R (SymmetricFunction R),
      ∀ μ, b μ = schur R μ := by
  classical
  let E (d : ℕ) := homogeneousRestrictEquiv R d d le_rfl
  have hE (d : ℕ) (f : (homogeneousComponent R d).range) :
      (E d f : MvPolynomial (Fin d) R) = restrict R d f.val :=
    coe_homogeneousRestrictEquiv d d le_rfl f
  let b (d : ℕ) : Module.Basis (Nat.Partition d) R (homogeneousComponent R d).range :=
    ((TauCeti.schurPolyBasis (Fin d) R d).reindex
      (TauCeti.partitionEquivSchurIndex d d le_rfl).symm).map (E d).symm
  have hb (d : ℕ) (ν : d.Partition) : (b d ν).val = schur R (TauCeti.diagramOf ν) := by
    have hν : IsHomogeneous (schur R (TauCeti.diagramOf ν)) d := by
      apply isHomogeneous_iff_component.mpr
      simpa only [TauCeti.card_diagramOf] using
        (isHomogeneous_iff_component.mp (@isHomogeneous_schur R _ (TauCeti.diagramOf ν)))
    apply restrict_inj_of_degreeBound
      (IsHomogeneous.mem_degreeFiltration
        ((mem_range_homogeneousComponent d (b d ν).val).mp (b d ν).property))
      (IsHomogeneous.mem_degreeFiltration hν)
    rw [← hE d (b d ν), restrict_schur_diagramOf]
    have he : E d (b d ν) = TauCeti.schurPolyBasis (Fin d) R d
        (TauCeti.partitionEquivSchurIndex d d le_rfl ν) := by
      simp only [b, Module.Basis.map_apply, Module.Basis.reindex_apply,
        Equiv.symm_symm, LinearEquiv.apply_symm_apply]
    rw [he, TauCeti.coe_schurPolyBasis, TauCeti.partitionEquivSchurIndex_apply]
  let S := homogeneousSumEquiv R
  have hS (d : ℕ) (f : (homogeneousComponent R d).range) :
      S (DFinsupp.single d f) = f.val := homogeneousSumEquiv_single d f
  let B := DFinsupp.basis b
  have hB (d : ℕ) (ν : d.Partition) : B ⟨d, ν⟩ = DFinsupp.single d (b d ν) := by
    apply B.repr.injective
    rw [Module.Basis.repr_self]
    change Finsupp.single ⟨d, ν⟩ 1 =
      (sigmaFinsuppLequivDFinsupp R).symm
        (DFinsupp.mapRange.linearEquiv (fun k => (b k).repr) (DFinsupp.single d (b d ν)))
    apply (sigmaFinsuppLequivDFinsupp R).injective
    rw [LinearEquiv.apply_symm_apply]
    change sigmaFinsuppEquivDFinsupp (Finsupp.single ⟨d, ν⟩ (1 : R)) =
      DFinsupp.mapRange (fun k => (b k).repr) (fun k => map_zero (b k).repr)
        (DFinsupp.single d (b d ν))
    simp only [sigmaFinsuppEquivDFinsupp_single,
      DFinsupp.mapRange_single, Module.Basis.repr_self]
  let indexEquiv : (Σ d : ℕ, Nat.Partition d) ≃ YoungDiagram :=
    (Equiv.sigmaCongrRight (fun d => TauCeti.partitionEquivYoungDiagram d)).trans
      (Equiv.sigmaFiberEquiv YoungDiagram.card)
  refine ⟨(B.map S).reindex indexEquiv, ?_⟩
  intro μ
  obtain ⟨⟨d, ν⟩, rfl⟩ := indexEquiv.surjective μ
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.map_apply, hB, hS]
  change (b d ν).val = schur R (TauCeti.diagramOf ν)
  exact hb d ν

/-- The Schur basis of the stable symmetric-function ring. -/
def schurBasis (R : Type*) [CommRing R] : Module.Basis YoungDiagram R (SymmetricFunction R) :=
  (exists_schurBasis R).choose

/-- The vector indexed by a diagram is its Schur symmetric function. -/
@[simp]
theorem schurBasis_apply {R : Type*} [CommRing R] (μ : YoungDiagram) :
    schurBasis R μ = schur R μ := (exists_schurBasis R).choose_spec μ

end SymmetricFunction
