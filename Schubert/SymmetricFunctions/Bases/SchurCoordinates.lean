import Schubert.SymmetricFunctions.Bases.SchurBasis

/-!
# Homogeneous projections in Schur coordinates

Homogeneous projection keeps exactly the Schur coordinates of the selected diagram size.

## Main results

* `schur_repr_homogeneousComponent` gives the coordinate projection formula.
* `schur_repr_eq_zero_of_degreeBound` vanishes above a filtration bound.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommRing R]

/-- Homogeneous projection selects Schur coordinates with the prescribed diagram size. -/
theorem schur_repr_homogeneousComponent (d : ℕ) (f : SymmetricFunction R)
    (μ : YoungDiagram) :
    (schurBasis R).repr (homogeneousComponent R d f) μ =
      if μ.card = d then (schurBasis R).repr f μ else 0 := by
  classical
  have hmap : ((schurBasis R).coord μ).comp (homogeneousComponent R d) =
      if μ.card = d then (schurBasis R).coord μ else 0 := by
    apply (schurBasis R).ext
    intro ν
    have hc : (schurBasis R).coord μ (schur R ν) = if ν = μ then 1 else 0 := by
      rw [Module.Basis.coord_apply, ← schurBasis_apply, Module.Basis.repr_self_apply]
    simp only [LinearMap.comp_apply, schurBasis_apply,
      homogeneousComponent_of_isHomogeneous (isHomogeneous_schur (R := R) ν),
      apply_ite, map_zero, hc]
    by_cases hν : ν = μ
    · subst ν
      split_ifs <;> simp_all
    · split_ifs <;> simp_all
  have he := LinearMap.congr_fun hmap f
  by_cases hd : μ.card = d
  · simpa only [hd, ite_true, LinearMap.comp_apply, Module.Basis.coord_apply] using he
  · simpa only [hd, ite_false, LinearMap.comp_apply, Module.Basis.coord_apply,
      LinearMap.zero_apply] using he

/-- Coordinates above a total-degree bound vanish. -/
theorem schur_repr_eq_zero_of_degreeBound {d : ℕ} {f : SymmetricFunction R}
    (hf : f ∈ degreeFiltration R d) (μ : YoungDiagram) (hμ : d < μ.card) :
    (schurBasis R).repr f μ = 0 := by
  have he := schur_repr_homogeneousComponent μ.card f μ
  rw [homogeneousComponent_eq_zero hf hμ, map_zero, Finsupp.zero_apply,
    ite_eq_left rfl] at he
  exact he.symm

/-- Schur coordinates commute with a homomorphism of coefficient rings. -/
theorem schurBasis_repr_map {S : Type*} [CommRing S] (φ : R →+* S)
    (f : SymmetricFunction R) :
    (schurBasis S).repr (map φ f) = ((schurBasis R).repr f).mapRange φ φ.map_zero := by
  classical
  have h := (schurBasis R).linearCombination_repr f
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at h
  apply_fun map φ at h
  simp only [map_sum] at h
  have hm (μ : YoungDiagram) (r : R) :
      map φ (r • schurBasis R μ) = φ r • schurBasis S μ := by
    rw [Algebra.smul_def, map_mul, map_algebraMap, schurBasis_apply, map_schur,
      schurBasis_apply, Algebra.smul_def]
  simp_rw [hm] at h
  rw [← h, map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single]
  ext μ
  simp only [Finsupp.mapRange_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν _ hν
    simp only [hν, ite_false]
  · intro hμ
    simp only [Finsupp.notMem_support_iff.mp hμ, map_zero, zero_smul, ite_true]

end SymmetricFunction
