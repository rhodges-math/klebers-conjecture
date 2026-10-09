import KlebersConjecture.SymmetricFunctions.Grading

/-! # Maps of coefficient rings

A homomorphism of coefficient semirings acts coefficientwise on symmetric functions.
It preserves homogeneous components and degree bounds, and is injective whenever
the coefficient homomorphism is injective.

## Main results

* `SymmetricFunction.map` is the induced ring homomorphism.
* `SymmetricFunction.coeff_map` gives its coefficients.
* `SymmetricFunction.map_injective` transfers injectivity.
-/

noncomputable section

namespace SymmetricFunction

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

/-- Mapping coefficients preserves a degree bound. -/
theorem HasDegreeBound.map {f : MvPowerSeries ℕ R} {d : ℕ}
    (hf : HasDegreeBound f d) (φ : R →+* S) :
    HasDegreeBound (MvPowerSeries.map φ f) d := by
  intro n hn
  rw [MvPowerSeries.coeff_map, hf n hn, map_zero]

/-- Mapping coefficients preserves symmetry. -/
theorem IsSymmetricSeries.map {f : MvPowerSeries ℕ R}
    (hf : IsSymmetricSeries f) (φ : R →+* S) :
    IsSymmetricSeries (MvPowerSeries.map φ f) := by
  intro e
  change MvPowerSeries.rename e (MvPowerSeries.map φ f) = MvPowerSeries.map φ f
  rw [MvPowerSeries.rename_map]
  exact congrArg (MvPowerSeries.map φ) (hf e)

/-- Apply a coefficient homomorphism to every coefficient of a symmetric function. -/
def map (φ : R →+* S) : SymmetricFunction R →+* SymmetricFunction S :=
  ((MvPowerSeries.map φ).comp (toPowerSeries R).toRingHom).codRestrict
    (boundedSymmetricSubalgebra S) (by
      intro f
      obtain ⟨d, hd⟩ := exists_mem_degreeFiltration f
      exact ⟨f.isSymmetricSeries.map φ, d, hd.map φ⟩)

/-- The power-series inclusion commutes with coefficient maps. -/
theorem toPowerSeries_map (φ : R →+* S) (f : SymmetricFunction R) :
    toPowerSeries S (map φ f) = MvPowerSeries.map φ (toPowerSeries R f) := rfl

/-- Mapping coefficients applies the coefficient homomorphism to each coefficient. -/
@[simp]
theorem coeff_map (φ : R →+* S) (n : ℕ →₀ ℕ) (f : SymmetricFunction R) :
    coeff S n (map φ f) = φ (coeff R n f) := rfl

/-- The identity coefficient homomorphism induces the identity map. -/
@[simp]
theorem map_id : map (RingHom.id R) = RingHom.id (SymmetricFunction R) := by
  apply RingHom.ext
  intro f
  exact ext (fun _ => rfl)

/-- Mapping coefficients respects composition of homomorphisms. -/
theorem map_comp (φ : R →+* S) (ψ : S →+* T) :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  apply RingHom.ext
  intro f
  exact ext (fun _ => rfl)

/-- Successive coefficient maps equal their composite map. -/
@[simp]
theorem map_map (φ : R →+* S) (ψ : S →+* T) (f : SymmetricFunction R) :
    map ψ (map φ f) = map (ψ.comp φ) f := by
  exact ext (fun _ => rfl)

/-- A coefficient map preserves embedded scalars. -/
theorem map_algebraMap (φ : R →+* S) (r : R) :
    map φ (algebraMap R (SymmetricFunction R) r) =
      algebraMap S (SymmetricFunction S) (φ r) := by
  apply ext
  intro n
  rw [coeff_map, coeff_algebraMap, coeff_algebraMap]
  by_cases hn : n = 0
  · simp only [hn, ite_true]
  · simp only [hn, ite_false, map_zero]

/-- An injective map of coefficient semirings induces an injective map of symmetric functions. -/
theorem map_injective (φ : R →+* S) (hφ : Function.Injective φ) :
    Function.Injective (map φ) := by
  intro f g hfg
  apply ext
  intro n
  apply hφ
  simpa only [coeff_map] using congrArg (coeff S n) hfg

/-- Coefficient maps commute with homogeneous projection. -/
theorem map_homogeneousComponent (φ : R →+* S) (d : ℕ) (f : SymmetricFunction R) :
    map φ (homogeneousComponent R d f) = homogeneousComponent S d (map φ f) := by
  apply ext
  intro n
  rw [coeff_map, coeff_homogeneousComponent, coeff_homogeneousComponent, coeff_map]
  by_cases hn : n.degree = d
  · simp only [hn, ite_true]
  · simp only [hn, ite_false, map_zero]

/-- Mapping coefficients preserves homogeneous degree. -/
theorem IsHomogeneous.map {f : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) (φ : R →+* S) : IsHomogeneous (map φ f) d := by
  rw [isHomogeneous_iff_component] at hf ⊢
  rw [← map_homogeneousComponent, hf]

/-- Coefficient maps preserve the degree filtration. -/
theorem map_mem_degreeFiltration (φ : R →+* S) {f : SymmetricFunction R} {d : ℕ}
    (hf : f ∈ degreeFiltration R d) : map φ f ∈ degreeFiltration S d :=
  hf.map φ

section Algebra

variable [Algebra R S] [Algebra R T]

/-- An algebra homomorphism of coefficient semirings induces an algebra homomorphism
of symmetric-function algebras. -/
def mapAlgHom (φ : S →ₐ[R] T) : SymmetricFunction S →ₐ[R] SymmetricFunction T where
  __ := map φ.toRingHom
  commutes' r := by
    change map φ.toRingHom (algebraMap R (SymmetricFunction S) r) =
      algebraMap R (SymmetricFunction T) r
    rw [IsScalarTower.algebraMap_apply R S (SymmetricFunction S), map_algebraMap]
    change algebraMap T (SymmetricFunction T) (φ (algebraMap R S r)) =
      algebraMap R (SymmetricFunction T) r
    rw [φ.commutes, ← IsScalarTower.algebraMap_apply R T (SymmetricFunction T)]

/-- The induced algebra homomorphism acts by the coefficient map. -/
theorem mapAlgHom_apply (φ : S →ₐ[R] T) (f : SymmetricFunction S) :
    mapAlgHom φ f = map φ.toRingHom f := rfl

end Algebra

end SymmetricFunction
