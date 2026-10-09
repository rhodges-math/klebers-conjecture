import KlebersConjecture.SymmetricFunctions.Families.Exponents
import KlebersConjecture.SymmetricFunctions.Components
import KlebersConjecture.SymmetricFunctions.Restriction
import KlebersConjecture.SymmetricFunctions.Map

/-! # Monomial symmetric functions

A monomial symmetric function has coefficient one on the exponent vectors of its shape
and zero on the other exponent vectors.

## Main results

* `coeff_monomial` gives the indicator coefficient formula.
* `restrict_monomial` identifies finite-alphabet restriction.
* `map_monomial` commutes with coefficient maps.
-/

noncomputable section

namespace SymmetricFunction

open scoped Classical in
/-- The monomial symmetric function indexed by a Young diagram. -/
def monomial (R : Type*) [CommSemiring R] (μ : YoungDiagram) : SymmetricFunction R :=
  ⟨fun d => if exponentDiagram d = μ then 1 else 0, by
    constructor
    · intro e
      apply MvPowerSeries.ext
      intro d
      obtain ⟨c, rfl⟩ := Finsupp.mapDomain_surjective e.surjective d
      have h := MvPowerSeries.coeff_embDomain_rename e.toEmbedding
        (fun d => if exponentDiagram d = μ then (1 : R) else 0) c
      rw [Finsupp.embDomain_eq_mapDomain] at h
      change MvPowerSeries.coeff (c.mapDomain e)
        (MvPowerSeries.rename e (fun d => if exponentDiagram d = μ then (1 : R) else 0)) =
          MvPowerSeries.coeff c (fun d => if exponentDiagram d = μ then (1 : R) else 0) at h
      change MvPowerSeries.coeff (c.mapDomain e)
        (MvPowerSeries.rename e (fun d => if exponentDiagram d = μ then (1 : R) else 0)) = _
      rw [h]
      change (if exponentDiagram c = μ then (1 : R) else 0) =
        (if exponentDiagram (c.mapDomain e) = μ then 1 else 0)
      rw [exponentDiagram_mapDomain]
    · refine ⟨μ.card, ?_⟩
      intro d hd
      change (if exponentDiagram d = μ then (1 : R) else 0) = 0
      apply ite_eq_right
      intro h
      have hc := congrArg YoungDiagram.card h
      rw [card_exponentDiagram] at hc
      omega⟩

variable {R : Type*} [CommSemiring R]

open scoped Classical in
/-- The coefficients of a monomial symmetric function are the indicator of its exponent shape. -/
@[simp]
theorem coeff_monomial (μ : YoungDiagram) (d : ℕ →₀ ℕ) :
    coeff R d (monomial R μ) = if exponentDiagram d = μ then 1 else 0 := rfl

open scoped Classical in
/-- Canonical row exponents distinguish the monomial symmetric functions. -/
theorem coeff_monomial_rowExponent (μ ν : YoungDiagram) :
    coeff R (rowExponent ν) (monomial R μ) = if ν = μ then 1 else 0 := by
  rw [coeff_monomial, exponentDiagram_rowExponent]

/-- The monomial symmetric function of the empty diagram is one. -/
@[simp]
theorem monomial_bot : monomial R ⊥ = 1 := by
  classical
  apply ext
  intro d
  rw [coeff_monomial, coeff_one]
  simp only [exponentDiagram_eq_bot_iff]

/-- A monomial symmetric function is homogeneous of the size of its diagram. -/
theorem isHomogeneous_monomial (μ : YoungDiagram) : IsHomogeneous (monomial R μ) μ.card := by
  classical
  change MvPowerSeries.IsHomogeneous _ _
  rw [MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent]
  apply MvPowerSeries.ext
  intro d
  rw [MvPowerSeries.coeff_homogeneousComponent]
  change (if exponentDiagram d = μ then (1 : R) else 0) =
    if d.degree = μ.card then (if exponentDiagram d = μ then 1 else 0) else 0
  by_cases hshape : exponentDiagram d = μ
  · have hdegree := congrArg YoungDiagram.card hshape
    rw [card_exponentDiagram] at hdegree
    simp only [hshape, hdegree, ite_true]
  · simp only [hshape, ite_false, ite_self]

/-- A monomial symmetric function belongs to the degree bound given by its size. -/
theorem monomial_mem_degreeFiltration (μ : YoungDiagram) :
    monomial R μ ∈ degreeFiltration R μ.card := by
  exact IsHomogeneous.mem_degreeFiltration (@isHomogeneous_monomial R _ μ)

/-- Symmetry equates coefficients on exponent vectors with equal diagrams. -/
theorem coeff_eq_of_exponentDiagram {d e : ℕ →₀ ℕ}
    (h : exponentDiagram d = exponentDiagram e) (f : SymmetricFunction R) :
    coeff R d f = coeff R e f := by
  obtain ⟨q, rfl⟩ := (exponentDiagram_eq_iff_perm d e).mp h
  have hc := MvPowerSeries.coeff_embDomain_rename q.toEmbedding f.val d
  change MvPowerSeries.coeff (Finsupp.embDomain q.toEmbedding d)
    (MvPowerSeries.renameEquiv R q (toPowerSeries R f)) = _ at hc
  rw [f.isSymmetricSeries q, Finsupp.embDomain_eq_mapDomain] at hc
  exact hc.symm

/-- Every coefficient is the coefficient at the canonical exponent of its diagram. -/
theorem coeff_eq_rowExponent (d : ℕ →₀ ℕ) (f : SymmetricFunction R) :
    coeff R d f = coeff R (rowExponent (exponentDiagram d)) f :=
  coeff_eq_of_exponentDiagram (exponentDiagram_rowExponent _).symm f

/-- Restriction gives the finite-alphabet monomial symmetric polynomial of the same shape. -/
theorem restrict_monomial (n : ℕ) (μ : YoungDiagram) :
    restrict R n (monomial R μ) = MvPolynomial.msymm (Fin n) R (TauCeti.shapePartition μ) := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_restrict, coeff_monomial]
  by_cases hd : d.degree = μ.card
  · rw [TauCeti.coeff_msymm R _ hd, exponentDiagram_embDomain _ _ hd]
    have hshape : TauCeti.diagramOf (TauCeti.weightPartition d hd) = μ ↔
        TauCeti.weightPartition d hd = TauCeti.shapePartition μ := by
      constructor
      · intro h
        apply TauCeti.diagramOf_injective
        exact h.trans (TauCeti.diagramOf_shapePartition μ).symm
      · intro h
        exact (congrArg TauCeti.diagramOf h).trans (TauCeti.diagramOf_shapePartition μ)
    simp only [hshape]
  · rw [TauCeti.coeff_msymm_eq_zero_of_degree_ne R _ hd]
    apply ite_eq_right
    intro hshape
    apply hd
    have hc := congrArg YoungDiagram.card hshape
    simpa only [card_exponentDiagram, Finsupp.embDomain_eq_mapDomain,
      Finsupp.degree_mapDomain] using hc

end SymmetricFunction

/-! # Monomial functions under scalar extension

Maps of coefficient rings preserve monomial symmetric functions and their coordinates.
-/

noncomputable section

namespace SymmetricFunction

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- A coefficient-ring homomorphism sends a monomial symmetric function to the same shape. -/
theorem map_monomial (φ : R →+* S) (μ : YoungDiagram) :
    map φ (monomial R μ) = monomial S μ := by
  classical
  apply ext
  intro n
  rw [coeff_map, coeff_monomial, coeff_monomial]
  by_cases hn : exponentDiagram n = μ
  · simp only [hn, ite_true, map_one]
  · simp only [hn, ite_false, map_zero]

end SymmetricFunction
