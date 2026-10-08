import Schubert.SymmetricFunctions.Families.Monomial
import Schubert.SymmetricFunctions.Transfer
import Schubert.SymmetricFunctions.ForMathlib.AlternantRegularity
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric

/-!
# Schur symmetric functions

The Kostka expansion defines a Schur function as a finite sum of monomial functions.

## Main results

* `restrict_schur`: restriction gives the finite Schur polynomial.
* `coeff_schur_of_degree_eq`: coefficients of the correct degree are Kostka numbers.
* `restrict_schur_mul_alternant`: the division-free bialternant identity.
-/

noncomputable section

namespace SymmetricFunction

/-- The Schur symmetric function of a Young diagram, defined by its Kostka expansion. -/
def schur (R : Type*) [CommSemiring R] (μ : YoungDiagram) : SymmetricFunction R :=
  ∑ ν : μ.card.Partition, (TauCeti.kostkaNumber (TauCeti.shapePartition μ) ν : R) •
    monomial R (TauCeti.diagramOf ν)

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

private theorem exponentDiagram_eq_weight {n : ℕ} (d : ℕ →₀ ℕ) (hd : d.degree = n) :
    exponentDiagram d = TauCeti.diagramOf (TauCeti.weightPartition d hd) := by
  subst n
  rfl

open scoped Classical in
/-- The coefficients of a Schur function are its finite Kostka expansion. -/
theorem coeff_schur (μ : YoungDiagram) (d : ℕ →₀ ℕ) :
    coeff R d (schur R μ) =
      ∑ ν : μ.card.Partition, (TauCeti.kostkaNumber (TauCeti.shapePartition μ) ν : R) *
        (if exponentDiagram d = TauCeti.diagramOf ν then 1 else 0) := by
  classical
  simp only [schur, map_sum, coeff_smul, coeff_monomial, smul_eq_mul]

/-- A Schur coefficient of the diagram's degree is the corresponding Kostka number. -/
theorem coeff_schur_of_degree_eq (μ : YoungDiagram) (d : ℕ →₀ ℕ)
    (hd : d.degree = μ.card) :
    coeff R d (schur R μ) =
      (TauCeti.kostkaNumber (TauCeti.shapePartition μ) (TauCeti.weightPartition d hd) : R) := by
  classical
  rw [coeff_schur, exponentDiagram_eq_weight d hd]
  simp only [TauCeti.diagramOf_injective.eq_iff, mul_ite, mul_one, mul_zero]
  simp

/-- Schur coefficients vanish outside the size of the diagram. -/
theorem coeff_schur_eq_zero (μ : YoungDiagram) (d : ℕ →₀ ℕ)
    (hd : d.degree ≠ μ.card) : coeff R d (schur R μ) = 0 := by
  classical
  rw [coeff_schur]
  apply Finset.sum_eq_zero
  intro ν _
  rw [ite_eq_right, mul_zero]
  intro h
  apply hd
  simpa only [card_exponentDiagram, TauCeti.card_diagramOf] using
    congrArg YoungDiagram.card h

/-- A Schur symmetric function is homogeneous of the size of its diagram. -/
theorem isHomogeneous_schur (μ : YoungDiagram) : IsHomogeneous (schur R μ) μ.card := by
  rw [isHomogeneous_iff_component]
  apply ext
  intro d
  rw [coeff_homogeneousComponent]
  by_cases hd : d.degree = μ.card
  · rw [ite_eq_left hd]
  · rw [ite_eq_right hd, coeff_schur_eq_zero μ d hd]

/-- A Schur symmetric function has degree bounded by the size of its diagram. -/
theorem schur_mem_degreeFiltration (μ : YoungDiagram) :
    schur R μ ∈ degreeFiltration R μ.card := by
  exact IsHomogeneous.mem_degreeFiltration (@isHomogeneous_schur R _ μ)

/-- Coefficient-ring homomorphisms preserve Schur functions. -/
theorem map_schur (φ : R →+* S) (μ : YoungDiagram) : map φ (schur R μ) = schur S μ := by
  classical
  apply ext
  intro d
  rw [coeff_map, coeff_schur, coeff_schur]
  simp only [map_sum, map_mul, map_natCast, apply_ite, map_one, map_zero]

/-- A sized-partition monomial restricts to the finite monomial of that partition. -/
theorem restrict_monomial_diagramOf (n : ℕ) {k : ℕ} (ν : k.Partition) :
    restrict R n (monomial R (TauCeti.diagramOf ν)) = MvPolynomial.msymm (Fin n) R ν := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_restrict, coeff_monomial]
  by_cases hd : d.degree = k
  · rw [TauCeti.coeff_msymm R ν hd, exponentDiagram_embDomain _ _ hd]
    simp only [TauCeti.diagramOf_injective.eq_iff]
  · rw [TauCeti.coeff_msymm_eq_zero_of_degree_ne R ν hd]
    apply ite_eq_right
    intro h
    apply hd
    simpa only [card_exponentDiagram, TauCeti.card_diagramOf,
      Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain] using
      congrArg YoungDiagram.card h

/-- Restriction of a Schur function gives its finite-alphabet Schur polynomial. -/
theorem restrict_schur (n : ℕ) (μ : YoungDiagram) :
    restrict R n (schur R μ) = TauCeti.schurPoly (Fin n) R (TauCeti.shapePartition μ) := by
  rw [schur, map_sum, TauCeti.schurPoly_eq_sum_kostkaNumber_smul_msymm]
  apply Finset.sum_congr rfl
  intro ν _
  rw [map_smul, restrict_monomial_diagramOf]

/-- Restriction gives the diagram-indexed finite Schur polynomial without a height bound. -/
theorem restrict_schur_eq_diagramSchurPoly (n : ℕ) (μ : YoungDiagram) :
    restrict R n (schur R μ) = TauCeti.diagramSchurPoly n R μ := by
  rw [restrict_schur, TauCeti.schurPoly_eq_rename, TauCeti.diagramOf_shapePartition]
  have hcast {a b : ℕ} (h : a = b) :
      MvPolynomial.rename (finCongr h) (TauCeti.diagramSchurPoly a R μ) =
        TauCeti.diagramSchurPoly b R μ := by
    subst b
    simp
  let c := finCongr (Fintype.card_fin n)
  let e := Fintype.equivFin (Fin n)
  calc
    MvPolynomial.rename e.symm (TauCeti.diagramSchurPoly _ R μ) =
        MvPolynomial.rename c
          (MvPolynomial.rename (c.trans e).symm (TauCeti.diagramSchurPoly _ R μ)) := by
      rw [MvPolynomial.rename_rename]
      congr 1
    _ = MvPolynomial.rename c (TauCeti.diagramSchurPoly _ R μ) := by
      rw [TauCeti.isSymmetric_diagramSchurPoly]
    _ = TauCeti.diagramSchurPoly n R μ := hcast (Fintype.card_fin n)

/-- Restriction agrees with the finite Schur polynomial of a sized partition. -/
theorem restrict_schur_diagramOf (n : ℕ) {k : ℕ} (ν : k.Partition) :
    restrict R n (schur R (TauCeti.diagramOf ν)) = TauCeti.schurPoly (Fin n) R ν := by
  rw [restrict_schur]
  simp only [TauCeti.schurPoly, TauCeti.diagramOf_shapePartition]

/-- The Schur function of the empty diagram is the multiplicative identity. -/
theorem schur_bot : schur R ⊥ = 1 := by
  apply ext_restrict
  intro n
  rw [restrict_schur, map_one]
  exact TauCeti.schurPoly_partition_zero _

/-- Finite restriction satisfies the height-bounded, division-free bialternant formula. -/
theorem restrict_schur_mul_alternant {R : Type*} [CommRing R]
    (n : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n) :
    restrict R n (schur R μ) * TauCeti.alternant (Fin n) R (fun j => n - 1 - j) =
      TauCeti.alternant (Fin n) R (fun j => μ.betaNumber n j) := by
  rw [restrict_schur_eq_diagramSchurPoly]
  exact TauCeti.diagramSchurPoly_mul_alternant n μ hμ

/-- Height-bounded bialternant identities characterize the Schur symmetric function. -/
theorem schur_eq_of_restrict_alternant {R : Type*} [CommRing R]
    (μ : YoungDiagram) (f : SymmetricFunction R)
    (h : ∀ n : ℕ, μ.colLen 0 ≤ n →
      restrict R n f * TauCeti.alternant (Fin n) R (fun j => n - 1 - j) =
        TauCeti.alternant (Fin n) R (fun j => μ.betaNumber n j)) :
    f = schur R μ := by
  have hres (n : ℕ) (hn : μ.colLen 0 ≤ n) : restrict R n f = restrict R n (schur R μ) := by
    have hr := FiniteAlphabet.isRegular_alternant_staircase R n
    exact hr.right ((h n hn).trans (restrict_schur_mul_alternant n μ hn).symm)
  apply ext_restrict
  intro n
  rw [← killCompl_restrict (le_max_left n (μ.colLen 0)) f,
    ← killCompl_restrict (le_max_left n (μ.colLen 0)) (schur R μ),
    hres (max n (μ.colLen 0)) (le_max_right n (μ.colLen 0))]

/-- Finite restriction satisfies the height-bounded, division-free bialternant formula. -/
theorem restrict_schur_mul_alternant_rename {R : Type*} [CommRing R]
    (n : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n) :
    restrict R n (schur R μ) *
        MvPolynomial.rename (Fintype.equivFin (Fin n)).symm
          (TauCeti.alternant (Fin (Fintype.card (Fin n))) R
            (fun j => Fintype.card (Fin n) - 1 - j)) =
      MvPolynomial.rename (Fintype.equivFin (Fin n)).symm
        (TauCeti.alternant (Fin (Fintype.card (Fin n))) R
          (fun j => μ.betaNumber (Fintype.card (Fin n)) j)) := by
  rw [restrict_schur]
  simpa only [TauCeti.diagramOf_shapePartition] using
    TauCeti.schurPoly_mul_alternant (R := R) (TauCeti.shapePartition μ)
      (by simpa only [TauCeti.diagramOf_shapePartition, Fintype.card_fin] using hμ)

/-- Height-bounded bialternant identities characterize the Schur symmetric function. -/
theorem schur_eq_of_restrict_alternant_rename {R : Type*} [CommRing R]
    (μ : YoungDiagram) (f : SymmetricFunction R)
    (h : ∀ n : ℕ, μ.colLen 0 ≤ n →
      restrict R n f *
          MvPolynomial.rename (Fintype.equivFin (Fin n)).symm
            (TauCeti.alternant (Fin (Fintype.card (Fin n))) R
              (fun j => Fintype.card (Fin n) - 1 - j)) =
        MvPolynomial.rename (Fintype.equivFin (Fin n)).symm
          (TauCeti.alternant (Fin (Fintype.card (Fin n))) R
            (fun j => μ.betaNumber (Fintype.card (Fin n)) j))) :
    f = schur R μ := by
  have hres (n : ℕ) (hn : μ.colLen 0 ≤ n) : restrict R n f = restrict R n (schur R μ) := by
    have hr := (MvPolynomial.renameEquiv R (Fintype.equivFin (Fin n)).symm).isRegular_apply
      (SymmetricFunction.FiniteAlphabet.isRegular_alternant_staircase R (Fintype.card (Fin n)))
    exact hr.right ((h n hn).trans (restrict_schur_mul_alternant_rename n μ hn).symm)
  apply ext_restrict
  intro n
  rw [← killCompl_restrict (le_max_left n (μ.colLen 0)) f,
    ← killCompl_restrict (le_max_left n (μ.colLen 0)) (schur R μ),
    hres (max n (μ.colLen 0)) (le_max_right n (μ.colLen 0))]

end SymmetricFunction
