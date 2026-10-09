import KlebersConjecture.SymmetricFunctions.Map
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Logic.Equiv.Fintype

/-! # Restriction to finitely many variables

Setting all variables outside the first `n` to zero sends a symmetric function to a
symmetric polynomial. Coefficients characterize this restriction independently of degree bounds.

## Main results

* `SymmetricFunction.coeff_restrict` characterizes restriction.
* `SymmetricFunction.restrict_map` commutes with coefficient maps.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommSemiring R]

/-- The embedding of the first `n` variable indices into the natural numbers. -/
def variableEmbedding (n : ℕ) : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩

/-- The initial-alphabet embedding sends an index to its natural value. -/
@[simp]
theorem variableEmbedding_apply (n : ℕ) (i : Fin n) : variableEmbedding n i = i.val := rfl

private theorem exists_restrictedPolynomial (n : ℕ) (f : SymmetricFunction R) :
    ∃ p : MvPolynomial (Fin n) R,
      (p : MvPowerSeries (Fin n) R) = MvPowerSeries.killCompl (variableEmbedding n) f.val := by
  obtain ⟨d, hd⟩ := exists_mem_degreeFiltration f
  refine ⟨MvPowerSeries.truncTotal (d + 1)
    (MvPowerSeries.killCompl (variableEmbedding n) f.val), ?_⟩
  apply MvPowerSeries.ext
  intro m
  rw [MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal_eq_ite]
  split_ifs with hm
  · rfl
  · rw [MvPowerSeries.coeff_killCompl]
    symm
    apply hd
    rw [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]
    omega

/-- The polynomial obtained by retaining the first `n` variables of a symmetric function. -/
private def restrictedPolynomial (n : ℕ) (f : SymmetricFunction R) : MvPolynomial (Fin n) R :=
  (exists_restrictedPolynomial n f).choose

private theorem coe_restrictedPolynomial (n : ℕ) (f : SymmetricFunction R) :
    (restrictedPolynomial n f : MvPowerSeries (Fin n) R) =
      MvPowerSeries.killCompl (variableEmbedding n) f.val :=
  (exists_restrictedPolynomial n f).choose_spec

/-- Restriction to the first `n` variables, with all remaining variables set to zero. -/
def restrict (R : Type*) [CommSemiring R] (n : ℕ) :
    SymmetricFunction R →ₐ[R] MvPolynomial (Fin n) R where
  toFun := restrictedPolynomial n
  map_one' := by
    apply MvPolynomial.coe_injective
    rw [coe_restrictedPolynomial, MvPolynomial.coe_one]
    exact map_one _
  map_mul' f g := by
    apply MvPolynomial.coe_injective
    rw [MvPolynomial.coe_mul, coe_restrictedPolynomial, coe_restrictedPolynomial,
      coe_restrictedPolynomial]
    exact map_mul _ f.val g.val
  map_zero' := by
    apply MvPolynomial.coe_injective
    rw [coe_restrictedPolynomial, MvPolynomial.coe_zero]
    exact map_zero _
  map_add' f g := by
    apply MvPolynomial.coe_injective
    rw [MvPolynomial.coe_add, coe_restrictedPolynomial, coe_restrictedPolynomial,
      coe_restrictedPolynomial]
    exact map_add _ f.val g.val
  commutes' r := by
    apply MvPolynomial.coe_injective
    rw [coe_restrictedPolynomial]
    change MvPowerSeries.killCompl (variableEmbedding n) (MvPowerSeries.C r) =
      ((MvPolynomial.C r : MvPolynomial (Fin n) R) : MvPowerSeries (Fin n) R)
    rw [MvPolynomial.coe_C]
    exact MvPowerSeries.killCompl_C r

/-- Polynomial restriction equals setting the remaining power-series variables to zero. -/
theorem coe_restrict (n : ℕ) (f : SymmetricFunction R) :
    (restrict R n f : MvPowerSeries (Fin n) R) =
      MvPowerSeries.killCompl (variableEmbedding n) (toPowerSeries R f) :=
  coe_restrictedPolynomial n f

/-- Restriction retains precisely the coefficients whose variable indices lie below `n`. -/
theorem coeff_restrict (n : ℕ) (m : Fin n →₀ ℕ) (f : SymmetricFunction R) :
    (restrict R n f).coeff m = coeff R (Finsupp.embDomain (variableEmbedding n) m) f := by
  rw [← MvPolynomial.coeff_coe, coe_restrict, MvPowerSeries.coeff_killCompl]
  rfl

/-- Every degree cutoff beyond a bound gives the same restricted polynomial. -/
theorem restrict_eq_truncTotal {d n : ℕ} (f : SymmetricFunction R)
    (hf : f ∈ degreeFiltration R d) :
    restrict R n f = MvPowerSeries.truncTotal (d + 1)
      (MvPowerSeries.killCompl (variableEmbedding n) (toPowerSeries R f)) := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_restrict, MvPowerSeries.coeff_truncTotal_eq_ite]
  split_ifs with hm
  · rw [MvPowerSeries.coeff_killCompl]
    rfl
  · apply hf
    rw [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]
    omega

/-- Finite-alphabet restriction preserves an upper bound on total degree. -/
theorem totalDegree_restrict_le {d n : ℕ} (f : SymmetricFunction R)
    (hf : f ∈ degreeFiltration R d) : (restrict R n f).totalDegree ≤ d := by
  rw [restrict_eq_truncTotal f hf]
  exact Nat.lt_succ_iff.mp (MvPowerSeries.totalDegree_truncTotal_lt _ (Nat.succ_ne_zero d))

/-- Finite-alphabet restriction is a symmetric polynomial. -/
theorem isSymmetric_restrict (n : ℕ) (f : SymmetricFunction R) :
    MvPolynomial.IsSymmetric (restrict R n f) := by
  classical
  intro e
  apply MvPolynomial.ext
  intro m
  obtain ⟨k, rfl⟩ := Finsupp.mapDomain_surjective e.surjective m
  rw [MvPolynomial.coeff_rename_mapDomain e e.injective, coeff_restrict, coeff_restrict]
  let extension := e.viaFintypeEmbedding (variableEmbedding n)
  have hext : (Finsupp.embDomain (variableEmbedding n) k).mapDomain extension =
      Finsupp.embDomain (variableEmbedding n) (k.mapDomain e) := by
    simp only [Finsupp.embDomain_eq_mapDomain]
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    apply congrArg (fun g : Fin n → ℕ => k.mapDomain g)
    funext i
    exact Equiv.Perm.viaFintypeEmbedding_apply_image e (variableEmbedding n) i
  have h := MvPowerSeries.coeff_embDomain_rename extension.toEmbedding f.val
    (Finsupp.embDomain (variableEmbedding n) k)
  change MvPowerSeries.coeff _
    (MvPowerSeries.renameEquiv R extension (toPowerSeries R f)) = _ at h
  rw [f.isSymmetricSeries extension, Finsupp.embDomain_eq_mapDomain] at h
  change MvPowerSeries.coeff
    ((Finsupp.embDomain (variableEmbedding n) k).mapDomain extension) f.val = _ at h
  rw [hext] at h
  exact h.symm

/-- Restriction to a smaller alphabet commutes with restriction from a larger alphabet. -/
theorem killCompl_restrict {m n : ℕ} (h : m ≤ n) (f : SymmetricFunction R) :
    MvPolynomial.killCompl (Fin.castLEEmb h).injective (restrict R n f) = restrict R m f := by
  apply MvPolynomial.ext
  intro k
  rw [MvPolynomial.coeff_killCompl, coeff_restrict, coeff_restrict]
  simp only [Finsupp.embDomain_eq_mapDomain]
  rw [← Finsupp.mapDomain_comp]
  rfl

/-- Coefficient maps commute with finite-alphabet restriction. -/
theorem restrict_map {S : Type*} [CommSemiring S] (φ : R →+* S)
    (n : ℕ) (f : SymmetricFunction R) :
    restrict S n (map φ f) = MvPolynomial.map φ (restrict R n f) := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_restrict, coeff_map, MvPolynomial.coeff_map, coeff_restrict]

/-- Restriction with codomain the algebra of finite symmetric polynomials. -/
def restrictSymmetric (R : Type*) [CommSemiring R] (n : ℕ) :
    SymmetricFunction R →ₐ[R] MvPolynomial.symmetricSubalgebra (Fin n) R :=
  (restrict R n).codRestrict (MvPolynomial.symmetricSubalgebra (Fin n) R)
    (fun f => (MvPolynomial.mem_symmetricSubalgebra _).mpr (isSymmetric_restrict n f))

/-- Forgetting symmetry recovers the polynomial restriction. -/
@[simp]
theorem coe_restrictSymmetric (n : ℕ) (f : SymmetricFunction R) :
    (restrictSymmetric R n f : MvPolynomial (Fin n) R) = restrict R n f := rfl

end SymmetricFunction
