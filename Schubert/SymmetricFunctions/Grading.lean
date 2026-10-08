import Schubert.SymmetricFunctions.Coefficients
import Mathlib.RingTheory.MvPowerSeries.Order

/-! # Homogeneous components and degree bounds

The homogeneous components of a symmetric function are symmetric functions. Coefficient
vanishing defines the degree filtration.

## Main results

* `SymmetricFunction.homogeneousComponent` extracts a single degree.
* `SymmetricFunction.mem_degreeFiltration_iff` characterizes degree bounds by coefficients.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommSemiring R]

/-- Every homogeneous component of a symmetric series is symmetric. -/
theorem IsSymmetricSeries.homogeneousComponent {f : MvPowerSeries ℕ R}
    (hf : IsSymmetricSeries f) (d : ℕ) :
    IsSymmetricSeries (MvPowerSeries.homogeneousComponent d f) := by
  classical
  intro e
  apply MvPowerSeries.ext
  intro n
  obtain ⟨m, rfl⟩ := Finsupp.mapDomain_surjective e.surjective n
  have hcoeff : MvPowerSeries.coeff (m.mapDomain e) f = MvPowerSeries.coeff m f := by
    have h := MvPowerSeries.coeff_embDomain_rename e.toEmbedding f m
    change MvPowerSeries.coeff (Finsupp.embDomain e.toEmbedding m)
      (MvPowerSeries.renameEquiv R e f) = MvPowerSeries.coeff m f at h
    rw [hf e, Finsupp.embDomain_eq_mapDomain] at h
    exact h
  change MvPowerSeries.coeff (m.mapDomain e)
    (MvPowerSeries.rename e (MvPowerSeries.homogeneousComponent d f)) = _
  have h := MvPowerSeries.coeff_embDomain_rename e.toEmbedding
    (MvPowerSeries.homogeneousComponent d f) m
  rw [Finsupp.embDomain_eq_mapDomain] at h
  change MvPowerSeries.coeff (m.mapDomain e)
    (MvPowerSeries.rename e (MvPowerSeries.homogeneousComponent d f)) =
      MvPowerSeries.coeff m (MvPowerSeries.homogeneousComponent d f) at h
  rw [h]
  rw [MvPowerSeries.coeff_homogeneousComponent, MvPowerSeries.coeff_homogeneousComponent]
  simp only [Finsupp.degree_mapDomain, hcoeff]

/-- A homogeneous component has degree bounded by its index. -/
theorem hasDegreeBound_homogeneousComponent (f : MvPowerSeries ℕ R) (d : ℕ) :
    HasDegreeBound (MvPowerSeries.homogeneousComponent d f) d := by
  intro n hn
  rw [MvPowerSeries.coeff_homogeneousComponent, ite_eq_right (Nat.ne_of_gt hn)]

/-- The degree-`d` homogeneous component of a symmetric function. -/
def homogeneousComponent (R : Type*) [CommSemiring R] (d : ℕ) :
    SymmetricFunction R →ₗ[R] SymmetricFunction R where
  toFun f := ⟨MvPowerSeries.homogeneousComponent d f.val,
    f.isSymmetricSeries.homogeneousComponent d,
    d, hasDegreeBound_homogeneousComponent f.val d⟩
  map_add' f g := Subtype.ext (map_add _ f.val g.val)
  map_smul' r f := Subtype.ext (map_smul _ r f.val)

/-- Homogeneous projection keeps exactly the coefficients of its degree. -/
@[simp]
theorem coeff_homogeneousComponent (d : ℕ) (n : ℕ →₀ ℕ) (f : SymmetricFunction R) :
    coeff R n (homogeneousComponent R d f) = if n.degree = d then coeff R n f else 0 :=
  MvPowerSeries.coeff_homogeneousComponent d n f.val

/-- A symmetric function is homogeneous of degree `d` if all other coefficients vanish. -/
def IsHomogeneous (f : SymmetricFunction R) (d : ℕ) : Prop :=
  MvPowerSeries.IsHomogeneous (toPowerSeries R f) d

/-- The degree projection is homogeneous in its index. -/
theorem isHomogeneous_homogeneousComponent (f : SymmetricFunction R) (d : ℕ) :
    IsHomogeneous (homogeneousComponent R d f) d :=
  MvPowerSeries.isHomogeneous_homogeneousComponent f.val d

/-- A homogeneous function has zero coefficients outside its degree. -/
theorem IsHomogeneous.coeff_eq_zero {f : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) {n : ℕ →₀ ℕ} (hn : n.degree ≠ d) : coeff R n f = 0 :=
  MvPowerSeries.IsHomogeneous.coeff_eq_zero hf hn

/-- Homogeneous degrees add under multiplication. -/
theorem IsHomogeneous.mul {f g : SymmetricFunction R} {d k : ℕ}
    (hf : IsHomogeneous f d) (hg : IsHomogeneous g k) : IsHomogeneous (f * g) (d + k) :=
  MvPowerSeries.IsHomogeneous.mul hf hg

/-- A function is homogeneous exactly when its degree projection fixes it. -/
theorem isHomogeneous_iff_component {f : SymmetricFunction R} {d : ℕ} :
    IsHomogeneous f d ↔ homogeneousComponent R d f = f := by
  change MvPowerSeries.IsHomogeneous f.val d ↔ _
  rw [MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent]
  exact ⟨fun h => Subtype.ext h.symm, fun h => (congrArg Subtype.val h).symm⟩

/-- The submodule of symmetric functions of total degree at most `d`. -/
def degreeFiltration (R : Type*) [CommSemiring R] (d : ℕ) : Submodule R (SymmetricFunction R) where
  carrier := {f | HasDegreeBound f.val d}
  zero_mem' := HasDegreeBound.zero d
  add_mem' hf hg := by
    change HasDegreeBound (_ + _) d
    simpa only [max_self] using hf.add hg
  smul_mem' r _ hf := hf.smul r

/-- Filtration membership agrees with the ambient degree bound. -/
@[simp]
theorem mem_degreeFiltration (d : ℕ) (f : SymmetricFunction R) :
    f ∈ degreeFiltration R d ↔ HasDegreeBound (toPowerSeries R f) d := Iff.rfl

/-- Membership in the degree filtration is characterized by coefficient vanishing. -/
theorem mem_degreeFiltration_iff (d : ℕ) (f : SymmetricFunction R) :
    f ∈ degreeFiltration R d ↔ ∀ n : ℕ →₀ ℕ, d < n.degree → coeff R n f = 0 := Iff.rfl

/-- Every symmetric function belongs to some term of the degree filtration. -/
theorem exists_mem_degreeFiltration (f : SymmetricFunction R) :
    ∃ d : ℕ, f ∈ degreeFiltration R d := f.hasBoundedDegree

/-- Homogeneity is characterized by coefficient vanishing outside a single degree. -/
theorem isHomogeneous_iff_coeff {f : SymmetricFunction R} {d : ℕ} :
    IsHomogeneous f d ↔ ∀ n : ℕ →₀ ℕ, n.degree ≠ d → coeff R n f = 0 := by
  constructor
  · intro hf n hn
    exact hf.coeff_eq_zero hn
  · intro hf n hn
    change Finsupp.weight (fun _ : ℕ => 1) n = d
    rw [← Finsupp.degree_eq_weight_one]
    by_contra h
    exact hn (hf n h)

/-- The degree filtration is increasing. -/
theorem degreeFiltration_mono {d k : ℕ} (hdk : d ≤ k) :
    degreeFiltration R d ≤ degreeFiltration R k := fun _ hf => hf.mono hdk

/-- The degree projection belongs to the filtration of its degree. -/
theorem homogeneousComponent_mem (f : SymmetricFunction R) (d : ℕ) :
    homogeneousComponent R d f ∈ degreeFiltration R d :=
  hasDegreeBound_homogeneousComponent f.val d

/-- A projection above a filtration bound is zero. -/
theorem homogeneousComponent_eq_zero {f : SymmetricFunction R} {d k : ℕ}
    (hf : f ∈ degreeFiltration R d) (hdk : d < k) : homogeneousComponent R k f = 0 := by
  apply ext
  intro n
  rw [coeff_homogeneousComponent, coeff_zero]
  split_ifs with hn
  · exact hf n (hn ▸ hdk)
  · rfl

end SymmetricFunction
