import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Data.Finsupp.Weight

/-! # Bounded symmetric power series

The algebra of symmetric functions is the subalgebra of symmetric power series with bounded
total degree in countably many variables.

## Main definitions

* `SymmetricFunction` is the algebra of symmetric series of bounded degree.
* `SymmetricFunction.toPowerSeries` is the canonical ambient inclusion.

## Main results

* `SymmetricFunction.toPowerSeries` is the injective algebra inclusion.
* `SymmetricFunction.boundedSymmetricSubalgebra` defines bounded symmetric series.

## Implementation notes

The conventional variable `x_i`, with positive index `i`, is the ambient variable `X (i - 1)`.
The carrier is the subtype of a subalgebra of power series in countably many variables; its algebra
and semiring structures are inherited from that subalgebra. A commutative coefficient ring
therefore also gives the inherited commutative ring structure.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, §2.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommSemiring R]

/-- A power series has degree at most `d` if all coefficients above degree `d` vanish. -/
def HasDegreeBound (f : MvPowerSeries ℕ R) (d : ℕ) : Prop :=
  ∀ n : ℕ →₀ ℕ, d < n.degree → MvPowerSeries.coeff n f = 0

/-- A power series has bounded degree if some natural number bounds its total degree. -/
def HasBoundedDegree (f : MvPowerSeries ℕ R) : Prop :=
  ∃ d : ℕ, HasDegreeBound f d

/-- A power series is symmetric if every permutation of its variables fixes it. -/
def IsSymmetricSeries (f : MvPowerSeries ℕ R) : Prop :=
  ∀ e : Equiv.Perm ℕ, MvPowerSeries.renameEquiv R e f = f

/-- A degree bound remains valid when increased. -/
theorem HasDegreeBound.mono {f : MvPowerSeries ℕ R} {d k : ℕ}
    (hf : HasDegreeBound f d) (hdk : d ≤ k) : HasDegreeBound f k :=
  fun n hn => hf n (lt_of_le_of_lt hdk hn)

/-- The zero series satisfies every degree bound. -/
theorem HasDegreeBound.zero (d : ℕ) : HasDegreeBound (0 : MvPowerSeries ℕ R) d := by
  intro n _
  exact map_zero _

/-- A sum has degree bounded by the larger of the two bounds. -/
theorem HasDegreeBound.add {f g : MvPowerSeries ℕ R} {d k : ℕ}
    (hf : HasDegreeBound f d) (hg : HasDegreeBound g k) :
    HasDegreeBound (f + g) (max d k) := by
  intro n hn
  rw [map_add, hf n (lt_of_le_of_lt (le_max_left _ _) hn),
    hg n (lt_of_le_of_lt (le_max_right _ _) hn), zero_add]

/-- Degree bounds add under multiplication. -/
theorem HasDegreeBound.mul {f g : MvPowerSeries ℕ R} {d k : ℕ}
    (hf : HasDegreeBound f d) (hg : HasDegreeBound g k) :
    HasDegreeBound (f * g) (d + k) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  have hdeg : p.1.degree + p.2.degree = n.degree := by
    rw [← map_add, hsum]
  by_cases hleft : d < p.1.degree
  · rw [hf p.1 hleft, zero_mul]
  · have hright : k < p.2.degree := by omega
    rw [hg p.2 hright, mul_zero]

/-- Negation preserves a degree bound. -/
theorem HasDegreeBound.neg {R : Type*} [CommRing R] {f : MvPowerSeries ℕ R} {d : ℕ}
    (hf : HasDegreeBound f d) : HasDegreeBound (-f) d := by
  intro n hn
  rw [map_neg, hf n hn, neg_zero]

/-- Scalar multiplication preserves a degree bound. -/
theorem HasDegreeBound.smul {f : MvPowerSeries ℕ R} {d : ℕ}
    (hf : HasDegreeBound f d) (r : R) : HasDegreeBound (r • f) d := by
  intro n hn
  rw [map_smul, hf n hn, smul_zero]

/-- A constant series has degree bounded by zero. -/
theorem hasDegreeBound_C (r : R) : HasDegreeBound (MvPowerSeries.C r) 0 := by
  intro n hn
  apply MvPowerSeries.coeff_C_of_ne_zero
  intro hzero
  subst n
  simp at hn

/-- A sum of symmetric series is symmetric. -/
theorem IsSymmetricSeries.add {f g : MvPowerSeries ℕ R}
    (hf : IsSymmetricSeries f) (hg : IsSymmetricSeries g) : IsSymmetricSeries (f + g) := by
  intro e
  rw [map_add, hf e, hg e]

/-- A product of symmetric series is symmetric. -/
theorem IsSymmetricSeries.mul {f g : MvPowerSeries ℕ R}
    (hf : IsSymmetricSeries f) (hg : IsSymmetricSeries g) : IsSymmetricSeries (f * g) := by
  intro e
  rw [map_mul, hf e, hg e]

/-- Negation preserves symmetry. -/
theorem IsSymmetricSeries.neg {R : Type*} [CommRing R] {f : MvPowerSeries ℕ R}
    (hf : IsSymmetricSeries f) : IsSymmetricSeries (-f) := by
  intro e
  rw [map_neg, hf e]

/-- Scalar multiplication preserves symmetry. -/
theorem IsSymmetricSeries.smul {f : MvPowerSeries ℕ R}
    (hf : IsSymmetricSeries f) (r : R) : IsSymmetricSeries (r • f) := by
  intro e
  rw [map_smul, hf e]

/-- A constant series is symmetric. -/
theorem isSymmetricSeries_C (r : R) : IsSymmetricSeries (MvPowerSeries.C r) := by
  intro e
  exact MvPowerSeries.rename_C e r

/-- The subalgebra of symmetric power series of bounded total degree. -/
def boundedSymmetricSubalgebra (R : Type*) [CommSemiring R] :
    Subalgebra R (MvPowerSeries ℕ R) where
  carrier := {f | IsSymmetricSeries f ∧ HasBoundedDegree f}
  algebraMap_mem' r := ⟨isSymmetricSeries_C r, 0, hasDegreeBound_C r⟩
  add_mem' := by
    rintro f g ⟨hf, d, hd⟩ ⟨hg, k, hk⟩
    exact ⟨hf.add hg, max d k, hd.add hk⟩
  mul_mem' := by
    rintro f g ⟨hf, d, hd⟩ ⟨hg, k, hk⟩
    exact ⟨hf.mul hg, d + k, hd.mul hk⟩

end SymmetricFunction

/-- A symmetric function over `R` is a bounded symmetric power series
in countably many variables. -/
abbrev SymmetricFunction (R : Type*) [CommSemiring R] : Type _ :=
  ↥(SymmetricFunction.boundedSymmetricSubalgebra R)

namespace SymmetricFunction

variable {R : Type*} [CommSemiring R]

/-- The canonical inclusion of symmetric functions into power series. -/
def toPowerSeries (R : Type*) [CommSemiring R] :
    SymmetricFunction R →ₐ[R] MvPowerSeries ℕ R :=
  (boundedSymmetricSubalgebra R).val

/-- The inclusion into power series is injective. -/
theorem toPowerSeries_injective : Function.Injective (toPowerSeries R) :=
  Subtype.val_injective

/-- The inclusion forgets the boundedness and symmetry certificates. -/
@[simp]
theorem toPowerSeries_apply (f : SymmetricFunction R) : toPowerSeries R f = f.val := rfl

/-- Every symmetric function has a symmetric ambient series. -/
theorem isSymmetricSeries (f : SymmetricFunction R) :
    IsSymmetricSeries (toPowerSeries R f) := f.property.1

/-- Every symmetric function has a finite degree bound. -/
theorem hasBoundedDegree (f : SymmetricFunction R) :
    HasBoundedDegree (toPowerSeries R f) := f.property.2

end SymmetricFunction
