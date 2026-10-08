import Schubert.SymmetricFunctions.Grading

/-! # Finite homogeneous decomposition

A symmetric function is the sum of its finitely many homogeneous components.
Homogeneity is preserved by the module operations, and degree bounds are additive
under multiplication.

## Main results

* `SymmetricFunction.sum_homogeneousComponent` reconstructs a degree-bounded function.
* `SymmetricFunction.homogeneousComponent_component` gives the component projections.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommSemiring R]

/-- The zero function is homogeneous in every degree. -/
theorem IsHomogeneous.zero (d : ℕ) : IsHomogeneous (0 : SymmetricFunction R) d := by
  rw [isHomogeneous_iff_component, map_zero]

/-- A sum of functions of the same degree is homogeneous of that degree. -/
theorem IsHomogeneous.add {f g : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) (hg : IsHomogeneous g d) : IsHomogeneous (f + g) d := by
  rw [isHomogeneous_iff_component] at hf hg ⊢
  rw [map_add, hf, hg]

/-- Negation preserves homogeneous degree. -/
theorem IsHomogeneous.neg {R : Type*} [CommRing R] {f : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) : IsHomogeneous (-f) d := by
  rw [isHomogeneous_iff_component] at hf ⊢
  rw [map_neg, hf]

/-- Scalar multiplication preserves homogeneous degree. -/
theorem IsHomogeneous.smul {f : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) (r : R) : IsHomogeneous (r • f) d := by
  rw [isHomogeneous_iff_component] at hf ⊢
  rw [map_smul, hf]

/-- The multiplicative identity is homogeneous of degree zero. -/
theorem IsHomogeneous.one : IsHomogeneous (1 : SymmetricFunction R) 0 := by
  rw [isHomogeneous_iff_coeff]
  intro n hn
  rw [coeff_one, ite_eq_right]
  intro h
  subst n
  exact hn rfl

/-- Coefficients embedded as constants are homogeneous of degree zero. -/
theorem isHomogeneous_algebraMap (r : R) :
    IsHomogeneous (algebraMap R (SymmetricFunction R) r) 0 := by
  rw [isHomogeneous_iff_coeff]
  intro n hn
  rw [coeff_algebraMap, ite_eq_right]
  intro h
  subst n
  exact hn rfl

/-- A finite sum of functions of a fixed degree has that degree. -/
theorem IsHomogeneous.sum {ι : Type*} (s : Finset ι) (f : ι → SymmetricFunction R)
    (d : ℕ) (hf : ∀ i ∈ s, IsHomogeneous (f i) d) :
    IsHomogeneous (∑ i ∈ s, f i) d := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact IsHomogeneous.zero d
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact IsHomogeneous.add (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Degrees add under finite products of homogeneous functions. -/
theorem IsHomogeneous.prod {ι : Type*} (s : Finset ι) (f : ι → SymmetricFunction R)
    (d : ι → ℕ) (hf : ∀ i ∈ s, IsHomogeneous (f i) (d i)) :
    IsHomogeneous (∏ i ∈ s, f i) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact IsHomogeneous.one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact IsHomogeneous.mul (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Degrees add under products indexed by a list, retaining repeated factors. -/
theorem IsHomogeneous.list_prod {ι : Type*} (l : List ι)
    (f : ι → SymmetricFunction R) (w : ι → ℕ)
    (hf : ∀ i ∈ l, IsHomogeneous (f i) (w i)) :
    IsHomogeneous ((l.map f).prod) ((l.map w).sum) := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, List.map_nil, List.sum_nil]
    exact IsHomogeneous.one
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons]
    exact IsHomogeneous.mul (hf i List.mem_cons_self)
      (ih (fun j hj => hf j (List.mem_cons_of_mem i hj)))

/-- Taking a power multiplies the homogeneous degree by its exponent. -/
theorem IsHomogeneous.pow {f : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) (n : ℕ) : IsHomogeneous (f ^ n) (n * d) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_mul]
    exact IsHomogeneous.one
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact IsHomogeneous.mul ih hf

/-- The homogeneous submodule of degree `d`. -/
def homogeneousSubmodule (R : Type*) [CommSemiring R] (d : ℕ) :
    Submodule R (SymmetricFunction R) := (homogeneousComponent R d).range

/-- Membership in a homogeneous submodule means homogeneity of that degree. -/
theorem mem_homogeneousSubmodule (d : ℕ) (f : SymmetricFunction R) :
    f ∈ homogeneousSubmodule R d ↔ IsHomogeneous f d := by
  constructor
  · rintro ⟨g, rfl⟩
    exact isHomogeneous_homogeneousComponent g d
  · intro hf
    exact ⟨f, isHomogeneous_iff_component.mp hf⟩

/-- A homogeneous function belongs to the filtration of its degree. -/
theorem IsHomogeneous.mem_degreeFiltration {f : SymmetricFunction R} {d : ℕ}
    (hf : IsHomogeneous f d) : f ∈ degreeFiltration R d := by
  intro n hn
  exact hf.coeff_eq_zero (Nat.ne_of_gt hn)

/-- Filtration degrees add under multiplication. -/
theorem mul_mem_degreeFiltration {f g : SymmetricFunction R} {d k : ℕ}
    (hf : f ∈ degreeFiltration R d) (hg : g ∈ degreeFiltration R k) :
    f * g ∈ degreeFiltration R (d + k) :=
  hf.mul hg

/-- Projection of a homogeneous function is itself or zero. -/
theorem homogeneousComponent_of_isHomogeneous {f : SymmetricFunction R} {k : ℕ}
    (hf : IsHomogeneous f k) (d : ℕ) :
    homogeneousComponent R d f = if d = k then f else 0 := by
  by_cases hdk : d = k
  · subst d
    simpa only [ite_true] using isHomogeneous_iff_component.mp hf
  · apply ext
    intro n
    rw [ite_eq_right hdk, coeff_zero, coeff_homogeneousComponent]
    split_ifs with hn
    · exact hf.coeff_eq_zero (hn ▸ hdk)
    · rfl

/-- Successive projections agree in equal degrees and vanish otherwise. -/
theorem homogeneousComponent_component (d k : ℕ) (f : SymmetricFunction R) :
    homogeneousComponent R d (homogeneousComponent R k f) =
      if d = k then homogeneousComponent R k f else 0 :=
  homogeneousComponent_of_isHomogeneous (isHomogeneous_homogeneousComponent f k) d

/-- A function of degree at most `d` is the sum of its components of degrees zero through `d`. -/
theorem sum_homogeneousComponent {f : SymmetricFunction R} {d : ℕ}
    (hf : f ∈ degreeFiltration R d) :
    ∑ i ∈ Finset.range (d + 1), homogeneousComponent R i f = f := by
  apply ext
  intro n
  simp only [map_sum, coeff_homogeneousComponent]
  by_cases hn : n.degree ≤ d
  · have hmem : n.degree ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single n.degree]
    · simp only [ite_true]
    · intro i _ hi
      simp only [Ne.symm hi, ite_false]
    · intro hnot
      exact (hnot hmem).elim
  · have hz : coeff R n f = 0 := hf n (Nat.lt_of_not_le hn)
    rw [hz]
    apply Finset.sum_eq_zero
    intro i hi
    have hni : n.degree ≠ i := by
      have := Finset.mem_range.mp hi
      omega
    simp only [hni, ite_false]

end SymmetricFunction
