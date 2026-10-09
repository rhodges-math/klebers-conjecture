import KlebersConjecture.SymmetricFunctions.SymplecticCharacters.Basic
import KlebersConjecture.SymmetricFunctions.JacobiTrudi.JacobiTrudi
import KlebersConjecture.SymmetricFunctions.Components
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The filtration of symplectic universal characters

The uncorrected determinant is the Schur function. Every surviving correction lowers
the total degree by twice a positive column index.

## Main results

* `symplecticCharacter_mem_degreeFiltration`: the character has degree at most the diagram size.
* `symplecticCharacter_sub_schur_mem`: the correction has strictly smaller degree.
* `homogeneousComponent_symplecticCharacter`: the top component is the Schur function.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommRing R]

private theorem homogeneous_prod_complete {ι : Type*} (s : Finset ι) (k : ι → ℤ)
    (hk : ∀ i ∈ s, 0 ≤ k i) :
    IsHomogeneous (∏ i ∈ s, complete R (k i)) (∑ i ∈ s, k i).toNat := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h : IsHomogeneous (complete R (0 : ℕ)) 0 :=
      isHomogeneous_complete_nat (R := R) 0
    change IsHomogeneous (complete R 0) 0 at h
    rw [complete_zero] at h
    simp only [Finset.prod_empty, Finset.sum_empty, Int.toNat_zero]
    exact @h
  | @insert a s ha ih =>
    have hka := hk a (Finset.mem_insert_self _ _)
    have hks : ∀ i ∈ s, 0 ≤ k i := fun i hi => hk i (Finset.mem_insert_of_mem hi)
    have hs : 0 ≤ ∑ i ∈ s, k i := Finset.sum_nonneg hks
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Int.toNat_add hka hs]
    apply IsHomogeneous.mul
    · have h : IsHomogeneous (complete R ((k a).toNat : ℤ)) (k a).toNat :=
        isHomogeneous_complete_nat (R := R) (k a).toNat
      rw [Int.toNat_of_nonneg hka] at h
      exact @h
    · exact ih hks

private theorem prod_complete_mem {ι : Type*} (s : Finset ι) (k : ι → ℤ) (d : ℕ)
    (hd : (∑ i ∈ s, k i) ≤ (d : ℤ)) :
    (∏ i ∈ s, complete R (k i)) ∈ degreeFiltration R d := by
  classical
  by_cases hk : ∀ i ∈ s, 0 ≤ k i
  · apply degreeFiltration_mono (show (∑ i ∈ s, k i).toNat ≤ d by omega)
    exact IsHomogeneous.mem_degreeFiltration (homogeneous_prod_complete s k hk)
  · push Not at hk
    obtain ⟨i, hi, hki⟩ := hk
    have hz : (∏ i ∈ s, complete R (k i)) = 0 :=
      Finset.prod_eq_zero hi (complete_neg _ hki)
    rw [hz]
    exact Submodule.zero_mem _

/-- The integer complete index of an uncorrected permutation entry. -/
private def mainIndex (μ : YoungDiagram) (σ : Equiv.Perm (Fin (μ.colLen 0)))
    (j : Fin (μ.colLen 0)) : ℤ :=
  (μ.rowLen (σ j).val : ℤ) - (σ j).val + j.val

/-- Choose the correction in the indicated columns. -/
private def selectedIndex (μ : YoungDiagram) (σ : Equiv.Perm (Fin (μ.colLen 0)))
    (s : Finset (Fin (μ.colLen 0))) (j : Fin (μ.colLen 0)) : ℤ :=
  mainIndex μ σ j - if j ∈ s then 2 * (j.val : ℤ) else 0

/-- The selected product of correction and main determinant entries. -/
private def selectedTerm (R : Type*) [CommRing R] (μ : YoungDiagram)
    (σ : Equiv.Perm (Fin (μ.colLen 0))) (s : Finset (Fin (μ.colLen 0))) :
    SymmetricFunction R :=
  ∏ j : Fin (μ.colLen 0), if j ∈ s then
    (if j.val = 0 then 0 else
      complete R ((μ.rowLen (σ j).val : ℤ) - (σ j).val - j.val))
    else complete R (mainIndex μ σ j)

private theorem sum_mainIndex (μ : YoungDiagram) (σ : Equiv.Perm (Fin (μ.colLen 0))) :
    (∑ j : Fin (μ.colLen 0), mainIndex μ σ j) = (μ.card : ℤ) := by
  simp only [mainIndex, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Equiv.sum_comp σ (fun i => (μ.rowLen i.val : ℤ)),
    Equiv.sum_comp σ (fun i => (i.val : ℤ)), sub_add_cancel]
  rw [YoungDiagram.card_eq_sum_range_rowLen μ le_rfl,
    ← Fin.sum_univ_eq_sum_range (fun i => μ.rowLen i) (μ.colLen 0)]
  simp only [Nat.cast_sum]

private theorem sum_selectedIndex (μ : YoungDiagram)
    (σ : Equiv.Perm (Fin (μ.colLen 0))) (s : Finset (Fin (μ.colLen 0))) :
    (∑ j : Fin (μ.colLen 0), selectedIndex μ σ s j) =
      (μ.card : ℤ) - 2 * ∑ j ∈ s, (j.val : ℤ) := by
  simp only [selectedIndex, Finset.sum_sub_distrib, sum_mainIndex,
    Finset.sum_ite_mem_eq, Finset.mul_sum]

private theorem selectedTerm_mem (μ : YoungDiagram)
    (σ : Equiv.Perm (Fin (μ.colLen 0))) (s : Finset (Fin (μ.colLen 0)))
    (hs : s ≠ ∅) : selectedTerm R μ σ s ∈ degreeFiltration R (μ.card - 1) := by
  classical
  by_cases hz : ∃ j ∈ s, j.val = 0
  · obtain ⟨j, hj, hj0⟩ := hz
    have he : selectedTerm R μ σ s = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp only [ite_eq_left hj, ite_eq_left hj0]
    rw [he]
    exact Submodule.zero_mem _
  · have he : selectedTerm R μ σ s =
        ∏ j : Fin (μ.colLen 0), complete R (selectedIndex μ σ s j) := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j ∈ s
      · have hj0 : j.val ≠ 0 := fun h => hz ⟨j, hj, h⟩
        simp only [selectedIndex, ite_eq_left hj, ite_eq_right hj0]
        congr 1
        unfold mainIndex
        ring
      · simp only [selectedIndex, ite_eq_right hj, sub_zero]
    rw [he]
    apply prod_complete_mem
    rw [sum_selectedIndex]
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hj0 : j.val ≠ 0 := fun h => hz ⟨j, hj, h⟩
    have hsum : (j.val : ℤ) ≤ ∑ k ∈ s, (k.val : ℤ) :=
      Finset.single_le_sum (fun k _ => Int.natCast_nonneg k.val) hj
    have hpos : 0 < (j.val : ℤ) := by exact_mod_cast (Nat.pos_of_ne_zero hj0)
    omega

private theorem selectedTerm_split (μ : YoungDiagram)
    (σ : Equiv.Perm (Fin (μ.colLen 0))) (s : Finset (Fin (μ.colLen 0))) :
    selectedTerm R μ σ s =
      (∏ j ∈ s, if j.val = 0 then 0 else
        complete R ((μ.rowLen (σ j).val : ℤ) - (σ j).val - j.val)) *
      ∏ j ∈ sᶜ, complete R (mainIndex μ σ j) := by
  classical
  unfold selectedTerm
  rw [Finset.prod_ite]
  congr 1
  · congr 1
    ext j
    simp
  · congr 1
    ext j
    simp

private theorem permutation_correction (μ : YoungDiagram)
    (σ : Equiv.Perm (Fin (μ.colLen 0))) :
    (∏ j, symplecticCharacterMatrix R μ (μ.colLen 0) (σ j) j) -
        (∏ j, complete R (mainIndex μ σ j)) =
      ∑ s ∈ (Finset.univ : Finset (Finset (Fin (μ.colLen 0)))).erase ∅,
        selectedTerm R μ σ s := by
  classical
  have hexpand : (∏ j, symplecticCharacterMatrix R μ (μ.colLen 0) (σ j) j) =
      ∑ s : Finset (Fin (μ.colLen 0)), selectedTerm R μ σ s := by
    change (∏ j, (complete R (mainIndex μ σ j) +
      if j.val = 0 then 0 else
        complete R ((μ.rowLen (σ j).val : ℤ) - (σ j).val - j.val))) = _
    simp_rw [add_comm (complete R (mainIndex μ σ _))]
    rw [Fintype.prod_add]
    apply Finset.sum_congr rfl
    intro s _
    exact (selectedTerm_split μ σ s).symm
  have hempty : selectedTerm R μ σ ∅ = ∏ j, complete R (mainIndex μ σ j) := by
    simp only [selectedTerm, Finset.notMem_empty, ite_false]
  rw [hexpand, ← hempty]
  exact (eq_sub_iff_add_eq.mpr
    (Finset.sum_erase_add _ _ (Finset.mem_univ ∅))).symm

/-- The correction to the Schur function has degree strictly below the diagram size. -/
theorem symplecticCharacter_sub_schur_mem (μ : YoungDiagram) :
    symplecticCharacter R μ - schur R μ ∈ degreeFiltration R (μ.card - 1) := by
  classical
  rw [symplecticCharacter, schur_eq_det_jacobiTrudiMatrix R μ (μ.colLen 0) le_rfl,
    Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro σ _
  change Equiv.Perm.sign σ • (∏ j,
    symplecticCharacterMatrix R μ (μ.colLen 0) (σ j) j) -
      Equiv.Perm.sign σ • (∏ j, complete R (mainIndex μ σ j)) ∈ _
  simp only [Units.smul_def]
  rw [← zsmul_sub]
  rw [permutation_correction]
  apply (degreeFiltration R (μ.card - 1)).toAddSubgroup.zsmul_mem
  apply Submodule.sum_mem
  intro s hs
  exact selectedTerm_mem μ σ s (Finset.mem_erase.mp hs).1

/-- A symplectic universal character has degree at most the diagram size. -/
theorem symplecticCharacter_mem_degreeFiltration (μ : YoungDiagram) :
    symplecticCharacter R μ ∈ degreeFiltration R μ.card := by
  have h := degreeFiltration_mono (Nat.sub_le μ.card 1)
    (symplecticCharacter_sub_schur_mem (R := R) μ)
  simpa only [sub_add_cancel] using
    Submodule.add_mem (degreeFiltration R μ.card) h (schur_mem_degreeFiltration μ)

/-- The top homogeneous component of a symplectic character is the Schur function. -/
theorem homogeneousComponent_symplecticCharacter (μ : YoungDiagram) :
    homogeneousComponent R μ.card (symplecticCharacter R μ) = schur R μ := by
  by_cases hz : μ.card = 0
  · have hμ : μ = ⊥ := by
      apply YoungDiagram.ext
      rw [YoungDiagram.cells_bot]
      exact Finset.card_eq_zero.mp hz
    subst μ
    rw [symplecticCharacter_bot, ← schur_bot]
    exact isHomogeneous_iff_component.mp (isHomogeneous_schur (R := R) ⊥)
  · have h := homogeneousComponent_eq_zero
      (symplecticCharacter_sub_schur_mem (R := R) μ) (show μ.card - 1 < μ.card by omega)
    rw [map_sub, homogeneousComponent_of_isHomogeneous
      (isHomogeneous_schur (R := R) μ), ite_eq_left rfl] at h
    exact sub_eq_zero.mp h

end SymmetricFunction


