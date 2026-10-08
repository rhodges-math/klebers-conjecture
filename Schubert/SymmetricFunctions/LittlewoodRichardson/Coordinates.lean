import Schubert.SymmetricFunctions.LittlewoodRichardson.FiniteAlphabet.SchurBridge
import Schubert.SymmetricFunctions.Bases.SchurBasis
import Schubert.SymmetricFunctions.LittlewoodRichardson.FiniteAlphabet.Rule

/-! # Integral Schur coordinates from finite alternants

Finite alphabets large enough for a Schur expansion extract its stable coordinates.
The integral Littlewood--Richardson cancellation rule gives nonnegative product coordinates.

## Main results

* `schurBasis_repr_eq_alternant_coeff` extracts a support-bounded Schur coordinate.
* `schurBasis_repr_mul_eq_count` counts a product coordinate by finite tableaux.
* `schurBasis_repr_mul_nonneg` proves integral product coordinates are nonnegative.
* `exists_schur_alphabet_bound` bounds diagram heights and coordinate support.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction

open SymmetricFunction.FiniteAlphabet SymmetricFunction.FiniteAlphabet.Alternants

private theorem antitone_rows (μ : YoungDiagram) (n : ℕ) :
    Antitone (fun i : Fin n => (μ.rowLen i : ℤ)) := by
  intro i j hij
  change (μ.rowLen j : ℤ) ≤ (μ.rowLen i : ℤ)
  exact_mod_cast YoungDiagram.rowLen_anti μ i j hij

private theorem shifted_rows_eq_iff (μ ν : YoungDiagram) (n : ℕ)
    (hμ : μ.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n) :
    ((fun i : Fin n => (μ.rowLen i : ℤ)) + staircase n =
      (fun i : Fin n => (ν.rowLen i : ℤ)) + staircase n) ↔ μ = ν := by
  constructor
  · intro h
    apply YoungDiagram.rowLen_injective
    funext i
    by_cases hi : i < n
    · have he := congrFun h ⟨i, hi⟩
      simp only [Pi.add_apply] at he
      omega
    · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (hμ.trans (Nat.not_lt.mp hi)),
        YoungDiagram.rowLen_eq_zero_of_colLen_le (hν.trans (Nat.not_lt.mp hi))]
  · rintro rfl
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- A finite Laurent coefficient extracts a Schur coordinate when all support heights fit. -/
theorem schurBasis_repr_eq_alternant_coeff (f : SymmetricFunction ℤ) (γ : YoungDiagram)
    (n : ℕ) (hγ : γ.colLen 0 ≤ n)
    (hf : ∀ ν ∈ ((schurBasis ℤ).repr f).support,
      ν.colLen 0 ≤ n) :
    (schurBasis ℤ).repr f γ =
      (alternant (staircase n) * toLaurent
        (restrict ℤ n f)).coeff
        ((fun i : Fin n => (γ.rowLen i : ℤ)) +
          staircase n) := by
  classical
  let d := n
  let φ := toLaurent.comp
    (restrict ℤ n).toRingHom
  let L : SymmetricFunction ℤ →ₗ[ℤ] IntLaurent d := φ.toAddMonoidHom.toIntLinearMap
  have hL (ν : YoungDiagram) : L (schur ℤ ν) =
      toLaurent (TauCeti.diagramSchurPoly d ℤ ν) := by
    change toLaurent (restrict ℤ n (schur ℤ ν)) = _
    rw [restrict_schur_eq_diagramSchurPoly]
  have hexp := congrArg L ((schurBasis ℤ).linearCombination_repr f)
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum] at hexp
  simp only [LinearMap.map_smul, schurBasis_apply, hL] at hexp
  change _ = (alternant (staircase d) * L f).coeff _
  rw [← hexp, Finset.mul_sum, AddMonoidAlgebra.coeff_sum]
  have hterm (ν : YoungDiagram) (hν : ν ∈ ((schurBasis ℤ).repr f).support) :
      (alternant (staircase d) *
        ((schurBasis ℤ).repr f ν • toLaurent (TauCeti.diagramSchurPoly d ℤ ν))).coeff
        ((fun i : Fin d => (γ.rowLen i : ℤ)) + staircase d) =
        if ν = γ then (schurBasis ℤ).repr f ν else 0 := by
    rw [mul_smul_comm, alternant_mul_schur ν (hf ν hν)]
    simp only [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    change (schurBasis ℤ).repr f ν *
      (alternant ((fun i : Fin d => (ν.rowLen i : ℤ)) + staircase d)).coeff
        ((fun i : Fin d => (γ.rowLen i : ℤ)) + staircase d) = _
    rw [coeff_alternant_of_strictAnti
      (strictAnti_add_staircase (antitone_rows ν d))
      (strictAnti_add_staircase (antitone_rows γ d))]
    simp only [shifted_rows_eq_iff ν γ d (hf ν hν) hγ]
    split_ifs <;> simp
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_congr rfl hterm]
  simp

/-- A sufficiently large finite alphabet counts an integral Schur product coordinate. -/
theorem schurBasis_repr_mul_eq_count (α β γ : YoungDiagram) (n : ℕ)
    (hα : α.colLen 0 ≤ n)
    (hγ : γ.colLen 0 ≤ n)
    (hf : ∀ ν ∈ ((schurBasis ℤ).repr (schur ℤ α * schur ℤ β)).support,
      ν.colLen 0 ≤ n) :
    (schurBasis ℤ).repr (schur ℤ α * schur ℤ β) γ =
      ((Finset.univ.filter fun T : TauCeti.BoundedSSYT n β =>
        FiniteAlphabet.LittlewoodRichardson.IsLattice
          (fun i : Fin n => (α.rowLen i : ℤ)) T.1 ∧
          (fun i : Fin n => (α.rowLen i : ℤ)) +
            FiniteAlphabet.LittlewoodRichardson.weightVec T =
            (fun i : Fin n => (γ.rowLen i : ℤ))).card : ℤ) := by
  classical
  rw [schurBasis_repr_eq_alternant_coeff _ γ n hγ hf, map_mul, map_mul,
    restrict_schur_eq_diagramSchurPoly, restrict_schur_eq_diagramSchurPoly, ← mul_assoc,
    alternant_mul_schur α hα]
  exact FiniteAlphabet.LittlewoodRichardson.coeff_alternant_mul_schur _ _
    (antitone_rows α _) (antitone_rows γ _) β

/-- A finite alphabet contains two diagrams and every nonzero coordinate of a function. -/
theorem exists_schur_alphabet_bound (f : SymmetricFunction ℤ) (α γ : YoungDiagram) :
    ∃ n, α.colLen 0 ≤ n ∧ γ.colLen 0 ≤ n ∧
      ∀ ν ∈ ((schurBasis ℤ).repr f).support, ν.colLen 0 ≤ n := by
  classical
  let S := ((schurBasis ℤ).repr f).support
  refine ⟨max (α.colLen 0) (max (γ.colLen 0) (S.sup fun ν => ν.colLen 0)),
    le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro ν hν
  exact (Finset.le_sup (f := fun ν : YoungDiagram => ν.colLen 0) hν).trans
    ((le_max_right _ _).trans (le_max_right _ _))

/-- Every integral Schur product coordinate is nonnegative. -/
theorem schurBasis_repr_mul_nonneg (α β γ : YoungDiagram) :
    0 ≤ (schurBasis ℤ).repr (schur ℤ α * schur ℤ β) γ := by
  classical
  obtain ⟨n, hα, hγ, hf⟩ :=
    exists_schur_alphabet_bound (schur ℤ α * schur ℤ β) α γ
  rw [schurBasis_repr_mul_eq_count α β γ n hα hγ hf]
  exact Int.natCast_nonneg _

end SymmetricFunction
