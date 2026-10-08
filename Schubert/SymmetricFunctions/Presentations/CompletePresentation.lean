import Schubert.SymmetricFunctions.Families.CompleteIdentities
import Schubert.SymmetricFunctions.Presentations.ElementaryPresentation
import Schubert.SymmetricFunctions.ForMathlib.PositiveTriangular
import Mathlib.Data.PNat.Basic

/-! # The complete symmetric-function presentation

The inverse elementary and complete identities give a unit triangular change of positive
polynomial generators over every commutative ring.

## Main results

* `SymmetricFunction.exists_completePresentation` gives the normalized algebra equivalence.
-/

noncomputable section

namespace SymmetricFunction

variable (R : Type*) [CommRing R]

private def completeRemainder (e : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R) (n : ℕ+) :
    MvPolynomial ℕ+ R :=
  -∑ i ∈ Finset.Ico 1 n.val, (-1 : R) ^ i •
    (e.symm (elementary R i) * e.symm (complete R ((n.val - i : ℕ) : ℤ)))

private theorem completeCoordinates
    (e : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R)
    (he : ∀ n : ℕ+, e (MvPolynomial.X n) = elementary R n.val) (n : ℕ+) :
    e.symm (complete R (n.val : ℤ)) =
      MvPolynomial.C ((-1 : R) ^ (n.val + 1)) * MvPolynomial.X n +
        completeRemainder R e n := by
  rw [complete_nat_eq_signed_elementary R n.val n.pos, map_sub, map_smul,
    symm_elementary_eq_X R e he]
  simp only [map_sum, map_smul, map_mul, completeRemainder,
    MvPolynomial.smul_eq_C_mul, sub_eq_add_neg]

private theorem remainder_supported
    (e : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R)
    (he : ∀ n : ℕ+, e (MvPolynomial.X n) = elementary R n.val) (n : ℕ+)
    (ih : ∀ m : ℕ+, m < n → e.symm (complete R (m.val : ℤ)) ∈
      MvPolynomial.supported R {k | k ≤ m}) :
    completeRemainder R e n ∈ MvPolynomial.supported R {k | k < n} := by
  classical
  unfold completeRemainder
  apply Subalgebra.neg_mem
  apply Subalgebra.sum_mem
  intro i hi
  have hmem := Finset.mem_Ico.mp hi
  have hipos : 0 < i := by omega
  have hjpos : 0 < n.val - i := Nat.sub_pos_of_lt hmem.2
  have hjlt : (⟨n.val - i, hjpos⟩ : ℕ+) < n := by
    change n.val - i < n.val
    omega
  apply Subalgebra.smul_mem
  apply Subalgebra.mul_mem
  · have hi := symm_elementary_eq_X R e he (⟨i, hipos⟩ : ℕ+)
    change e.symm (elementary R i) = MvPolynomial.X (⟨i, hipos⟩ : ℕ+) at hi
    rw [hi]
    apply MvPolynomial.generator_mem_supported R _ _
    change i < n.val
    exact hmem.2
  · exact MvPolynomial.supported_mono
      (s := {k : ℕ+ | k ≤ ⟨n.val - i, hjpos⟩}) (t := {k : ℕ+ | k < n})
      (fun k hk => by
        change k ≤ ⟨n.val - i, hjpos⟩ at hk
        change k < n
        exact lt_of_le_of_lt hk hjlt)
      (ih ⟨n.val - i, hjpos⟩ hjlt)

private theorem completeCoordinates_supported
    (e : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R)
    (he : ∀ n : ℕ+, e (MvPolynomial.X n) = elementary R n.val) (n : ℕ+) :
    e.symm (complete R (n.val : ℤ)) ∈ MvPolynomial.supported R {k | k ≤ n} := by
  exact MvPolynomial.supported_of_pnat_triangular R
    (fun n => e.symm (complete R (n.val : ℤ)))
    (fun n => (-1 : R) ^ (n.val + 1)) (completeRemainder R e)
    (completeCoordinates R e he) (fun n ih => remainder_supported R e he n ih) n

/-- Positive complete functions freely generate the symmetric-function algebra. -/
theorem exists_completePresentation :
    ∃ e : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R,
      ∀ n : ℕ+, e (MvPolynomial.X n) = complete R (n.val : ℤ) := by
  classical
  obtain ⟨e, he⟩ := exists_elementaryPresentation R
  have hp : ∀ n k, k ∈ (completeRemainder R e n).vars → k < n := by
    intro n k hk
    exact (MvPolynomial.mem_supported.mp (remainder_supported R e he n
      (fun m _ => completeCoordinates_supported R e he m))) hk
  obtain ⟨t, ht⟩ := MvPolynomial.exists_pnatTriangularAlgEquiv R
    (fun n => (-1 : Rˣ) ^ (n.val + 1)) (completeRemainder R e) hp
  refine ⟨t.trans e, ?_⟩
  intro n
  change e (t (MvPolynomial.X n)) = complete R (n.val : ℤ)
  rw [ht]
  change e (MvPolynomial.C ((-1 : R) ^ (n.val + 1)) * MvPolynomial.X n +
    completeRemainder R e n) = complete R (n.val : ℤ)
  rw [← completeCoordinates R e he n, e.apply_symm_apply]

/-- The polynomial presentation by positive complete symmetric functions. -/
def completePresentation : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R :=
  (exists_completePresentation R).choose

/-- Positive polynomial generators map to the corresponding complete functions. -/
@[simp]
theorem completePresentation_apply_X (n : ℕ+) :
    completePresentation R (MvPolynomial.X n) = complete R (n.val : ℤ) :=
  (exists_completePresentation R).choose_spec n

/-- The inverse presentation sends a positive complete function to its generator. -/
@[simp↓]
theorem completePresentation_symm_complete (n : ℕ+) :
    (completePresentation R).symm (complete R (n.val : ℤ)) = MvPolynomial.X n := by
  rw [← completePresentation_apply_X R n, AlgEquiv.symm_apply_apply]


/-- The normalized complete presentation is evaluation at its generators. -/
theorem completePresentation_toAlgHom :
    (completePresentation R).toAlgHom =
      MvPolynomial.aeval (fun n : ℕ+ => complete R (n.val : ℤ)) := by
  apply MvPolynomial.algHom_ext
  intro n
  rw [MvPolynomial.aeval_X]
  exact completePresentation_apply_X R n

/-- Evaluation gives the presentation value on every polynomial. -/
theorem completePresentation_apply
    (p : MvPolynomial ℕ+ R) :
    completePresentation R p = MvPolynomial.aeval (fun n : ℕ+ => complete R (n.val : ℤ)) p :=
  DFunLike.congr_fun (completePresentation_toAlgHom R) p

end SymmetricFunction
