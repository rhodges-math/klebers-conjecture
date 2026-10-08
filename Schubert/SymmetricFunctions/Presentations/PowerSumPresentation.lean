import Schubert.SymmetricFunctions.Families.PowerSumIdentities
import Schubert.SymmetricFunctions.Presentations.ElementaryPresentation
import Schubert.SymmetricFunctions.ForMathlib.PositiveTriangular

/-!
# The rational power-sum presentation

Newton identities give a triangular substitution from elementary generators to power sums.
Its diagonal consists of rational units, including after mapping to the zero ring.

## Main results

* `exists_powerSumPresentation`: positive power sums freely generate over a rational algebra.
-/

noncomputable section

namespace SymmetricFunction

variable (R : Type*) [CommRing R]

/-- The lower Newton remainder in elementary polynomial coordinates. -/
private def newtonRemainder (e : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R) (n : ℕ+) :
    MvPolynomial ℕ+ R :=
  -∑ a ∈ Finset.antidiagonal n.val with a.1 ∈ Set.Ioo 0 n.val,
    (-1) ^ a.1 * e.symm (elementary R a.1) *
      (if h : 0 < a.2 then e.symm (powerSum R ⟨a.2, h⟩) else 0)

private theorem newtonCoordinates
    (e : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R)
    (he : ∀ n : ℕ+, e (MvPolynomial.X n) = elementary R n.val) (n : ℕ+) :
    e.symm (powerSum R n) =
      MvPolynomial.C ((-1 : R) ^ (n.val + 1) * n.val) * MvPolynomial.X n +
        newtonRemainder R e n := by
  rw [powerSum_newton, map_sub, map_mul, map_mul, map_pow, map_neg, map_one,
    map_natCast, symm_elementary_eq_X R e he]
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, apply_dite, map_zero]
  simp only [newtonRemainder, sub_eq_add_neg, apply_dite, map_natCast]

private theorem remainder_supported
    (e : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R)
    (he : ∀ n : ℕ+, e (MvPolynomial.X n) = elementary R n.val) (n : ℕ+)
    (ih : ∀ m : ℕ+, m < n → e.symm (powerSum R m) ∈
      MvPolynomial.supported R {k | k ≤ m}) :
    newtonRemainder R e n ∈ MvPolynomial.supported R {k | k < n} := by
  classical
  unfold newtonRemainder
  apply Subalgebra.neg_mem
  apply Subalgebra.sum_mem
  intro a ha
  have hm := Finset.mem_filter.mp ha
  have hs := Finset.mem_antidiagonal.mp hm.1
  have hfirst : 0 < a.1 := hm.2.1
  have hsecond : 0 < a.2 := by have h := hm.2.2; omega
  have hlt : (⟨a.2, hsecond⟩ : ℕ+) < n := by
    change a.2 < n.val
    omega
  rw [dite_eq_left hsecond]
  apply Subalgebra.mul_mem
  · apply Subalgebra.mul_mem
    · exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _
    · have hel : e.symm (elementary R a.1) = MvPolynomial.X ⟨a.1, hfirst⟩ :=
        symm_elementary_eq_X R e he ⟨a.1, hfirst⟩
      rw [hel]
      apply MvPolynomial.generator_mem_supported R _ _
      change a.1 < n.val
      exact hm.2.2
  · exact MvPolynomial.supported_mono
      (s := {k : ℕ+ | k ≤ ⟨a.2, hsecond⟩}) (t := {k : ℕ+ | k < n})
      (fun k hk => by
        change k ≤ ⟨a.2, hsecond⟩ at hk
        change k < n
        exact lt_of_le_of_lt hk hlt)
      (ih ⟨a.2, hsecond⟩ hlt)

private theorem powerCoordinates_supported
    (e : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R)
    (he : ∀ n : ℕ+, e (MvPolynomial.X n) = elementary R n.val) (n : ℕ+) :
    e.symm (powerSum R n) ∈ MvPolynomial.supported R {k | k ≤ n} := by
  exact MvPolynomial.supported_of_pnat_triangular R
    (fun n => e.symm (powerSum R n))
    (fun n => (-1 : R) ^ (n.val + 1) * n.val) (newtonRemainder R e)
    (newtonCoordinates R e he) (fun n ih => remainder_supported R e he n ih) n

/-- The signed positive Newton diagonal is the image of a rational unit. -/
private def newtonUnit [Algebra ℚ R] (n : ℕ+) : Rˣ :=
  Units.map (algebraMap ℚ R).toMonoidHom
    (Units.mk0 ((-1 : ℚ) ^ (n.val + 1) * n.val)
      (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt n.pos))))

private theorem newtonUnit_val [Algebra ℚ R] (n : ℕ+) :
    (newtonUnit R n : R) = (-1 : R) ^ (n.val + 1) * n.val := by
  simp [newtonUnit]

/-- Positive power sums give a polynomial presentation over every rational algebra. -/
theorem exists_powerSumPresentation [Algebra ℚ R] :
    ∃ e : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R,
      ∀ n : ℕ+, e (MvPolynomial.X n) = powerSum R n := by
  obtain ⟨e, he⟩ := exists_elementaryPresentation R
  have hvars (n k : ℕ+) (hk : k ∈ (newtonRemainder R e n).vars) : k < n :=
    (MvPolynomial.mem_supported.mp
      (remainder_supported R e he n (fun m _ => powerCoordinates_supported R e he m))) hk
  obtain ⟨t, ht⟩ := MvPolynomial.exists_pnatTriangularAlgEquiv R
    (newtonUnit R) (newtonRemainder R e) hvars
  refine ⟨t.trans e, ?_⟩
  intro n
  change e (t (MvPolynomial.X n)) = powerSum R n
  rw [ht, newtonUnit_val, ← newtonCoordinates R e he, e.apply_symm_apply]

/-- The polynomial presentation by positive power sums over a rational algebra. -/
def powerSumPresentation [Algebra ℚ R] :
    MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R :=
  (exists_powerSumPresentation R).choose

/-- Positive polynomial generators map to the corresponding power sums. -/
@[simp]
theorem powerSumPresentation_apply_X [Algebra ℚ R] (n : ℕ+) :
    powerSumPresentation R (MvPolynomial.X n) = powerSum R n :=
  (exists_powerSumPresentation R).choose_spec n

/-- The inverse presentation sends a positive power sum to its generator. -/
@[simp]
theorem powerSumPresentation_symm_powerSum [Algebra ℚ R] (n : ℕ+) :
    (powerSumPresentation R).symm (powerSum R n) = MvPolynomial.X n := by
  rw [← powerSumPresentation_apply_X R n, AlgEquiv.symm_apply_apply]


/-- The normalized powerSum presentation is evaluation at its generators. -/
theorem powerSumPresentation_toAlgHom [Algebra ℚ R] :
    (powerSumPresentation R).toAlgHom = MvPolynomial.aeval (fun n : ℕ+ => powerSum R n) := by
  apply MvPolynomial.algHom_ext
  intro n
  rw [MvPolynomial.aeval_X]
  exact powerSumPresentation_apply_X R n

/-- Evaluation gives the presentation value on every polynomial. -/
theorem powerSumPresentation_apply [Algebra ℚ R]
    (p : MvPolynomial ℕ+ R) :
    powerSumPresentation R p = MvPolynomial.aeval (fun n : ℕ+ => powerSum R n) p :=
  DFunLike.congr_fun (powerSumPresentation_toAlgHom R) p

end SymmetricFunction
