import KlebersConjecture.SymmetricFunctions.ForMathlib.Triangular
import Mathlib.Data.PNat.Equiv

/-! # Triangular changes of positive generators

Unit triangular substitutions are invertible for polynomials indexed by the positive
natural numbers. The lower terms involve only smaller positive indices.

These declarations extend Mathlib's algebra APIs.

## Main results

* `MvPolynomial.exists_pnatTriangularAlgEquiv` gives the normalized algebra equivalence.
-/

noncomputable section

namespace MvPolynomial

/-- Unit triangular substitutions of positive polynomial generators are invertible. -/
theorem exists_pnatTriangularAlgEquiv (R : Type*) [CommRing R]
    (u : ℕ+ → Rˣ) (p : ℕ+ → MvPolynomial ℕ+ R)
    (hp : ∀ n k, k ∈ (p n).vars → k < n) :
    ∃ e : MvPolynomial ℕ+ R ≃ₐ[R] MvPolynomial ℕ+ R,
      ∀ n, e (X n) = C (u n : R) * X n + p n := by
  classical
  let a := Equiv.pnatEquivNat
  let q : ℕ → MvPolynomial ℕ R := fun n => rename a (p (a.symm n))
  have hq : ∀ n k, k ∈ (q n).vars → k < n := by
    intro n k hk
    obtain ⟨i, hi, rfl⟩ := mem_vars_rename a (p (a.symm n)) hk
    have hlt := hp (a.symm n) i hi
    change i.val < n + 1 at hlt
    change i.val - 1 < n
    have hi0 := i.pos
    omega
  obtain ⟨e, he⟩ := exists_triangularAlgEquiv_of_vars R (fun n => u (a.symm n)) q hq
  let t := renameEquiv R a
  refine ⟨(t.trans e).trans t.symm, ?_⟩
  intro n
  change rename a.symm (e (rename a (X n))) = _
  rw [rename_X, he]
  simp only [map_add, map_mul, rename_C, rename_X, Equiv.symm_apply_apply]
  dsimp only [q]
  rw [rename_rename]
  simp only [Equiv.symm_apply_apply, a, Equiv.symm_comp_self, rename_id_apply]

end MvPolynomial

/-- A polynomial generator belongs to the algebra supported on a set containing its index. -/
theorem MvPolynomial.generator_mem_supported (R : Type*) [CommRing R]
    {σ : Type*} (s : Set σ) (n : σ) (hn : n ∈ s) :
    (MvPolynomial.X n : MvPolynomial σ R) ∈ MvPolynomial.supported R s :=
  Algebra.subset_adjoin ⟨n, hn, rfl⟩

/-- A triangular recurrence places each coordinate in the algebra of earlier generators. -/
theorem MvPolynomial.supported_of_pnat_triangular (R : Type*) [CommRing R]
    (v : ℕ+ → MvPolynomial ℕ+ R) (u : ℕ+ → R) (r : ℕ+ → MvPolynomial ℕ+ R)
    (hv : ∀ n, v n = MvPolynomial.C (u n) * MvPolynomial.X n + r n)
    (hr : ∀ n, (∀ m : ℕ+, m < n → v m ∈ MvPolynomial.supported R {k | k ≤ m}) →
      r n ∈ MvPolynomial.supported R {k | k < n}) (n : ℕ+) :
    v n ∈ MvPolynomial.supported R {k | k ≤ n} := by
  induction n using WellFoundedLT.induction with
  | ind n ih =>
    rw [hv]
    apply Subalgebra.add_mem
    · apply Subalgebra.mul_mem
      · exact (MvPolynomial.supported R {k | k ≤ n}).algebraMap_mem _
      · apply MvPolynomial.generator_mem_supported R _ n
        change n ≤ n
        exact le_rfl
    · exact MvPolynomial.supported_mono
        (s := {k : ℕ+ | k < n}) (t := {k : ℕ+ | k ≤ n})
        (fun k hk => by
          change k < n at hk
          change k ≤ n
          exact le_of_lt hk) (hr n ih)
