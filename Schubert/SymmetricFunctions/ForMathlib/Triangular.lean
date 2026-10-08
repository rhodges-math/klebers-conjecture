import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.Algebra.Algebra.Equiv

/-!
# Triangular changes of polynomial generators

A unit multiple of each generator may be modified by a polynomial in preceding generators.

These declarations extend Mathlib's algebra APIs.

## Main results

* `exists_triangularAlgEquiv`: a triangular family induces an algebra equivalence.
-/

noncomputable section

namespace MvPolynomial

variable (R : Type*) [CommRing R]

/-- The recursively substituted inverse generators of a triangular polynomial family. -/
private def triangularInverse (u : ℕ → Rˣ) (q : (n : ℕ) → MvPolynomial (Fin n) R) :
    ℕ → MvPolynomial ℕ R :=
  Nat.strongRec (fun n ih => C (↑((u n)⁻¹) : R) *
    (X n - aeval (fun i : Fin n => ih i.val i.isLt) (q n)))

private theorem triangularInverse_eq (u : ℕ → Rˣ)
    (q : (n : ℕ) → MvPolynomial (Fin n) R) (n : ℕ) :
    triangularInverse R u q n = C (↑((u n)⁻¹) : R) *
      (X n - aeval (fun i : Fin n => triangularInverse R u q i.val) (q n)) := by
  unfold triangularInverse
  rw [Nat.strongRec_eq]

/-- Unit triangular substitutions of countably many polynomial generators are invertible. -/
theorem exists_triangularAlgEquiv (u : ℕ → Rˣ)
    (q : (n : ℕ) → MvPolynomial (Fin n) R) :
    ∃ e : MvPolynomial ℕ R ≃ₐ[R] MvPolynomial ℕ R,
      ∀ n, e (X n) = C (u n : R) * X n + rename Fin.val (q n) := by
  let y : ℕ → MvPolynomial ℕ R := fun n => C (u n : R) * X n + rename Fin.val (q n)
  let g := triangularInverse R u q
  let F : MvPolynomial ℕ R →ₐ[R] MvPolynomial ℕ R := aeval y
  let G : MvPolynomial ℕ R →ₐ[R] MvPolynomial ℕ R := aeval g
  have hFG (n : ℕ) : F (g n) = X n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hq : F (aeval (fun i : Fin n => g i.val) (q n)) = rename Fin.val (q n) := by
        rw [comp_aeval_apply]
        have he : (fun i : Fin n => F (g i.val)) = fun i : Fin n => X i.val :=
          funext fun i => ih i.val i.isLt
        rw [he, rename_eq_aeval]
        rfl
      change F (triangularInverse R u q n) = X n
      rw [triangularInverse_eq, map_mul, map_sub, hq]
      simp only [F, aeval_C, algebraMap_eq, aeval_X]
      change C (↑((u n)⁻¹) : R) * (y n - rename Fin.val (q n)) = X n
      dsimp only [y]
      rw [add_sub_cancel_right, ← mul_assoc, ← C_mul]
      simp
  have hGF (n : ℕ) : G (y n) = X n := by
    change G (C (u n : R) * X n + rename Fin.val (q n)) = X n
    rw [map_add, map_mul]
    simp only [G, aeval_C, algebraMap_eq, aeval_X]
    change C (u n : R) * g n + aeval g (rename Fin.val (q n)) = X n
    rw [aeval_rename]
    change C (u n : R) * triangularInverse R u q n +
      aeval (fun i : Fin n => triangularInverse R u q i.val) (q n) = X n
    rw [triangularInverse_eq, ← mul_assoc, ← C_mul]
    simp
  have hFG' : F.comp G = AlgHom.id R (MvPolynomial ℕ R) := by
    apply algHom_ext
    intro n
    simpa only [AlgHom.comp_apply, AlgHom.id_apply, G, aeval_X] using hFG n
  have hGF' : G.comp F = AlgHom.id R (MvPolynomial ℕ R) := by
    apply algHom_ext
    intro n
    simpa only [AlgHom.comp_apply, AlgHom.id_apply, F, aeval_X] using hGF n
  refine ⟨AlgEquiv.ofAlgHom F G hFG' hGF', ?_⟩
  intro n
  exact aeval_X y n

/-- A variable-support formulation of the unit triangular substitution theorem. -/
theorem exists_triangularAlgEquiv_of_vars (u : ℕ → Rˣ)
    (p : ℕ → MvPolynomial ℕ R) (hp : ∀ n k, k ∈ (p n).vars → k < n) :
    ∃ e : MvPolynomial ℕ R ≃ₐ[R] MvPolynomial ℕ R,
      ∀ n, e (X n) = C (u n : R) * X n + p n := by
  have hq (n : ℕ) : ∃ q : MvPolynomial (Fin n) R, rename Fin.val q = p n := by
    apply exists_rename_eq_of_vars_subset_range (p n) Fin.val Fin.val_injective
    intro k hk
    exact ⟨⟨k, hp n k hk⟩, rfl⟩
  choose q hq using hq
  obtain ⟨e, he⟩ := exists_triangularAlgEquiv R u q
  refine ⟨e, ?_⟩
  intro n
  rw [he, hq]

end MvPolynomial
