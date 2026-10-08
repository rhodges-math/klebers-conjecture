import Schubert.ComplementaryProducts.Gap
import Schubert.SymmetricFunctions.Projection.FirstRowProjection
import Mathlib.Data.List.OfFn
import Mathlib.Order.PiLex

/-! # Successive gap projections

The gap projection applies the prescribed first-row projections in increasing row order.
For an empty gap vector it is the identity linear map.

## Main results

* `gapProjection_apply` evaluates the projection as successive row selections.
* `gapProjection_of_half_eq_zero` gives the identity when the gap vector has no entries.
-/

noncomputable section

namespace ComplementaryProducts

/-- Compose first-row projections in increasing order of the gap-vector indices. -/
def gapProjection (R : Type*) [CommRing R] (a b : ℕ) (g : Fin (a / 2) → ℕ) :
    SymmetricFunction R →ₗ[R] SymmetricFunction R :=
  (List.ofFn (fun i => ((b + g i : ℕ) : ℤ))).foldl
    (fun p n => (SymmetricFunction.firstRowProjection R n).comp p) (LinearMap.id)

private theorem foldl_projection_apply {R : Type*} [CommRing R] (ns : List ℤ)
    (p : SymmetricFunction R →ₗ[R] SymmetricFunction R) (f : SymmetricFunction R) :
    ns.foldl (fun q n => (SymmetricFunction.firstRowProjection R n).comp q) p f =
      ns.foldl (fun v n => SymmetricFunction.firstRowProjection R n v) (p f) := by
  induction ns generalizing p with
  | nil => rfl
  | cons n ns ih =>
    simpa only [List.foldl_cons, LinearMap.comp_apply] using
      ih ((SymmetricFunction.firstRowProjection R n).comp p)

/-- Evaluation applies row projections successively, from the first gap entry to the last. -/
theorem gapProjection_apply (R : Type*) [CommRing R] (a b : ℕ) (g : Fin (a / 2) → ℕ)
    (f : SymmetricFunction R) :
    gapProjection R a b g f =
      (List.ofFn (fun i => ((b + g i : ℕ) : ℤ))).foldl
        (fun v n => SymmetricFunction.firstRowProjection R n v) f :=
  foldl_projection_apply _ (LinearMap.id) f

/-- A gap vector of length zero gives the identity projection. -/
theorem gapProjection_of_half_eq_zero (R : Type*) [CommRing R] (a b : ℕ)
    (g : Fin (a / 2) → ℕ) (ha : a / 2 = 0) : gapProjection R a b g = LinearMap.id := by
  have hnil : List.ofFn (fun i => ((b + g i : ℕ) : ℤ)) = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa only [List.length_ofFn] using ha
  rw [gapProjection, hnil, List.foldl_nil]

end ComplementaryProducts
