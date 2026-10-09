import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Evaluation of weighted homogeneous polynomials

Substituting a homogeneous polynomial of the prescribed weight for each variable preserves
weighted degree as ordinary degree. Evaluation also commutes with the corresponding projections.

These declarations extend Mathlib's algebra APIs.

## Main results

* `MvPolynomial.IsWeightedHomogeneous.aeval` preserves degree under homogeneous substitution.
* `MvPolynomial.homogeneousComponent_aeval_weighted` commutes evaluation with degree projection.
-/

namespace MvPolynomial

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S]

namespace IsWeightedHomogeneous

/-- Weighted homogeneous evaluation is homogeneous when coefficients have degree zero and each
variable image has the prescribed degree. -/
theorem eval₂ {w : σ → ℕ} {p : MvPolynomial σ R} {m : ℕ}
    (hp : p.IsWeightedHomogeneous w m) (f : R →+* MvPolynomial τ S)
    (g : σ → MvPolynomial τ S) (hf : ∀ r, (f r).IsHomogeneous 0)
    (hg : ∀ i, (g i).IsHomogeneous (w i)) : (p.eval₂ f g).IsHomogeneous m := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa only [eval₂_zero] using isHomogeneous_zero τ S m
  | add p q _ _ hp hq => simpa only [eval₂_add] using hp.add hq
  | monomial d r hr =>
    rw [eval₂_monomial]
    have hprod := IsHomogeneous.prod d.support (fun i => g i ^ d i)
      (fun i => w i * d i) (fun i _ => (hg i).pow (d i))
    have hw : (∑ i ∈ d.support, w i * d i) = m := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.mul_comm] using hr
    simpa only [Finsupp.prod, hw, zero_add] using (hf r).mul hprod

/-- Substituting homogeneous images of the prescribed degrees preserves weighted degree. -/
theorem aeval [Algebra R S] {w : σ → ℕ} {p : MvPolynomial σ R} {m : ℕ}
    (hp : p.IsWeightedHomogeneous w m) (g : σ → MvPolynomial τ S)
    (hg : ∀ i, (g i).IsHomogeneous (w i)) : (MvPolynomial.aeval g p).IsHomogeneous m :=
  hp.eval₂ _ _ (fun _ => isHomogeneous_C _ _) hg

end IsWeightedHomogeneous

/-- Evaluation commutes with weighted-to-ordinary degree projection when coefficients have degree
zero and variable images have their prescribed degrees. -/
theorem homogeneousComponent_eval₂_weighted (w : σ → ℕ) (f : R →+* MvPolynomial τ S)
    (g : σ → MvPolynomial τ S) (hf : ∀ r, (f r).IsHomogeneous 0)
    (hg : ∀ i, (g i).IsHomogeneous (w i)) (p : MvPolynomial σ R) (n : ℕ) :
    homogeneousComponent n (p.eval₂ f g) = (weightedHomogeneousComponent w n p).eval₂ f g := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d r =>
    have hp := isWeightedHomogeneous_monomial w d r rfl
    have he := hp.eval₂ f g hf hg
    rw [homogeneousComponent_of_mem he, weightedHomogeneousComponent_of_mem hp]
    split_ifs <;> simp only [eval₂_zero]
  | add p q hp hq =>
    rw [eval₂_add, map_add, map_add, eval₂_add, hp, hq]

/-- Algebra evaluation commutes with degree projection when every variable image has its weight
as homogeneous degree. -/
theorem homogeneousComponent_aeval_weighted [Algebra R S] (w : σ → ℕ)
    (g : σ → MvPolynomial τ S) (hg : ∀ i, (g i).IsHomogeneous (w i))
    (p : MvPolynomial σ R) (n : ℕ) :
    homogeneousComponent n (aeval g p) = aeval g (weightedHomogeneousComponent w n p) :=
  homogeneousComponent_eval₂_weighted w (algebraMap R (MvPolynomial τ S)) g
    (fun _ => isHomogeneous_C _ _) hg p n

end MvPolynomial
