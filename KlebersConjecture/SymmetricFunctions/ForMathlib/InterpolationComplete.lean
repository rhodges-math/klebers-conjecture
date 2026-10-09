import KlebersConjecture.SymmetricFunctions.ForMathlib.InterpolationMoments
import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Complete symmetric polynomials as interpolation moments

Reflecting polynomial interpolation gives partial fractions for a product of geometric series.
Coefficient extraction identifies the resulting moments with complete symmetric polynomials.

These declarations extend Mathlib's algebra APIs.

## Main results

* `Lagrange.eval_hsymm_eq_moment` evaluates a complete symmetric polynomial at distinct nodes.
-/

noncomputable section

namespace Lagrange

variable {F ι : Type*} [Field F]

private theorem reflect_sum [DecidableEq ι] (s : Finset ι) (p : ι → Polynomial F) (n : ℕ) :
    Polynomial.reflect n (∑ i ∈ s, p i) = ∑ i ∈ s, Polynomial.reflect n (p i) := by
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.reflect_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Polynomial.reflect_add, ih,
      Finset.sum_insert ha]

private theorem reflect_prod_sub [DecidableEq ι] (s : Finset ι) (x : ι → F) :
    Polynomial.reflect s.card (∏ a ∈ s, (Polynomial.X - Polynomial.C (x a))) =
      ∏ a ∈ s, (1 - Polynomial.C (x a) * Polynomial.X) := by
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.reflect_one]
  | @insert a s ha ih =>
    rw [Finset.card_insert_of_notMem ha, Finset.prod_insert ha,
      show s.card + 1 = 1 + s.card by omega]
    rw [Polynomial.reflect_mul _ _ (by simp) (by simp)]
    have hx : Polynomial.reflect 1 (Polynomial.X : Polynomial F) = 1 := by
      simp
    rw [ih, Polynomial.reflect_sub, hx, Polynomial.reflect_C]
    simp only [pow_one]
    rw [Finset.prod_insert ha]

private theorem interpolation_numerator {N : ℕ} (hN : 0 < N) (x : Fin N → F)
    (hx : Function.Injective x) :
    (∑ a : Fin N, Polynomial.C (x a ^ (N - 1) /
      ∏ b ∈ Finset.univ.erase a, (x a - x b)) *
        ∏ b ∈ Finset.univ.erase a, (1 - Polynomial.C (x b) * Polynomial.X)) = 1 := by
  have hdeg : (Polynomial.X ^ (N - 1) : Polynomial F).degree <
      (Finset.univ : Finset (Fin N)).card := by
    rw [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (show N - 1 < N by omega)
  have h := eq_interpolate hx.injOn hdeg
  rw [interpolate_eq_sum] at h
  have hr := congrArg (Polynomial.reflect (N - 1)) h
  rw [reflect_sum] at hr
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.reflect_C_mul] at hr
  simp only [Polynomial.reflect_monomial, Polynomial.revAt_le le_rfl,
    Nat.sub_self, pow_zero] at hr
  have he (a : Fin N) : (Finset.univ.erase a).card = N - 1 := by simp
  calc
    _ = ∑ a : Fin N, Polynomial.C (x a ^ (N - 1) /
        ∏ b ∈ Finset.univ.erase a, (x a - x b)) *
          Polynomial.reflect (N - 1)
            (∏ b ∈ Finset.univ.erase a, (Polynomial.X - Polynomial.C (x b))) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← he a, reflect_prod_sub]
    _ = 1 := hr.symm

private theorem geometric_mul_factor (c : F) :
    PowerSeries.mk (fun n => c ^ n) * (1 - PowerSeries.C c * PowerSeries.X) = 1 := by
  have h := congrArg (PowerSeries.rescale c) (PowerSeries.mk_one_mul_one_sub_eq_one F)
  simpa [PowerSeries.rescale_mk] using h

private theorem product_geometric_cancel (s : Finset ι) (x : ι → F) :
    (∏ a ∈ s, (1 - PowerSeries.C (x a) * PowerSeries.X)) *
      (∏ a ∈ s, PowerSeries.mk (fun n => x a ^ n)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro a _
  rw [mul_comm, geometric_mul_factor]

private theorem coeff_geometric_product [Fintype ι] [DecidableEq ι] (x : ι → F) (k : ℕ) :
    PowerSeries.coeff k (∏ a : ι, PowerSeries.mk (fun n => x a ^ n)) =
      MvPolynomial.eval x (MvPolynomial.hsymm ι F k) := by
  classical
  rw [PowerSeries.coeff_prod, TauCeti.eval_hsymm]
  simp only [PowerSeries.coeff_mk]
  let e : Sym ι k ≃ {d : ι →₀ ℕ // d ∈ Finset.finsuppAntidiag Finset.univ k} :=
    (Sym.equivNatSum ι k).trans (Equiv.subtypeEquivRight fun d => by
      simp only [Finset.mem_finsuppAntidiag', Finset.subset_univ, and_true]
      rfl)
  rw [← Finset.sum_attach]
  symm
  refine Fintype.sum_equiv e _ _ ?_
  intro s
  rw [Finset.prod_multiset_map_count]
  rw [Finset.prod_subset (Finset.subset_univ _) (fun a _ ha => by
    rw [Multiset.count_eq_zero.mpr (by simpa using ha), pow_zero])]
  apply Finset.prod_congr rfl
  intro a _
  rfl

/-- A complete symmetric polynomial at distinct nodes is the corresponding power moment. -/
theorem eval_hsymm_eq_moment {N : ℕ} (hN : 0 < N) (x : Fin N → F)
    (hx : Function.Injective x) (k : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Fin N) F k) =
      ∑ a : Fin N, x a ^ (k + N - 1) /
        ∏ b ∈ Finset.univ.erase a, (x a - x b) := by
  let G : Fin N → PowerSeries F := fun a => PowerSeries.mk (fun n => x a ^ n)
  have h := congrArg Polynomial.coeToPowerSeries.ringHom
    (interpolation_numerator hN x hx)
  simp only [map_sum, map_mul, map_prod, map_sub, map_one,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X] at h
  have hm := congrArg (fun p => p * ∏ a : Fin N, G a) h
  rw [one_mul, Finset.sum_mul] at hm
  have hterm (a : Fin N) :
      (∏ b ∈ Finset.univ.erase a, (1 - PowerSeries.C (x b) * PowerSeries.X)) *
        (∏ b : Fin N, G b) = G a := by
    rw [← Finset.mul_prod_erase Finset.univ G (Finset.mem_univ a)]
    calc
      _ = G a * ((∏ b ∈ Finset.univ.erase a,
          (1 - PowerSeries.C (x b) * PowerSeries.X)) *
            ∏ b ∈ Finset.univ.erase a, G b) := by ring
      _ = G a := by rw [product_geometric_cancel, mul_one]
  simp only [mul_assoc, hterm] at hm
  have hc := congrArg (PowerSeries.coeff k) hm
  rw [coeff_geometric_product] at hc
  simp only [map_sum, PowerSeries.coeff_C_mul, G, PowerSeries.coeff_mk] at hc
  calc
    _ = ∑ a : Fin N, (x a ^ (N - 1) /
        ∏ b ∈ Finset.univ.erase a, (x a - x b)) * x a ^ k := hc.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [div_mul_eq_mul_div, ← pow_add]
      congr 1
      congr 1
      omega

end Lagrange
