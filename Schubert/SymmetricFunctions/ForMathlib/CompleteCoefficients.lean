import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Complete
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Monomial

/-! # Coefficients of complete homogeneous polynomials

A complete homogeneous polynomial has coefficient one at every monomial of its degree.
These declarations extend Mathlib's symmetric-polynomial coefficient API.

## Main results

* `MvPolynomial.coeff_hsymm` computes all complete homogeneous coefficients.
-/

noncomputable section

namespace MvPolynomial

/-- A complete homogeneous polynomial contains every monomial of its degree once. -/
theorem coeff_hsymm {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]
    (k : ℕ) (d : σ →₀ ℕ) :
    (MvPolynomial.hsymm σ R k).coeff d = if d.degree = k then 1 else 0 := by
  classical
  rw [MvPolynomial.hsymm, MvPolynomial.coeff_sum]
  simp only [TauCeti.prod_map_X_eq_monomial, MvPolynomial.coeff_monomial]
  by_cases hd : d.degree = k
  · rw [ite_eq_left hd, Finset.sum_eq_single (TauCeti.weightSym d hd)]
    · change (if d.toMultiset.toFinsupp = d then (1 : R) else 0) = 1
      rw [Finsupp.toMultiset_toFinsupp, ite_eq_left rfl]
    · intro s _ hs
      apply ite_eq_right
      intro h
      apply hs
      apply Sym.ext
      rw [TauCeti.coe_weightSym, ← h, Multiset.toFinsupp_toMultiset]
      rfl
    · exact fun h => (h (Finset.mem_univ _)).elim
  · rw [ite_eq_right hd]
    apply Finset.sum_eq_zero
    intro s _
    apply ite_eq_right
    intro h
    apply hd
    have hc := congrArg (fun t : σ →₀ ℕ => t.degree) h
    have hs : (Multiset.toFinsupp (s : Multiset σ)).degree = k := by
      rw [← TauCeti.card_toMultiset_eq_degree, Multiset.toFinsupp_toMultiset]
      exact s.property
    exact hc.symm.trans hs


end MvPolynomial
