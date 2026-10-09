import KlebersConjecture.SymmetricFunctions.LittlewoodRichardson.FiniteAlphabet.Involution
import KlebersConjecture.SymmetricFunctions.LittlewoodRichardson.FiniteAlphabet.SchurBridge

/-! # Integral finite Littlewood–Richardson rule

The recutting involution cancels the nonlattice terms in the tableau expansion of an alternant
times a finite Schur polynomial.

## Main results

* `alternant_mul_schur_eq_sum_lattice`: only lattice tableaux contribute to the alternant expansion.
* `coeff_alternant_mul_schur`: its decreasing-weight coefficients count lattice tableaux.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction.FiniteAlphabet.LittlewoodRichardson

open SemistandardYoungTableau SymmetricFunction.FiniteAlphabet.Alternants Equiv

variable {d : ℕ} {ν : YoungDiagram} {κ : IntWeight d}

/-- The involution, on tableaux in the letters `0, …, d − 1`. -/
def lrSwapBounded (hκ : Antitone κ) (T : TauCeti.BoundedSSYT d ν) {r i : ℕ}
    (h : IsFirstViolation κ T.1 r i) : TauCeti.BoundedSSYT d ν :=
  ⟨lrSwap hκ h, fun a c hac => by
    have hlt := h.lt
    rw [lrSwap, recut_apply]
    split_ifs
    · omega
    · omega
    · exact T.2 a c hac⟩

/-- The bounded recutting operation has the underlying recut tableau. -/
theorem lrSwapBounded_val (hκ : Antitone κ) (T : TauCeti.BoundedSSYT d ν) {r i : ℕ}
    (h : IsFirstViolation κ T.1 r i) : (lrSwapBounded hκ T h).1 = lrSwap hκ h :=
  rfl

/-- **The sign-reversing property**: the involution replaces `κ + wt T + δ` by its image under
the transposition of the letters `i` and `i + 1`. -/
theorem weight_lrSwapBounded (hκ : Antitone κ) (T : TauCeti.BoundedSSYT d ν) {r i : ℕ}
    (h : IsFirstViolation κ T.1 r i) :
    κ + weightVec (lrSwapBounded hκ T h) + staircase d =
      (κ + weightVec T + staircase d) ∘ ⇑(swap (⟨i, by have := h.lt; omega⟩ : Fin d)
        ⟨i + 1, h.lt⟩) := by
  have hlt := h.lt
  have hadd := content_lrSwap_add hκ h
  have hpair := content_lrSwap_pair hκ h
  have he := balanceNat_eq hκ h
  rw [balance] at he
  have hki := weightAt_of_lt κ (i := i) (by omega)
  have hki' := weightAt_of_lt κ hlt
  have hz : ((content (lrSwap hκ h) i : ℕ) : ℤ) + (balanceNat κ T.1 r i : ℕ) + 1 +
      (countBelow T.1 r (i + 1) : ℕ) = (content T.1 (i + 1) : ℕ) + (countBelow T.1 r i : ℕ) := by
    exact_mod_cast hadd
  have hp : ((content (lrSwap hκ h) i : ℕ) : ℤ) + (content (lrSwap hκ h) (i + 1) : ℕ) =
      (content T.1 i : ℕ) + (content T.1 (i + 1) : ℕ) := by
    exact_mod_cast hpair
  rw [hki, hki'] at he
  funext x
  obtain ⟨x, hx⟩ := x
  simp only [Pi.add_apply, Function.comp_apply, weightVec, lrSwapBounded_val, staircase]
  by_cases hxi : x = i
  · subst hxi
    rw [swap_apply_left]
    simp only
    push_cast at *
    linarith
  · by_cases hxi' : x = i + 1
    · subst hxi'
      rw [swap_apply_right]
      simp only
      push_cast at *
      linarith
    · rw [swap_apply_of_ne_of_ne (fun e => hxi (congrArg Fin.val e))
        (fun e => hxi' (congrArg Fin.val e)), content_lrSwap_of_ne hκ h hxi hxi']

/-- An alternant changes sign under a transposition. -/
theorem alternant_comp_swap (β : IntWeight d) {a b : Fin d} (hab : a ≠ b) :
    alternant (β ∘ ⇑(swap a b)) = -alternant β := by
  rw [alternant_comp_perm, Perm.sign_swap hab]
  ext w
  rw [coeff_single_zero_mul]
  simp

/-- On a tableau that is not lattice, the involution reverses the sign of the alternant term. -/
theorem alternant_lrSwapBounded (hκ : Antitone κ) (T : TauCeti.BoundedSSYT d ν) {r i : ℕ}
    (h : IsFirstViolation κ T.1 r i) :
    alternant (κ + weightVec (lrSwapBounded hκ T h) + staircase d) =
      -alternant (κ + weightVec T + staircase d) := by
  rw [weight_lrSwapBounded hκ T h, alternant_comp_swap]
  intro e
  have := congrArg Fin.val e
  simp at this

/-- Recutting twice at the preserved first violation recovers the tableau. -/
theorem lrSwapBounded_lrSwapBounded (hκ : Antitone κ) (T : TauCeti.BoundedSSYT d ν) {r i r' i' : ℕ}
    (h : IsFirstViolation κ T.1 r i) (h' : IsFirstViolation κ (lrSwapBounded hκ T h).1 r' i') :
    lrSwapBounded hκ (lrSwapBounded hκ T h) h' = T := by
  obtain ⟨rfl, rfl⟩ := (isFirstViolation_lrSwap hκ h).unique h'
  exact Subtype.ext (lrSwap_lrSwap hκ h)

/-- The first violation of a tableau that is not lattice. -/
def firstViolation {T : SemistandardYoungTableau ν} (h : ¬ IsLattice κ T) : ℕ × ℕ :=
  Classical.choose (show ∃ p : ℕ × ℕ, IsFirstViolation κ T p.1 p.2 by
    obtain ⟨r, i, hri⟩ := exists_isFirstViolation h
    exact ⟨(r, i), hri⟩)

/-- The chosen first violation satisfies its defining inequalities. -/
theorem isFirstViolation_firstViolation {T : SemistandardYoungTableau ν}
    (h : ¬ IsLattice κ T) :
    IsFirstViolation κ T (firstViolation h).1 (firstViolation h).2 :=
  Classical.choose_spec (show ∃ p : ℕ × ℕ, IsFirstViolation κ T p.1 p.2 by
    obtain ⟨r, i, hri⟩ := exists_isFirstViolation h
    exact ⟨(r, i), hri⟩)

/-- The involution on all bounded tableaux: the identity on the lattice ones. -/
def lrInvolution (hκ : Antitone κ) (T : TauCeti.BoundedSSYT d ν) : TauCeti.BoundedSSYT d ν :=
  if h : IsLattice κ T.1 then T else lrSwapBounded hκ T (isFirstViolation_firstViolation h)

/-- On a nonlattice tableau, the involution uses its first violation. -/
theorem lrInvolution_of_not (hκ : Antitone κ) {T : TauCeti.BoundedSSYT d ν}
    (h : ¬ IsLattice κ T.1) :
    lrInvolution hκ T = lrSwapBounded hκ T (isFirstViolation_firstViolation h) :=
  dite_eq_right h

/-- The cancellation involution preserves nonlattice tableaux. -/
theorem not_isLattice_lrInvolution (hκ : Antitone κ) {T : TauCeti.BoundedSSYT d ν}

    (h : ¬ IsLattice κ T.1) : ¬ IsLattice κ (lrInvolution hκ T).1 := by
  rw [lrInvolution_of_not hκ h]
  exact (isFirstViolation_lrSwap hκ (isFirstViolation_firstViolation h)).not_isLattice

/-- The cancellation map is involutive on nonlattice tableaux. -/
theorem lrInvolution_lrInvolution (hκ : Antitone κ) {T : TauCeti.BoundedSSYT d ν}
    (h : ¬ IsLattice κ T.1) :
    lrInvolution hκ (lrInvolution hκ T) = T := by
  have key : ∀ S : TauCeti.BoundedSSYT d ν,
      S = lrSwapBounded hκ T (isFirstViolation_firstViolation h) →
        ∀ {r' i' : ℕ} (h' : IsFirstViolation κ S.1 r' i'), lrSwapBounded hκ S h' = T := by
    rintro S rfl r' i' h'
    exact lrSwapBounded_lrSwapBounded hκ T _ h'
  rw [lrInvolution_of_not hκ (not_isLattice_lrInvolution hκ h)]
  exact key _ (lrInvolution_of_not hκ h) _

/-- **The terms of the tableaux that are not lattice cancel.** -/
theorem sum_not_isLattice (hκ : Antitone κ) :
    ∑ T ∈ Finset.univ.filter (fun T : TauCeti.BoundedSSYT d ν => ¬ IsLattice κ T.1),
      alternant (κ + weightVec T + staircase d) = 0 := by
  refine Finset.sum_involution (fun T _ => lrInvolution hκ T) (fun T hT => ?_) (fun T hT hne => ?_)
    (fun T hT => ?_) (fun T hT => ?_)
  · have hT' := (Finset.mem_filter.mp hT).2
    rw [lrInvolution_of_not hκ hT', alternant_lrSwapBounded, add_neg_cancel]
  · have hT' := (Finset.mem_filter.mp hT).2
    intro heq
    apply hne
    have h1 : alternant (κ + weightVec (lrInvolution hκ T) + staircase d) =
        -alternant (κ + weightVec T + staircase d) := by
      rw [lrInvolution_of_not hκ hT', alternant_lrSwapBounded]
    rw [heq] at h1
    ext w
    have h3 := congrArg (fun f : IntLaurent d => f.coeff w) h1
    simp only [AddMonoidAlgebra.coeff_neg] at h3
    have h4 : (alternant (κ + weightVec T + staircase d)).coeff w = 0 := by
      have h5 : (alternant (κ + weightVec T + staircase d)).coeff w =
          -(alternant (κ + weightVec T + staircase d)).coeff w := by simpa using h3
      linarith
    simpa using h4
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      not_isLattice_lrInvolution hκ (Finset.mem_filter.mp hT).2⟩
  · exact lrInvolution_lrInvolution hκ (Finset.mem_filter.mp hT).2

/-- A Schur polynomial, as a Laurent polynomial, is the sum of the monomials of its tableaux. -/
theorem toLaurent_diagramSchurPoly (ν : YoungDiagram) :
    toLaurent (TauCeti.diagramSchurPoly d ℤ ν) =
      ∑ T : TauCeti.BoundedSSYT d ν, AddMonoidAlgebra.single (weightVec T) (1 : ℤ) := by
  rw [TauCeti.diagramSchurPoly_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [toLaurent_monomial]
  congr 1

/-- **The Littlewood–Richardson rule**, alternant form: for a weakly decreasing integer weight
`κ` and a Young diagram `ν`, `a_{κ + δ} · s_ν = ∑_{T lattice from κ} a_{κ + wt(T) + δ}`, the
sum over the semistandard tableaux of shape `ν` in the letters `0, …, d − 1` whose reverse
row word is lattice from `κ`. -/
theorem alternant_mul_schur_eq_sum_lattice (κ : IntWeight d) (hκ : Antitone κ) (ν : YoungDiagram) :
    alternant (κ + staircase d) * toLaurent (TauCeti.diagramSchurPoly d ℤ ν) =
      ∑ T ∈ Finset.univ.filter (fun T : TauCeti.BoundedSSYT d ν => IsLattice κ T.1),
        alternant (κ + weightVec T + staircase d) := by
  have hsym : IsSymmetric (∑ T ∈ (Finset.univ : Finset (TauCeti.BoundedSSYT d ν)),
      AddMonoidAlgebra.single (weightVec T) (1 : ℤ)) := by
    rw [← toLaurent_diagramSchurPoly]
    exact isSymmetric_toLaurent (TauCeti.isSymmetric_diagramSchurPoly d ℤ ν)
  rw [toLaurent_diagramSchurPoly, alternant_mul_sum_single _ _ _ hsym,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun T : TauCeti.BoundedSSYT d ν =>
      IsLattice κ T.1)]
  have h0 := sum_not_isLattice hκ (ν := ν)
  have hc : ∀ T : TauCeti.BoundedSSYT d ν,
      κ + staircase d + weightVec T = κ + weightVec T + staircase d := fun T => add_right_comm _ _ _
  simp only [hc, h0, add_zero]

/-- **The coefficient form of the Littlewood–Richardson rule**: for weakly decreasing `κ` and
`λ`, the coefficient of `x^{λ + δ}` in `a_{κ + δ} s_ν` (the multiplicity of `a_{λ + δ}`) is
the number of tableaux of shape `ν` lattice from `κ` with `κ + wt(T) = λ`. -/
theorem coeff_alternant_mul_schur (κ lam : IntWeight d) (hκ : Antitone κ) (hlam : Antitone lam)
    (ν : YoungDiagram) :
    (alternant (κ + staircase d) * toLaurent (TauCeti.diagramSchurPoly d ℤ ν)).coeff
        (lam + staircase d) =
      ((Finset.univ.filter fun T : TauCeti.BoundedSSYT d ν =>
        IsLattice κ T.1 ∧ κ + weightVec T = lam).card : ℤ) := by
  classical
  rw [alternant_mul_schur_eq_sum_lattice κ hκ ν]
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  have hterm : ∀ T ∈ Finset.univ.filter (fun T : TauCeti.BoundedSSYT d ν => IsLattice κ T.1),
      (alternant (κ + weightVec T + staircase d)).coeff (lam + staircase d) =
        if κ + weightVec T = lam then 1 else 0 := by
    intro T hT
    rw [coeff_alternant_of_strictAnti
      (strictAnti_add_staircase (antitone_add_weightVec (Finset.mem_filter.mp hT).2))
      (strictAnti_add_staircase hlam)]
    by_cases he : κ + weightVec T = lam
    · simp [he]
    · have he' : κ + weightVec T + staircase d ≠ lam + staircase d :=
        fun e => he (add_right_cancel e)
      simp [he, he']
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole, Finset.filter_filter]

end SymmetricFunction.FiniteAlphabet.LittlewoodRichardson

end
