import Schubert.ComplementaryProducts.OrientedIndependence
import Schubert.ComplementaryProducts.Products
import Schubert.SymmetricFunctions.Presentations.SchurCompleteCalculus

/-! # Derivative incidences of unordered splitting products

The two product-rule incidences give coordinates in the ordered splitting family.
An unequal pair contributes once at each applicable orientation; a self-pair contributes twice.

## Main results

* `coeff_zero_of_unequal_max_hook` removes unequal pairs containing a maximal hook.
-/

noncomputable section

open scoped Classical

namespace ComplementaryProducts

open SymmetricFunction

variable {R : Type*} [CommRing R] {θ : YoungDiagram}

private theorem out_sum (p : splittings θ) : p.val.out.1 + p.val.out.2 = θ := by
  apply (mk_mem_splittings θ _ _).mp
  have h : s(p.val.out.1, p.val.out.2) = p.val := by
    rw [Sym2.mk, Quot.out_eq]
  rw [h]
  exact p.property

/-- The ordered incidence obtained by differentiating the second factor. -/
private def edge (R : Type*) [CommRing R] (θ : YoungDiagram) (n : ℕ+)
    (α β : YoungDiagram) (hs : α + β = θ) : orientedSplittings θ (n.val : ℤ) →₀ R := by
  classical
  exact if h : β ≠ ⊥ ∧ β.rowLen 0 + β.colLen 0 - 1 = n.val then
    Finsupp.single ⟨(α, β), (mem_orientedSplittings _ _ _).mpr
      ⟨hs, h.1, by exact_mod_cast h.2⟩⟩ ((-1 : R) ^ (β.colLen 0 - 1)) else 0

private theorem edge_apply (n : ℕ+) (α β : YoungDiagram) (hs : α + β = θ)
    (q : orientedSplittings θ (n.val : ℤ)) :
    edge R θ n α β hs q =
      if q.val = (α, β) then (-1 : R) ^ (β.colLen 0 - 1) else 0 := by
  classical
  unfold edge
  by_cases h : β ≠ ⊥ ∧ β.rowLen 0 + β.colLen 0 - 1 = n.val
  · rw [dite_eq_left h]
    simp only [Finsupp.single_apply, Subtype.ext_iff, eq_comm]
  · rw [dite_eq_right h, Finsupp.zero_apply]
    symm
    apply ite_eq_right
    intro he
    have hq := (mem_orientedSplittings θ _ q.val).mp q.property
    have hn : q.val.2.rowLen 0 + q.val.2.colLen 0 - 1 = n.val := by
      exact_mod_cast hq.2.2
    exact h (by simpa only [he] using And.intro hq.2.1 hn)

private theorem edge_combination (n : ℕ+) (α β : YoungDiagram) (hs : α + β = θ)
    (hb : β = ⊥ ∨ β.rowLen 0 + β.colLen 0 - 1 ≤ n.val) :
    Finsupp.linearCombination R
      (fun q : orientedSplittings θ (n.val : ℤ) => orientedPairProduct R q.val)
      (edge R θ n α β hs) = schur R α * completeDerivation R n (schur R β) := by
  classical
  unfold edge
  by_cases hz : β = ⊥
  · subst β
    simp only [ne_eq, not_true_eq_false, false_and, dite_false, map_zero, schur_bot,
      Derivation.map_one_eq_zero, mul_zero]
  · have hle : β.rowLen 0 + β.colLen 0 - 1 ≤ n.val := hb.resolve_left hz
    by_cases he : β.rowLen 0 + β.colLen 0 - 1 = n.val
    · rw [dite_eq_left ⟨hz, he⟩, Finsupp.linearCombination_single, orientedPairProduct_apply,
        completeDerivation_eq_coeff_one n _ (degreeOf_schur_le_one β hz n he.symm),
        completeCoeff_schur β hz n he.symm, mul_smul_comm]
    · have hd : completeDerivation R n (schur R β) = 0 := by
        rw [completeDerivation_apply, MvPolynomial.pderiv_eq_zero_of_notMem_vars, map_zero]
        simp only [MvPolynomial.mem_vars_iff_degreeOf_ne_zero,
          degreeOf_schur_above β n (by omega), ne_eq, not_true_eq_false, not_false_eq_true]
      rw [dite_eq_right (fun h => he h.2), map_zero, hd, mul_zero]

/-- An unequal splitting containing a maximal nonempty hook has zero coefficient. -/
theorem coeff_zero_of_unequal_max_hook (n : ℕ+) (c : splittings θ → R)
    (hbound : ∀ p, c p ≠ 0 → ∀ μ ∈ (p : Sym2 YoungDiagram),
      μ = ⊥ ∨ μ.rowLen 0 + μ.colLen 0 - 1 ≤ n.val)
    (hrel : ∑ p : splittings θ, c p • schurPairProduct R p.val = 0)
    (q : orientedSplittings θ (n.val : ℤ)) (hne : q.val.1 ≠ q.val.2) :
    c ⟨s(q.val.1, q.val.2), mk_mem_splittings θ _ _ |>.mpr
      ((mem_orientedSplittings θ _ _).mp q.property).1⟩ = 0 := by
  classical
  let Q := ↥(orientedSplittings θ (n.val : ℤ))
  let v (q : Q) := orientedPairProduct R q.val
  let e (p : splittings θ) : Q →₀ R :=
    edge R θ n p.val.out.1 p.val.out.2 (out_sum p) +
      edge R θ n p.val.out.2 p.val.out.1 ((add_comm _ _).trans (out_sum p))
  let x : Q →₀ R := ∑ p : splittings θ, c p • e p
  have hx : x = 0 := by
    apply linearIndependent_iff.mp (oriented_linearIndependent R θ (n.val : ℤ))
    have he (p : splittings θ) :
        Finsupp.linearCombination R v (c p • e p) =
          c p • completeDerivation R n (schurPairProduct R p.val) := by
      by_cases hz : c p = 0
      · rw [hz, zero_smul, map_zero, zero_smul]
      · rw [map_smul, map_add, edge_combination n _ _ (out_sum p)
          (hbound p hz _ (Sym2.out_snd_mem p.val)),
          edge_combination n _ _ ((add_comm _ _).trans (out_sum p))
            (hbound p hz _ (Sym2.out_fst_mem p.val))]
        have hp : schurPairProduct R p.val = schur R p.val.out.1 * schur R p.val.out.2 := by
          conv_lhs => rw [← Quot.out_eq p.val]
          rfl
        rw [hp, completeDerivation_mul]
    have hd := congrArg (completeDerivation R n) hrel
    rw [map_sum, map_zero] at hd
    change (Finsupp.linearCombination R v) (∑ p, c p • e p) = 0
    rw [map_sum]
    simp_rw [he]
    simpa only [Derivation.map_smul] using hd
  let pq : splittings θ := ⟨s(q.val.1, q.val.2),
    (mk_mem_splittings θ _ _).mpr ((mem_orientedSplittings θ _ _).mp q.property).1⟩
  have he (p : splittings θ) :
      e p q = if p = pq then (-1 : R) ^ (q.val.2.colLen 0 - 1) else 0 := by
    have hp : s(p.val.out.1, p.val.out.2) = p.val := by rw [Sym2.mk, Quot.out_eq]
    change (edge R θ n _ _ _ + edge R θ n _ _ _) q = _
    rw [Finsupp.add_apply, edge_apply, edge_apply]
    by_cases h : p = pq
    · have hm : s(p.val.out.1, p.val.out.2) = s(q.val.1, q.val.2) := by
        rw [hp, h]
      rcases Sym2.eq_iff.mp hm with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha, hb, ite_eq_left rfl]
        have hn : q.val ≠ (q.val.2, q.val.1) := fun he => hne (congrArg Prod.fst he)
        rw [ite_eq_right hn, add_zero, ite_eq_left h]
      · rw [ha, hb, ite_eq_left rfl]
        have hn : q.val ≠ (q.val.2, q.val.1) := fun he => hne (congrArg Prod.fst he)
        rw [ite_eq_right hn, zero_add, ite_eq_left h]
    · have hleft : q.val ≠ (p.val.out.1, p.val.out.2) := by
        intro hq
        apply h
        apply Subtype.ext
        rw [← hp]
        exact congrArg (fun z : YoungDiagram × YoungDiagram => s(z.1, z.2)) hq.symm
      have hright : q.val ≠ (p.val.out.2, p.val.out.1) := by
        intro hq
        apply h
        apply Subtype.ext
        rw [← hp, Sym2.eq_swap]
        exact congrArg (fun z : YoungDiagram × YoungDiagram => s(z.1, z.2)) hq.symm
      rw [ite_eq_right hleft, ite_eq_right hright, zero_add, ite_eq_right h]
  have hv := congrArg (fun z : Q →₀ R => z q) hx
  simp only [x, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, he,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finsupp.zero_apply] at hv
  exact (isUnit_neg_one.pow (q.val.2.colLen 0 - 1)).mul_left_eq_zero.mp hv

end ComplementaryProducts
