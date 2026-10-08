import Schubert.ComplementaryProducts.SplittingDerivative
import Schubert.ComplementaryProducts.MaximalSelfPair

/-! # Independence of componentwise splitting products

Differentiating at a maximal supported hook eliminates the unequal splittings.
The maximal-self-pair coefficient theorem eliminates the remaining diagonal term integrally.

## Main results

* `splitting_linearIndependent` proves independence over every commutative ring.
-/

noncomputable section

namespace ComplementaryProducts

open SymmetricFunction

/-- A relation on the empty splitting has zero coefficient at its sole index. -/
private theorem coeff_zero_of_empty_splitting (R : Type*) [CommRing R]
    (c : splittings ⊥ → R)
    (hrel : (∑ q : splittings ⊥, c q • schurPairProduct R q.val) = 0)
    (p : splittings ⊥) : c p = 0 := by
  classical
  have he (q : splittings ⊥) : q = p := by
    apply Subtype.ext
    have hq : q.val = s(⊥, ⊥) := by
      simpa only [splittings_bot, Finset.mem_singleton] using q.property
    have hp : p.val = s(⊥, ⊥) := by
      simpa only [splittings_bot, Finset.mem_singleton] using p.property
    exact hq.trans hp.symm
  rw [Finset.sum_eq_single p] at hrel
  · have hval : p.val = s(⊥, ⊥) := by
      simpa only [splittings_bot, Finset.mem_singleton] using p.property
    rw [hval, schurPairProduct_mk, schur_bot, one_mul] at hrel
    have hz := congrArg (fun f : SymmetricFunction R => (schurBasis R).repr f ⊥) hrel
    rw [map_smul, ← schur_bot, ← schurBasis_apply, Module.Basis.repr_self] at hz
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one,
      map_zero, Finsupp.zero_apply] at hz
    exact hz
  · intro q _ hqp
    exact False.elim (hqp (he q))
  · intro hn
    exact False.elim (hn (Finset.mem_univ p))

/-- A maximal self-pair coefficient vanishes when every other hook is smaller. -/
private theorem coeff_zero_of_self_with_smaller (R : Type*) [CommRing R]
    (θ τ : YoungDiagram) (hτ : τ ≠ ⊥) (c : splittings θ → R)
    (p0 : splittings θ) (hp0 : p0.val = s(τ, τ))
    (hsmall : ∀ (q : splittings θ), q ≠ p0 → c q ≠ 0 → ∀ μ ∈ (q : Sym2 YoungDiagram),
      μ = ⊥ ∨ μ.rowLen 0 + μ.colLen 0 - 1 < τ.rowLen 0 + τ.colLen 0 - 1)
    (hrel : (∑ q : splittings θ, c q • schurPairProduct R q.val) = 0) : c p0 = 0 := by
  classical
  let T := {q : splittings θ // q ≠ p0}
  let e := (Fintype.equivFin T).symm
  let u := Fintype.card T
  let d (i : Fin u) := c (e i).val
  let α (i : Fin u) := if d i = 0 then ⊥ else (e i).val.val.out.1
  let β (i : Fin u) := if d i = 0 then ⊥ else (e i).val.val.out.2
  have hα (i : Fin u) : α i = ⊥ ∨
      (α i).rowLen 0 + (α i).colLen 0 - 1 < τ.rowLen 0 + τ.colLen 0 - 1 := by
    by_cases hz : d i = 0
    · exact Or.inl (ite_eq_left hz)
    · rw [show α i = (e i).val.val.out.1 from ite_eq_right hz]
      exact hsmall (e i).val (e i).property hz _ (Sym2.out_fst_mem _)
  have hβ (i : Fin u) : β i = ⊥ ∨
      (β i).rowLen 0 + (β i).colLen 0 - 1 < τ.rowLen 0 + τ.colLen 0 - 1 := by
    by_cases hz : d i = 0
    · exact Or.inl (ite_eq_left hz)
    · rw [show β i = (e i).val.val.out.2 from ite_eq_right hz]
      exact hsmall (e i).val (e i).property hz _ (Sym2.out_snd_mem _)
  have hi (i : Fin u) : d i • (schur R (α i) * schur R (β i)) =
      c (e i).val • schurPairProduct R (e i).val.val := by
    by_cases hz : d i = 0
    · change d i • _ = d i • _
      rw [hz, zero_smul, zero_smul]
    · rw [show α i = (e i).val.val.out.1 from ite_eq_right hz,
        show β i = (e i).val.val.out.2 from ite_eq_right hz]
      congr 1
      conv_rhs => rw [← Quot.out_eq (e i).val.val]
      rfl
  have htail := Fintype.sum_equiv e
    (fun i => d i • (schur R (α i) * schur R (β i)))
    (fun q : T => c q.val • schurPairProduct R q.val.val) hi
  let : Fintype {q : splittings θ // q = p0} := Subtype.fintype _
  have hfirst : (∑ q : {q : splittings θ // q = p0},
      c q.val • schurPairProduct R q.val.val) = c p0 • schur R τ ^ 2 := by
    rw [Finset.sum_eq_single (⟨p0, rfl⟩ : {q : splittings θ // q = p0})]
    · rw [hp0, schurPairProduct_mk, pow_two]
    · intro q _ hq
      exact False.elim (hq (Subtype.ext q.property))
    · intro hn
      exact False.elim (hn (Finset.mem_univ _))
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun q : splittings θ => q = p0)
    (fun q => c q • schurPairProduct R q.val)
  change (∑ q : {q : splittings θ // q = p0}, c q.val • schurPairProduct R q.val.val) +
    (∑ q : T, c q.val • schurPairProduct R q.val.val) = _ at hsplit
  rw [hfirst, ← htail] at hsplit
  have hz := coeff_eq_zero_of_maximal_self_pair R τ hτ u (c p0) d α β hα hβ
    (hsplit.trans hrel)
  exact hz

/-- Schur products indexed by unordered componentwise splittings are linearly independent. -/
theorem splitting_linearIndependent (R : Type*) [CommRing R] (θ : YoungDiagram) :
    LinearIndependent R (fun p : splittings θ => schurPairProduct R (p : Sym2 YoungDiagram)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hrel p
  by_contra hp
  by_cases hθ : θ = ⊥
  · subst θ
    exact hp (coeff_zero_of_empty_splitting R c hrel p)
  · let S := Finset.univ.filter (fun q : splittings θ => c q ≠ 0)
    let D := S.biUnion (fun q => q.val.toFinset.erase ⊥)
    have hD : D.Nonempty := by
      obtain ⟨α, β, he, hs⟩ := (mem_splittings θ p.val).mp p.property
      have hα : α ≠ ⊥ ∨ β ≠ ⊥ := by
        by_contra h
        push Not at h
        rw [h.1, h.2, ← YoungDiagram.zero_eq_bot, zero_add] at hs
        exact hθ hs.symm
      rcases hα with hα | hβ
      · refine ⟨α, Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hp⟩, Finset.mem_erase.mpr ⟨hα, ?_⟩⟩⟩
        rw [Sym2.mem_toFinset, he]
        exact Sym2.mem_mk_left _ _
      · refine ⟨β, Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hp⟩, Finset.mem_erase.mpr ⟨hβ, ?_⟩⟩⟩
        rw [Sym2.mem_toFinset, he]
        exact Sym2.mem_mk_right _ _
    obtain ⟨τ, hτD, hmax⟩ := D.exists_max_image
      (fun μ : YoungDiagram => μ.rowLen 0 + μ.colLen 0 - 1) hD
    obtain ⟨p0, hp0S, hτp0⟩ := Finset.mem_biUnion.mp hτD
    have hτ : τ ≠ ⊥ := (Finset.mem_erase.mp hτp0).1
    have hτmem : τ ∈ (p0 : Sym2 YoungDiagram) :=
      Sym2.mem_toFinset.mp (Finset.mem_erase.mp hτp0).2
    have hc0 : c p0 ≠ 0 := (Finset.mem_filter.mp hp0S).2
    have hrow : 0 < τ.rowLen 0 :=
      Nat.pos_of_ne_zero ((YoungDiagram.eq_bot_iff_rowLen_zero τ).not.mp hτ)
    have hcol : 0 < τ.colLen 0 :=
      Nat.pos_of_ne_zero ((YoungDiagram.eq_bot_iff_colLen_zero τ).not.mp hτ)
    let n : ℕ+ := ⟨τ.rowLen 0 + τ.colLen 0 - 1, by omega⟩
    have hbound (q : splittings θ) (hq : c q ≠ 0) (μ : YoungDiagram)
        (hμ : μ ∈ (q : Sym2 YoungDiagram)) :
        μ = ⊥ ∨ μ.rowLen 0 + μ.colLen 0 - 1 ≤ n.val := by
      by_cases hz : μ = ⊥
      · exact Or.inl hz
      · apply Or.inr
        apply hmax μ
        exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hq⟩, Finset.mem_erase.mpr ⟨hz, Sym2.mem_toFinset.mpr hμ⟩⟩
    have hzero (q : splittings θ) (γ δ : YoungDiagram) (he : q.val = s(γ, δ))
        (hδ : δ ≠ ⊥) (hn : δ.rowLen 0 + δ.colLen 0 - 1 = n.val)
        (hne : γ ≠ δ) : c q = 0 := by
      have hs : γ + δ = θ := (mk_mem_splittings θ _ _).mp (he ▸ q.property)
      let t : orientedSplittings θ (n.val : ℤ) :=
        ⟨(γ, δ), (mem_orientedSplittings _ _ _).mpr ⟨hs, hδ, by exact_mod_cast hn⟩⟩
      have hz := coeff_zero_of_unequal_max_hook n c hbound hrel t hne
      have hq : (⟨s(γ, δ), (mk_mem_splittings θ _ _).mpr hs⟩ : splittings θ) = q :=
        Subtype.ext he.symm
      simpa only [t, hq] using hz
    obtain ⟨γ, hγ⟩ := Sym2.mem_iff_exists.mp hτmem
    have hp0 : p0.val = s(γ, τ) := hγ.trans Sym2.eq_swap
    have hγτ : γ = τ := by
      by_contra h
      exact hc0 (hzero p0 γ τ hp0 hτ rfl h)
    rw [hγτ] at hp0
    have hsumτ : τ + τ = θ := (mk_mem_splittings θ _ _).mp (hp0 ▸ p0.property)
    have hsmall (q : splittings θ) (hq : q ≠ p0) (hcq : c q ≠ 0)
        (μ : YoungDiagram) (hμ : μ ∈ (q : Sym2 YoungDiagram)) :
        μ = ⊥ ∨ μ.rowLen 0 + μ.colLen 0 - 1 < n.val := by
      rcases hbound q hcq μ hμ with hz | hb
      · exact Or.inl hz
      · by_cases hz : μ = ⊥
        · exact Or.inl hz
        · apply Or.inr
          by_contra hn
          have heq : μ.rowLen 0 + μ.colLen 0 - 1 = n.val := by omega
          obtain ⟨γ, he⟩ := Sym2.mem_iff_exists.mp hμ
          have he' : q.val = s(γ, μ) := he.trans Sym2.eq_swap
          by_cases hγ : γ = μ
          · have hs : μ + μ = τ + τ := by
              have hs := (mk_mem_splittings θ _ _).mp (he' ▸ q.property)
              rw [hγ] at hs
              exact hs.trans hsumτ.symm
            have hμτ : μ = τ := by
              apply YoungDiagram.rowLen_injective
              funext i
              have hr := congrArg (fun ρ : YoungDiagram => ρ.rowLen i) hs
              simp only [YoungDiagram.rowLen_add] at hr
              omega
            apply hq
            apply Subtype.ext
            rw [he', hγ, hμτ, hp0]
          · exact hcq (hzero q γ μ he' hz heq hγ)
    exact hc0 (coeff_zero_of_self_with_smaller R θ τ hτ c p0 hp0 hsmall hrel)

end ComplementaryProducts
