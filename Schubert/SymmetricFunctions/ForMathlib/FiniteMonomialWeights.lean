import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Monomial
import Schubert.SymmetricFunctions.ForMathlib.WeightMultisets
import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# Labelled weights of finite monomial symmetric polynomials

Injective assignments of labelled positive row weights count each monomial according to
the factorials of the multiplicities of its repeated row lengths.

These declarations extend Mathlib's algebra APIs.

## Main results

* `MvPolynomial.prod_embedding_eq_monomial` records the exponent of an injective assignment.
* `MvPolynomial.coeff_sum_embeddings` counts assignments with a prescribed exponent.
* `MvPolynomial.sum_embeddings_eq_msymm` gives the finite labelled normalization.
-/

noncomputable section

namespace MvPolynomial

variable {R ι σ : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ]

omit [DecidableEq ι] [Fintype σ] [DecidableEq σ] in
/-- An injective assignment of positive weights has their pushed-forward exponent vector. -/
theorem prod_embedding_eq_monomial (w : ι →₀ ℕ) (hw : w.support = Finset.univ)
    (f : ι ↪ σ) :
    (∏ i, X (f i) ^ w i : MvPolynomial σ R) = monomial (w.mapDomain f) 1 := by
  have he := congrArg (rename (R := R) f) (prod_X_pow_eq_monomial (R := R) (s := w))
  rw [hw, map_prod, rename_monomial] at he
  simpa only [map_pow, rename_X] using he

omit [DecidableEq ι] in
/-- The coefficient of the labelled injective sum counts its exponent fiber. -/
theorem coeff_sum_embeddings (w : ι →₀ ℕ) (hw : w.support = Finset.univ) (d : σ →₀ ℕ) :
    (∑ f : ι ↪ σ, ∏ i, X (f i) ^ w i : MvPolynomial σ R).coeff d =
      (Fintype.card {f : ι ↪ σ // w.mapDomain f = d} : R) := by
  simp only [coeff_sum, prod_embedding_eq_monomial w hw, coeff_monomial]
  rw [Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f _
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, eq_comm]

private def fiberSupportEquiv (w : ι →₀ ℕ) (hw : w.support = Finset.univ)
    (d : σ →₀ ℕ) (f : {f : ι ↪ σ // w.mapDomain f = d}) : ι ≃ d.support :=
  Equiv.ofBijective
    (fun i => ⟨f.val i, by
      have hs := congrArg Finsupp.support f.property
      rw [Finsupp.support_mapDomain_embedding, hw] at hs
      rw [← hs]
      simp⟩)
    ⟨fun i j h => f.val.injective (congrArg Subtype.val h), by
      intro x
      have hx := x.property
      have hs := congrArg Finsupp.support f.property
      rw [Finsupp.support_mapDomain_embedding, hw] at hs
      have hx' := Eq.mpr (congrArg (fun s : Finset σ => x.val ∈ s) hs) hx
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hx'
      exact ⟨i, Subtype.ext hi⟩⟩

omit [DecidableEq ι] [Fintype σ] [DecidableEq σ] in
private theorem fiberSupportEquiv_value (w : ι →₀ ℕ) (hw : w.support = Finset.univ)
    (d : σ →₀ ℕ) (f : {f : ι ↪ σ // w.mapDomain f = d}) (i : ι) :
    d (fiberSupportEquiv w hw d f i) = w i := by
  change d (f.val i) = w i
  exact (congrArg (fun e : σ →₀ ℕ => e (f.val i)) f.property).symm.trans
    (Finsupp.mapDomain_apply_of_injective f.val.injective w i)

private def embeddingOfSupportEquiv (d : σ →₀ ℕ) (e : ι ≃ d.support) : ι ↪ σ :=
  e.toEmbedding.trans (Function.Embedding.subtype _)

omit [Fintype ι] [DecidableEq ι] [Fintype σ] in
private theorem mapDomain_embeddingOfSupportEquiv (w : ι →₀ ℕ) (d : σ →₀ ℕ)
    (e : ι ≃ d.support) (he : ∀ i, d (e i) = w i) :
    w.mapDomain (embeddingOfSupportEquiv d e) = d := by
  ext x
  by_cases hx : x ∈ d.support
  · let i := e.symm ⟨x, hx⟩
    have hi : embeddingOfSupportEquiv d e i = x := by
      change (e (e.symm ⟨x, hx⟩)).val = x
      rw [e.apply_symm_apply]
    rw [← hi, Finsupp.mapDomain_apply_of_injective
      (embeddingOfSupportEquiv d e).injective]
    exact (he i).symm
  · have hn : x ∉ (w.mapDomain (embeddingOfSupportEquiv d e)).support := by
      rw [Finsupp.support_mapDomain_embedding]
      intro hm
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hm
      apply hx
      rw [← hi]
      exact (e i).property
    rw [Finsupp.notMem_support_iff.mp hn, Finsupp.notMem_support_iff.mp hx]

private def exponentFiberEquiv (w : ι →₀ ℕ) (hw : w.support = Finset.univ)
    (d : σ →₀ ℕ) :
    {f : ι ↪ σ // w.mapDomain f = d} ≃ {e : ι ≃ d.support // ∀ i, d (e i) = w i} where
  toFun f := ⟨fiberSupportEquiv w hw d f, fiberSupportEquiv_value w hw d f⟩
  invFun e := ⟨embeddingOfSupportEquiv d e.val,
    mapDomain_embeddingOfSupportEquiv w d e.val e.property⟩
  left_inv f := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply Subtype.ext
    rfl

private def preservingEquivPerm {α β : Type*} (a : α → ℕ) (b : β → ℕ)
    (e₀ : α ≃ β) (he₀ : ∀ i, b (e₀ i) = a i) :
    {e : α ≃ β // ∀ i, b (e i) = a i} ≃ {p : Equiv.Perm α // a ∘ p = a} where
  toFun e := ⟨e.val.trans e₀.symm, by
    funext i
    change a (e₀.symm (e.val i)) = a i
    rw [← he₀, e₀.apply_symm_apply, e.property]⟩
  invFun p := ⟨p.val.trans e₀, by
    intro i
    change b (e₀ (p.val i)) = a i
    rw [he₀]
    exact congrFun p.property i⟩
  left_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact e₀.apply_symm_apply _
  right_inv p := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact e₀.symm_apply_apply _

private theorem card_exponentFiber (w : ι →₀ ℕ) (hw : w.support = Finset.univ)
    (d : σ →₀ ℕ) (h : Nonempty {f : ι ↪ σ // w.mapDomain f = d}) :
    Fintype.card {f : ι ↪ σ // w.mapDomain f = d} =
      ∏ r ∈ Finset.univ.image w, (Fintype.card {i : ι // w i = r}).factorial := by
  let f := h.some
  let e₀ := fiberSupportEquiv w hw d f
  rw [Fintype.card_congr (exponentFiberEquiv w hw d),
    Fintype.card_congr (preservingEquivPerm w (fun x : d.support => d x) e₀
      (fiberSupportEquiv_value w hw d f))]
  exact DomMulAct.stabilizer_card' w

omit [Fintype σ] [DecidableEq ι] in
private theorem exponentFiber_nonempty_iff (w : ι →₀ ℕ) (hw : w.support = Finset.univ)
    (d : σ →₀ ℕ) :
    Nonempty {f : ι ↪ σ // w.mapDomain f = d} ↔
      Finset.univ.val.map w = d.support.val.map d := by
  constructor
  · rintro ⟨f⟩
    have he := congrArg (fun q : σ →₀ ℕ => q.support.val.map q) f.property
    rw [Finsupp.support_mapDomain_embedding, hw, Finset.map_val, Multiset.map_map] at he
    have hh : Finset.univ.val.map (fun i => (w.mapDomain f.val) (f.val i)) =
        Finset.univ.val.map w := by
      apply Multiset.map_congr rfl
      intro i _
      exact Finsupp.mapDomain_apply_of_injective f.val.injective w i
    exact hh.symm.trans he
  · intro h
    have ht : Finset.univ.val.map (fun x : d.support => d x) = d.support.val.map d := by
      rw [Finset.univ_eq_attach]
      exact Multiset.attach_map_val' _ _
    obtain ⟨e, he⟩ := Fintype.exists_equiv_of_weightMultiset w
      (fun x : d.support => d x) (h.trans ht.symm)
    exact ⟨⟨embeddingOfSupportEquiv d e, mapDomain_embeddingOfSupportEquiv w d e he⟩⟩

/-- Every labelled injective exponent fiber has its multiplicity-factorial cardinality. -/
theorem coeff_sum_embeddings_eq (w : ι →₀ ℕ) (hw : w.support = Finset.univ)
    (d : σ →₀ ℕ) :
    (∑ f : ι ↪ σ, ∏ i, X (f i) ^ w i : MvPolynomial σ R).coeff d =
      if Finset.univ.val.map w = d.support.val.map d then
        (∏ r ∈ Finset.univ.image w, (Fintype.card {i : ι // w i = r}).factorial : ℕ) else 0 := by
  classical
  rw [coeff_sum_embeddings w hw]
  by_cases h : Finset.univ.val.map w = d.support.val.map d
  · rw [ite_eq_left h, card_exponentFiber w hw d ((exponentFiber_nonempty_iff w hw d).mpr h)]
  · rw [ite_eq_right h]
    have : IsEmpty {f : ι ↪ σ // w.mapDomain f = d} :=
      not_nonempty_iff.mp (fun hf => h ((exponentFiber_nonempty_iff w hw d).mp hf))
    rw [Fintype.card_of_isEmpty, Nat.cast_zero]

/-- Summing labelled injective weights gives a monomial polynomial times its multiplicity count. -/
theorem sum_embeddings_eq_msymm (w : ι →₀ ℕ) (hw : w.support = Finset.univ) :
    (∑ f : ι ↪ σ, ∏ i, X (f i) ^ w i : MvPolynomial σ R) =
      (∏ r ∈ Finset.univ.image w, (Fintype.card {i : ι // w i = r}).factorial : ℕ) •
        msymm σ R (TauCeti.weightPartition w rfl) := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_sum_embeddings_eq w hw, coeff_smul]
  by_cases hd : d.degree = w.degree
  · rw [TauCeti.coeff_msymm R _ hd]
    have he : TauCeti.weightPartition d hd = TauCeti.weightPartition w rfl ↔
        Finset.univ.val.map w = d.support.val.map d := by
      rw [Nat.Partition.ext_iff, TauCeti.weightPartition_parts, TauCeti.weightPartition_parts,
        hw, eq_comm]
    simp only [he]
    split_ifs <;> simp
  · rw [TauCeti.coeff_msymm_eq_zero_of_degree_ne R _ hd, smul_zero]
    rw [Nat.cast_ite, Nat.cast_zero]
    apply ite_eq_right
    intro he
    apply hd
    have hs := congrArg Multiset.sum he
    simpa only [← hw, Finset.sum_eq_multiset_sum, Finsupp.degree_apply] using hs.symm

/-- A prescribed part multiset identifies the monomial polynomial of labelled weights. -/
theorem sum_embeddings_eq_msymm_of_parts {n : ℕ} (w : ι →₀ ℕ)
    (hw : w.support = Finset.univ) (ν : n.Partition)
    (hν : ν.parts = Finset.univ.val.map w) :
    (∑ f : ι ↪ σ, ∏ i, X (f i) ^ w i : MvPolynomial σ R) =
      (∏ r ∈ Finset.univ.image w, (Fintype.card {i : ι // w i = r}).factorial : ℕ) •
        msymm σ R ν := by
  classical
  have hn : w.degree = n := by
    have hs := ν.parts_sum
    rw [hν, ← hw] at hs
    simpa only [Finset.sum_eq_multiset_sum, Finsupp.degree_apply] using hs
  subst n
  have hp : ν = TauCeti.weightPartition w rfl := by
    rw [Nat.Partition.ext_iff, TauCeti.weightPartition_parts, hw]
    exact hν
  rw [hp]
  exact sum_embeddings_eq_msymm w hw

end MvPolynomial
