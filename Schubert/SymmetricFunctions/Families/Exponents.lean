import Schubert.Partitions.Basic
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Monomial
import Mathlib.Logic.Equiv.Fintype
import Schubert.SymmetricFunctions.ForMathlib.WeightMultisets

/-! # Young diagrams of exponent vectors

Sorting the nonzero exponents gives a Young diagram. Two exponent vectors have the same
diagram exactly when a permutation of the variables carries one to the other.

## Main results

* `exponentDiagram_eq_iff` characterizes equality by multisets of positive exponents.
* `exponentDiagram_eq_iff_perm` characterizes equality by a permutation of variables.
* `exponentDiagram_rowExponent` recovers a diagram from its canonical exponent vector.
-/

noncomputable section

namespace SymmetricFunction

/-- The Young diagram whose parts are the nonzero exponents of a monomial. -/
def exponentDiagram (d : ℕ →₀ ℕ) : YoungDiagram :=
  TauCeti.diagramOf (TauCeti.weightPartition d rfl)

/-- The exponent diagram has as many cells as the total degree. -/
@[simp]
theorem card_exponentDiagram (d : ℕ →₀ ℕ) : (exponentDiagram d).card = d.degree :=
  TauCeti.card_diagramOf _

/-- The rows of the exponent diagram are the decreasingly sorted nonzero exponents. -/
theorem rowLens_exponentDiagram (d : ℕ →₀ ℕ) :
    (exponentDiagram d).rowLens = (Multiset.map d d.support.val).sort (· ≥ ·) := by
  rw [exponentDiagram, TauCeti.rowLens_diagramOf, TauCeti.weightPartition_parts]

/-- Equal exponent diagrams are equivalent to equal multisets of nonzero exponents. -/
theorem exponentDiagram_eq_iff (d e : ℕ →₀ ℕ) :
    exponentDiagram d = exponentDiagram e ↔
      Multiset.map d d.support.val = Multiset.map e e.support.val := by
  constructor
  · intro h
    have hs := congrArg YoungDiagram.rowLens h
    rw [rowLens_exponentDiagram, rowLens_exponentDiagram] at hs
    have hc := congrArg (fun l : List ℕ => (l : Multiset ℕ)) hs
    simpa only [Multiset.sort_eq] using hc
  · intro h
    apply YoungDiagram.equivListRowLens.injective
    apply Subtype.ext
    change (exponentDiagram d).rowLens = (exponentDiagram e).rowLens
    rw [rowLens_exponentDiagram, rowLens_exponentDiagram, h]

/-- Permuting variables does not change the exponent diagram. -/
@[simp]
theorem exponentDiagram_mapDomain (d : ℕ →₀ ℕ) (e : Equiv.Perm ℕ) :
    exponentDiagram (d.mapDomain e) = exponentDiagram d := by
  apply (exponentDiagram_eq_iff _ _).mpr
  change Multiset.map (d.mapDomain e.toEmbedding) (d.mapDomain e.toEmbedding).support.val = _
  rw [Finsupp.support_mapDomain_embedding, Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  exact Finsupp.mapDomain_apply_of_injective e.injective d i

/-- Embedding an alphabet preserves the partition of the nonzero exponents. -/
theorem exponentDiagram_embDomain {σ : Type*} [DecidableEq σ] {k : ℕ}
    (e : σ ↪ ℕ) (d : σ →₀ ℕ) (h : d.degree = k) :
    exponentDiagram (Finsupp.embDomain e d) = TauCeti.diagramOf (TauCeti.weightPartition d h) := by
  apply YoungDiagram.equivListRowLens.injective
  apply Subtype.ext
  change (exponentDiagram (Finsupp.embDomain e d)).rowLens =
    (TauCeti.diagramOf (TauCeti.weightPartition d h)).rowLens
  rw [rowLens_exponentDiagram, TauCeti.rowLens_diagramOf, TauCeti.weightPartition_parts]
  apply congrArg (fun s : Multiset ℕ => s.sort (· ≥ ·))
  rw [Finsupp.embDomain_eq_mapDomain, Finsupp.support_mapDomain_embedding,
    Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  exact Finsupp.mapDomain_apply_of_injective e.injective d i

/-- The canonical exponent vector records the row lengths at consecutive variables. -/
def rowExponent (μ : YoungDiagram) : ℕ →₀ ℕ :=
  Finsupp.mapDomain Fin.val (TauCeti.rowLenWeight (μ.colLen 0) μ)

/-- The canonical exponent at each variable is the corresponding row length. -/
@[simp]
theorem rowExponent_apply (μ : YoungDiagram) (i : ℕ) : rowExponent μ i = μ.rowLen i :=
  congrFun (TauCeti.mapDomain_rowLenWeight (μ := μ) (le_refl (μ.colLen 0))) i

/-- The support of the canonical row exponent is the range of nonempty rows. -/
@[simp]
theorem support_rowExponent (μ : YoungDiagram) :
    (rowExponent μ).support = Finset.range (μ.colLen 0) := by
  ext i
  rw [Finsupp.mem_support_iff, rowExponent_apply, Finset.mem_range]
  rw [← Nat.pos_iff_ne_zero, ← YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_colLen]

/-- The canonical row exponent recovers its Young diagram. -/
@[simp]
theorem exponentDiagram_rowExponent (μ : YoungDiagram) : exponentDiagram (rowExponent μ) = μ := by
  apply YoungDiagram.equivListRowLens.injective
  apply Subtype.ext
  change (exponentDiagram (rowExponent μ)).rowLens = μ.rowLens
  rw [rowLens_exponentDiagram, support_rowExponent]
  have hp : Multiset.map (rowExponent μ) (Finset.range (μ.colLen 0)).val = μ.rowLens := by
    simp only [Finset.range_val, Multiset.range, Multiset.map_coe,
      YoungDiagram.rowLens]
    rw [show ⇑(rowExponent μ) = μ.rowLen from funext (rowExponent_apply μ)]
  rw [hp, YoungDiagram.sort_coe_rowLens]

/-- The total degree of the row exponent is the size of its diagram. -/
@[simp]
theorem degree_rowExponent (μ : YoungDiagram) : (rowExponent μ).degree = μ.card := by
  rw [← card_exponentDiagram, exponentDiagram_rowExponent]

/-- The canonical exponent of the empty diagram is zero. -/
@[simp]
theorem rowExponent_bot : rowExponent ⊥ = 0 := by
  ext i
  rw [rowExponent_apply, YoungDiagram.rowLen_bot, Finsupp.zero_apply]

/-- The zero exponent has empty diagram. -/
@[simp]
theorem exponentDiagram_zero : exponentDiagram 0 = ⊥ := by
  rw [← rowExponent_bot, exponentDiagram_rowExponent]

/-- Only the zero exponent has empty diagram. -/
@[simp]
theorem exponentDiagram_eq_bot_iff (d : ℕ →₀ ℕ) : exponentDiagram d = ⊥ ↔ d = 0 := by
  constructor
  · intro h
    apply (Finsupp.degree_eq_zero_iff d).mp
    have hc := congrArg YoungDiagram.card h
    rw [card_exponentDiagram, ← exponentDiagram_zero, card_exponentDiagram] at hc
    simpa only [map_zero] using hc
  · rintro rfl
    exact exponentDiagram_zero

/-- Equal multisets of exponents admit a support equivalence preserving exponent values. -/
private theorem supportEquiv_exists (d e : ℕ →₀ ℕ)
    (h : Multiset.map d d.support.val = Multiset.map e e.support.val) :
    ∃ q : d.support ≃ e.support, ∀ x : d.support, e (q x) = d x := by
  classical
  apply Fintype.exists_equiv_of_weightMultiset (fun x : d.support => d x)
    (fun x : e.support => e x)
  rw [Finset.univ_eq_attach, Finset.univ_eq_attach, Finset.attach_val, Finset.attach_val]
  change (d.support.val.attach.map fun x => d x.val) =
    (e.support.val.attach.map fun x => e x.val)
  rw [Multiset.attach_map_val', Multiset.attach_map_val']
  exact h

/-- Exponent diagrams classify monomials up to permutation of the variables. -/
theorem exponentDiagram_eq_iff_perm (d e : ℕ →₀ ℕ) :
    exponentDiagram d = exponentDiagram e ↔
      ∃ q : Equiv.Perm ℕ, d.mapDomain q = e := by
  classical
  constructor
  · intro h
    obtain ⟨q, hq⟩ := supportEquiv_exists d e ((exponentDiagram_eq_iff d e).mp h)
    let p : Equiv.Perm ℕ := q.extendSubtype
    refine ⟨p, ?_⟩
    ext i
    obtain ⟨j, rfl⟩ := p.surjective i
    rw [Finsupp.mapDomain_apply_of_injective p.injective]
    by_cases hj : j ∈ d.support
    · have hp : p j = (q ⟨j, hj⟩ : ℕ) := q.extendSubtype_apply_of_mem j hj
      rw [hp]
      exact (hq ⟨j, hj⟩).symm
    · have hp : p j ∉ e.support := q.extendSubtype_not_mem j hj
      rw [Finsupp.notMem_support_iff.mp hj, Finsupp.notMem_support_iff.mp hp]
  · rintro ⟨q, rfl⟩
    exact (exponentDiagram_mapDomain d q).symm

end SymmetricFunction
