import Mathlib.GroupTheory.Perm.DomMulAct

/-! # Equivalences preserving finite weight multisets

These declarations extend Mathlib's finite-type equivalence API.

## Main results

* `Fintype.exists_equiv_of_weightMultiset` realizes equality of weight multisets.
-/

noncomputable section

namespace Fintype

/-- A weight fiber has the multiplicity of its weight. -/
theorem card_weightFiber {α β : Type*} [Fintype α]
    [DecidableEq β] (a : α → β) (r : β) :
    Fintype.card {i : α // a i = r} = (Finset.univ.val.map a).count r := by
  rw [Fintype.card_subtype, Multiset.count_map]
  simp only [Finset.card, Finset.filter_val, eq_comm]

/-- Equal finite weight multisets admit a weight-preserving equivalence. -/
theorem exists_equiv_of_weightMultiset {α β : Type*} [Fintype α]
    [Fintype β] (a : α → ℕ) (b : β → ℕ)
    (h : Finset.univ.val.map a = Finset.univ.val.map b) :
    ∃ e : α ≃ β, ∀ i, b (e i) = a i := by
  have hc (r : ℕ) : Fintype.card {i : α // a i = r} =
      Fintype.card {j : β // b j = r} := by
    rw [card_weightFiber, card_weightFiber, h]
  let E (r : ℕ) : {i : α // a i = r} ≃ {j : β // b j = r} :=
    Fintype.equivOfCardEq (hc r)
  exact ⟨Equiv.ofFiberEquiv E, fun i => Equiv.ofFiberEquiv_map E i⟩

end Fintype
