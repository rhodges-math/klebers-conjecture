import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.Finset.Max

/-!
# Bases from degree-lowering corrections

A family differing from a basis only in strictly smaller natural degrees is again a basis.

These declarations extend Mathlib's algebra APIs.

## Main results

* `Module.Basis.exists_basis_of_degree_lowering` constructs the normalized basis.
-/

noncomputable section

namespace Module.Basis

/-- Corrections supported in strictly smaller degrees preserve a basis. -/
theorem exists_basis_of_degree_lowering {R M ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (b : Basis ι R M) (d : ι → ℕ) (w : ι → M)
    (h : ∀ i j, d i ≤ d j → b.repr (w i - b i) j = 0) :
    ∃ B : Basis ι R M, ∀ i, B i = w i := by
  classical
  have hli : LinearIndependent R w := by
    rw [linearIndependent_iff]
    intro c hc
    by_contra hn
    have hs : c.support.Nonempty := Finsupp.support_nonempty_iff.mpr hn
    obtain ⟨j, hj, hmax⟩ := c.support.exists_max_image d hs
    have hw (i : ι) (hi : i ∈ c.support) :
        b.repr (w i) j = b.repr (b i) j := by
      have hz := h i j (hmax i hi)
      simpa only [map_sub, Finsupp.sub_apply, sub_eq_zero] using hz
    have he := congrArg (b.coord j) hc
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
      map_zero, Basis.coord_apply] at he
    have he' : c j = 0 := by
      rw [Finset.sum_congr rfl (fun i hi => congrArg (c i • ·) (hw i hi))] at he
      simpa only [b.repr_self_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', ite_eq_left hj] using he
    exact (Finsupp.mem_support_iff.mp hj) he'
  let S := Submodule.span R (Set.range w)
  have hb : ∀ n i, d i = n → b i ∈ S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      have hcorr : w i - b i ∈ S := by
        rw [← b.linearCombination_repr (w i - b i), Finsupp.linearCombination_apply,
          Finsupp.sum]
        apply Submodule.sum_mem
        intro j hj
        apply Submodule.smul_mem
        have hjne := Finsupp.mem_support_iff.mp hj
        have hlt : d j < n := by
          by_contra hn
          exact hjne (h i j (by omega))
        exact ih (d j) hlt j rfl
      have hwi : w i ∈ S := Submodule.subset_span ⟨i, rfl⟩
      simpa only [sub_sub_cancel] using S.sub_mem hwi hcorr
  have hsp : ⊤ ≤ Submodule.span R (Set.range w) := by
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hb (d i) i rfl
  exact ⟨Basis.mk hli hsp, fun i => Basis.mk_apply hli hsp i⟩

end Module.Basis
