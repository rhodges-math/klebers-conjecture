import Schubert.ComplementaryProducts.Oriented
import Schubert.SymmetricFunctions.Projection.FirstRowProducts
import Mathlib.Data.Finset.Max

/-! # Independence of ordered corner-deleted splitting products

First-row projection reduces a maximal supported block to the corresponding ordered family
on the row-deleted target. The fixed hook index recovers the omitted row uniquely.

## Main results

* `oriented_linearIndependent` proves independence at every integer hook index.

## Implementation notes

The induction is organized by the target height. Row deletion embeds each maximal-width
block into a smaller-height ordered family; projection eliminates the other blocks.
The remaining one-row second factor is unique and is isolated by its Schur coordinate.
-/

noncomputable section

namespace ComplementaryProducts

open SymmetricFunction

private theorem tail_injective (θ : YoungDiagram) (n : ℤ) :
    Function.Injective (fun q : orientedSplittings θ n =>
      (q.val.1.dropRows 1, q.val.2.dropRows 1)) := by
  intro p q he
  have hp := (mem_orientedSplittings θ n p.val).mp p.property
  have hq := (mem_orientedSplittings θ n q.val).mp q.property
  have hpcol : 0 < p.val.2.colLen 0 := by
    by_contra h
    exact hp.2.1 ((YoungDiagram.eq_bot_iff_colLen_zero _).mpr (by omega))
  have hqcol : 0 < q.val.2.colLen 0 := by
    by_contra h
    exact hq.2.1 ((YoungDiagram.eq_bot_iff_colLen_zero _).mpr (by omega))
  have ht := congrArg Prod.snd he
  have hc := congrArg (fun μ : YoungDiagram => μ.colLen 0) ht
  rw [YoungDiagram.colLen_dropRows, YoungDiagram.colLen_dropRows] at hc
  have hcols : p.val.2.colLen 0 = q.val.2.colLen 0 := by omega
  have hrows : p.val.2.rowLen 0 = q.val.2.rowLen 0 := by omega
  have hb : p.val.2 = q.val.2 := by
    apply YoungDiagram.rowLen_injective
    funext i
    cases i with
    | zero => exact hrows
    | succ i =>
      have hr := congrArg (fun μ : YoungDiagram => μ.rowLen i) ht
      simpa only [YoungDiagram.rowLen_dropRows, Nat.add_comm 1] using hr
  have ha : p.val.1 = q.val.1 := by
    apply YoungDiagram.rowLen_injective
    funext i
    have hr := congrArg (fun μ : YoungDiagram => μ.rowLen i) (hp.1.trans hq.1.symm)
    rw [YoungDiagram.rowLen_add, YoungDiagram.rowLen_add, hb] at hr
    omega
  apply Subtype.ext
  exact Prod.ext ha hb

private theorem long_row_pos {β : YoungDiagram} (hβ : 2 ≤ β.colLen 0) :
    0 < β.rowLen 1 := by
  apply YoungDiagram.mem_iff_lt_rowLen.mp
  exact YoungDiagram.mem_iff_lt_colLen.mpr (by omega : 1 < β.colLen 0)

private theorem short_eq (θ : YoungDiagram) (n : ℤ) (p q : orientedSplittings θ n)
    (hp : p.val.2.colLen 0 ≤ 1) (hq : q.val.2.colLen 0 ≤ 1) : p = q := by
  apply tail_injective θ n
  have hp' := (mem_orientedSplittings θ n p.val).mp p.property
  have hq' := (mem_orientedSplittings θ n q.val).mp q.property
  have hp0 := YoungDiagram.dropRows_eq_bot hp
  have hq0 := YoungDiagram.dropRows_eq_bot hq
  apply Prod.ext
  · apply YoungDiagram.rowLen_injective
    funext i
    have hr := congrArg (fun μ : YoungDiagram => μ.rowLen (1 + i))
      (hp'.1.trans hq'.1.symm)
    rw [YoungDiagram.rowLen_add, YoungDiagram.rowLen_add,
      YoungDiagram.rowLen_eq_zero_of_colLen_le (hp.trans (by omega)),
      YoungDiagram.rowLen_eq_zero_of_colLen_le (hq.trans (by omega))] at hr
    simpa only [YoungDiagram.rowLen_dropRows, add_zero] using hr
  · change p.val.2.dropRows 1 = q.val.2.dropRows 1
    rw [hp0, hq0]

private theorem short_product (R : Type*) [CommRing R] {θ : YoungDiagram} {n : ℤ}
    (q : orientedSplittings θ n) (hq : q.val.2.colLen 0 ≤ 1) :
    orientedPairProduct R q.val = schur R q.val.1 := by
  have he : q.val.2.removeFirstRowCol = ⊥ := by
    apply YoungDiagram.rowLen_injective
    funext i
    rw [YoungDiagram.rowLen_removeFirstRowCol,
      YoungDiagram.rowLen_eq_zero_of_colLen_le (hq.trans (by omega)),
      YoungDiagram.rowLen_bot, Nat.zero_sub]
  rw [orientedPairProduct_apply, he, schur_bot, mul_one]

/-- The first-row sum after corner deletion in an ordered splitting. -/
private def blockWidth {θ : YoungDiagram} {n : ℤ} (q : orientedSplittings θ n) : ℕ :=
  q.val.1.rowLen 0 + q.val.2.removeFirstRowCol.rowLen 0

/-- Row deletion embeds each long fixed-width block into the induced hook-index family. -/
private def blockTailEmbedding (θ : YoungDiagram) (n : ℤ) (N : ℕ) :
    {q : orientedSplittings θ n // 2 ≤ q.val.2.colLen 0 ∧ blockWidth q = N} ↪
      orientedSplittings (θ.dropRows 1) ((N : ℤ) + n - θ.rowLen 0) where
  toFun q :=
    ⟨(q.val.val.1.dropRows 1, q.val.val.2.dropRows 1), by
      apply (mem_orientedSplittings _ _ _).mpr
      have hp := (mem_orientedSplittings θ n q.val.val).mp q.val.property
      refine ⟨?_, ?_, ?_⟩
      · rw [← YoungDiagram.dropRows_add, hp.1]
      · intro he
        have hb := congrArg (fun μ : YoungDiagram => μ.colLen 0) he
        rw [YoungDiagram.colLen_dropRows, YoungDiagram.colLen_bot] at hb
        have hlong := q.property.1
        omega
      · have hs := congrArg (fun μ : YoungDiagram => μ.rowLen 0) hp.1
        rw [YoungDiagram.rowLen_add] at hs
        have hw := q.property.2
        have hb := long_row_pos q.property.1
        simp only [blockWidth, YoungDiagram.rowLen_removeFirstRowCol, Nat.zero_add] at hw
        simp only [YoungDiagram.rowLen_dropRows, YoungDiagram.colLen_dropRows,
          Nat.add_zero]
        omega⟩
  inj' p q he := by
    apply Subtype.ext
    apply tail_injective θ n
    exact congrArg Subtype.val he

private theorem projection_vanishes (R : Type*) [CommRing R]
    (θ : YoungDiagram) (n : ℤ) (c : orientedSplittings θ n → R) (N : ℕ)
    (hshort : (θ.rowLen 0 : ℤ) < (N : ℤ) + n)
    (hmax : ∀ q, 2 ≤ q.val.2.colLen 0 → c q ≠ 0 → blockWidth q ≤ N)
    (q : orientedSplittings θ n) (hq : ¬(2 ≤ q.val.2.colLen 0 ∧ blockWidth q = N)) :
    c q • firstRowProjection R (N : ℤ) (orientedPairProduct R q.val) = 0 := by
  by_cases hz : c q = 0
  · rw [hz, zero_smul]
  by_cases hl : 2 ≤ q.val.2.colLen 0
  · have hw := hmax q hl hz
    have hn : blockWidth q < N := by
      have hne : blockWidth q ≠ N := fun he => hq ⟨hl, he⟩
      omega
    rw [orientedPairProduct_apply, firstRowProjection_product_above _ _
      (show ((blockWidth q : ℕ) : ℤ) < N by exact_mod_cast hn), smul_zero]
  · have hs : q.val.2.colLen 0 ≤ 1 := by omega
    have hp := (mem_orientedSplittings θ n q.val).mp q.property
    have hcol : q.val.2.colLen 0 = 1 := by
      by_contra h
      exact hp.2.1 ((YoungDiagram.eq_bot_iff_colLen_zero _).mpr (by omega))
    have hsum := congrArg (fun μ : YoungDiagram => μ.rowLen 0) hp.1
    rw [YoungDiagram.rowLen_add] at hsum
    have he : (q.val.1.rowLen 0 : ℤ) ≠ N := by omega
    rw [short_product R q hs, firstRowProjection_schur, ite_eq_right he, smul_zero]

private theorem long_coefficients_eq_zero (R : Type*) [CommRing R]
    (θ : YoungDiagram) (n : ℤ)
    (hind : ∀ ψ : YoungDiagram, ψ.colLen 0 < θ.colLen 0 → ∀ m : ℤ,
      LinearIndependent R (fun q : orientedSplittings ψ m => orientedPairProduct R q.val))
    (c : orientedSplittings θ n → R)
    (hc : ∑ q, c q • orientedPairProduct R q.val = 0) :
    ∀ q, 2 ≤ q.val.2.colLen 0 → c q = 0 := by
  classical
  let Q := ↥(orientedSplittings θ n)
  let w : Q → ℕ := blockWidth
  by_contra h
  push Not at h
  obtain ⟨q, hq, hcq⟩ := h
  let S := Finset.univ.filter (fun q : Q => 2 ≤ q.val.2.colLen 0 ∧ c q ≠ 0)
  have hS : S.Nonempty := ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, hcq⟩⟩
  obtain ⟨q0, hq0S, hmax⟩ := S.exists_max_image w hS
  have hq0 := (Finset.mem_filter.mp hq0S).2
  have hp0 := (mem_orientedSplittings θ n q0.val).mp q0.property
  let N := w q0
  let P (q : Q) := 2 ≤ q.val.2.colLen 0 ∧ w q = N
  let B := {q : Q // P q}
  let m : ℤ := (N : ℤ) + n - θ.rowLen 0
  have hsum0 := congrArg (fun μ : YoungDiagram => μ.rowLen 0) hp0.1
  rw [YoungDiagram.rowLen_add] at hsum0
  have hrow0 := long_row_pos hq0.1
  have hN : N = q0.val.1.rowLen 0 + (q0.val.2.rowLen 1 - 1) := by
    simp only [N, w, blockWidth, YoungDiagram.rowLen_removeFirstRowCol, Nat.zero_add]
  have hshort : (θ.rowLen 0 : ℤ) < (N : ℤ) + n := by omega
  have hkill (q : Q) (hq : ¬P q) := projection_vanishes R θ n c N hshort
    (fun q hl hz => hmax q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl, hz⟩)) q hq
  have hθ : (θ.dropRows 1).colLen 0 < θ.colLen 0 := by
    have hc0 := congrArg (fun μ : YoungDiagram => μ.colLen 0) hp0.1
    rw [YoungDiagram.colLen_add] at hc0
    rw [YoungDiagram.colLen_dropRows]
    omega
  have hi := hind (θ.dropRows 1) hθ m
  let f := blockTailEmbedding θ n N
  have hli := hi.comp f f.injective
  have hproject := congrArg (firstRowProjection R (N : ℤ)) hc
  rw [map_sum, map_zero] at hproject
  simp only [map_smul] at hproject
  have hz : (∑ q : {q : Q // ¬P q},
      c q.val • firstRowProjection R (N : ℤ) (orientedPairProduct R q.val.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    exact hkill q.val q.property
  have hsplit := Fintype.sum_subtype_add_sum_subtype P
    (fun q : Q => c q • firstRowProjection R (N : ℤ) (orientedPairProduct R q.val))
  rw [hz, add_zero] at hsplit
  have hblock : (∑ q : B, c q.val • orientedPairProduct R (f q).val) = 0 := by
    rw [← hproject, ← hsplit]
    apply Finset.sum_congr rfl
    intro q _
    congr 1
    have he := firstRowProjection_product_sum (R := R) q.val.val.1
      q.val.val.2.removeFirstRowCol
    rw [YoungDiagram.dropRows_removeFirstRowCol] at he
    have hn : q.val.val.1.rowLen 0 + q.val.val.2.removeFirstRowCol.rowLen 0 = N :=
      q.property.2
    rw [hn] at he
    exact he.symm
  have hc0 := Fintype.linearIndependent_iff.mp hli (fun q : B => c q.val) hblock
    (⟨q0, hq0.1, rfl⟩ : B)
  exact hq0.2 hc0

/-- Ordered corner-deleted splitting products are independent at every integer hook index. -/
theorem oriented_linearIndependent (R : Type*) [CommRing R] (θ : YoungDiagram) (n : ℤ) :
    LinearIndependent R (fun q : orientedSplittings θ n =>
      orientedPairProduct R (q : YoungDiagram × YoungDiagram)) := by
  classical
  suffices ∀ r (θ : YoungDiagram) (n : ℤ), θ.colLen 0 = r →
      LinearIndependent R (fun q : orientedSplittings θ n =>
        orientedPairProduct R q.val) by exact this _ θ n rfl
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro θ n hr
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    have hlong := long_coefficients_eq_zero R θ n
      (fun ψ hψ m => ih (ψ.colLen 0) (by omega) ψ m rfl) c hc
    intro q
    by_cases hl : 2 ≤ q.val.2.colLen 0
    · exact hlong q hl
    · have hq : q.val.2.colLen 0 ≤ 1 := by omega
      have he : (∑ p : orientedSplittings θ n, c p • orientedPairProduct R p.val) =
          c q • schur R q.val.1 := by
        rw [Finset.sum_eq_single q]
        · rw [short_product R q hq]
        · intro p _ hpq
          by_cases hp : 2 ≤ p.val.2.colLen 0
          · rw [hlong p hp, zero_smul]
          · exact False.elim (hpq (short_eq θ n p q (by omega) hq))
        · intro hn
          exact False.elim (hn (Finset.mem_univ q))
      rw [he] at hc
      have hz := congrArg (fun f : SymmetricFunction R => (schurBasis R).repr f q.val.1) hc
      simpa only [map_smul, ← schurBasis_apply, Module.Basis.repr_self,
        Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one,
        map_zero, Finsupp.zero_apply] using hz

end ComplementaryProducts
