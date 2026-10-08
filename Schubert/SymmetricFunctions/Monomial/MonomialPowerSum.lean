import Schubert.SymmetricFunctions.Monomial.FiniteMonomialIncidence
import Schubert.SymmetricFunctions.Families.Families
import Schubert.SymmetricFunctions.Transfer

/-!
# The largest power-sum generator of a monomial function

Integer Möbius inversion of labelled row weights isolates the one-block contribution.

## Main results

* `monomial_eq_smul_powerSum_add` gives the explicit nonzero largest-generator coefficient.
-/

noncomputable section

namespace SymmetricFunction

private theorem rowWeight_pos (μ : YoungDiagram) (i : Fin (μ.colLen 0)) :
    0 < μ.rowLen i.val :=
  YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr i.isLt)

private def blockPowerIndex (μ : YoungDiagram)
    (P : Finpartition (Finset.univ : Finset (Fin (μ.colLen 0)))) (B : P.parts) : ℕ+ :=
  ⟨∑ i ∈ B.val, μ.rowLen i.val, Finset.sum_pos (fun i _ => rowWeight_pos μ i)
    (P.nonempty_of_mem_parts B.property)⟩

private theorem rowWeight_sum (μ : YoungDiagram) :
    (∑ i : Fin (μ.colLen 0), μ.rowLen i.val) = μ.card := by
  have he : List.ofFn (fun i : Fin (μ.colLen 0) => μ.rowLen i.val) = μ.rowLens := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, YoungDiagram.length_rowLens]
    · intro i hi hj
      simp only [List.getElem_ofFn, YoungDiagram.get_rowLens]
  have hs := congrArg (fun l : List ℕ => (l : Multiset ℕ).sum) he
  rw [← Fin.univ_val_map, ← Finset.sum_eq_multiset_sum] at hs
  exact hs.trans (by simpa only [Multiset.sum_coe] using μ.sum_rowLens_eq_card)

private theorem monomial_moebius_expansion (R : Type*) [CommRing R] (μ : YoungDiagram) :
    (∏ r ∈ μ.rowLens.toFinset, (μ.rowLens.count r).factorial : ℕ) • monomial R μ =
      ∑ P : Finpartition (Finset.univ : Finset (Fin (μ.colLen 0))),
        IncidenceAlgebra.mu ℤ ⊥ P • ∏ B : P.parts, powerSum R (blockPowerIndex μ P B) := by
  classical
  apply ext_restrict
  intro N
  simp only [map_nsmul, restrict_monomial, map_sum, map_zsmul, map_prod, restrict_powerSum]
  rw [← sum_injective_row_weights]
  rw [Finpartition.sum_embeddings_mu_powerSums R]
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  exact (Finset.prod_coe_sort P.parts (fun B =>
    MvPolynomial.psum (Fin N) R (∑ i ∈ B, μ.rowLen i.val))).symm

private theorem blockPowerIndex_lt (μ : YoungDiagram)
    (P : Finpartition (Finset.univ : Finset (Fin (μ.colLen 0)))) (hP : P ≠ ⊤)
    (B : P.parts) : (blockPowerIndex μ P B).val < μ.card := by
  have hB : B.val ≠ Finset.univ := by
    intro he
    apply hP
    apply top_le_iff.mp
    rw [Finpartition.le_iff_mem_part]
    intro i j _
    have hp : P.part j = B.val := P.part_eq_of_mem B.property (by rw [he]; simp)
    rw [hp, he]
    exact Finset.mem_univ _
  have hx : ∃ i : Fin (μ.colLen 0), i ∉ B.val := by
    by_contra! hn
    exact hB (Finset.eq_univ_iff_forall.mpr hn)
  obtain ⟨i, hi⟩ := hx
  exact (Finset.sum_lt_sum_of_subset (Finset.subset_univ B.val) (Finset.mem_univ i) hi
    (rowWeight_pos μ i) (fun j _ _ => Nat.zero_le (μ.rowLen j.val))).trans_eq (rowWeight_sum μ)

private theorem top_powerProduct (R : Type*) [CommRing R] (μ : YoungDiagram)
    (hk : 0 < μ.colLen 0) (d : ℕ+) (hd : d.val = μ.card) :
    (∏ B : (⊤ : Finpartition (Finset.univ : Finset (Fin (μ.colLen 0)))).parts,
      powerSum R (blockPowerIndex μ ⊤ B)) = powerSum R d := by
  classical
  have hkcard : 0 < Fintype.card (Fin (μ.colLen 0)) := by
    simpa only [Fintype.card_fin] using hk
  let B₀ : (⊤ : Finpartition (Finset.univ : Finset (Fin (μ.colLen 0)))).parts :=
    ⟨Finset.univ, by rw [Finpartition.parts_top_univ hkcard]; simp⟩
  have hB (B : (⊤ : Finpartition (Finset.univ : Finset (Fin (μ.colLen 0)))).parts) :
      B = B₀ := by
    apply Subtype.ext
    have hb := B.property
    simpa only [Finpartition.parts_top_univ hkcard, Finset.mem_singleton] using hb
  rw [Finset.prod_eq_single B₀]
  · congr 1
    apply Subtype.ext
    change (∑ i : Fin (μ.colLen 0), μ.rowLen i.val) = d.val
    rw [rowWeight_sum μ, hd]
  · intro B _ hne
    exact (hne (hB B)).elim
  · simp

/-- The largest power-sum coefficient of a nonempty monomial has its signed-factorial value. -/
theorem monomial_eq_smul_powerSum_add (F : Type*) [Field F] [CharZero F]
    (α : YoungDiagram) (hα : α ≠ ⊥) (d : ℕ+) (hd : d.val = α.card) :
    ∃ (κ : F) (Q : SymmetricFunction F),
      κ = (-1 : F) ^ (α.colLen 0 - 1) * ((α.colLen 0 - 1).factorial : F) /
        ((∏ r ∈ α.rowLens.toFinset, (α.rowLens.count r).factorial : ℕ) : F) ∧
      κ ≠ 0 ∧ monomial F α = κ • powerSum F d + Q ∧
      Q ∈ Algebra.adjoin F ((fun j : ℕ+ => powerSum F j) '' {j | j.val < d.val}) := by
  classical
  have hk : 0 < α.colLen 0 := by
    have := (YoungDiagram.eq_bot_iff_colLen_zero α).not.mp hα
    omega
  let r : ℕ := ∏ t ∈ α.rowLens.toFinset, (α.rowLens.count t).factorial
  let A (P : Finpartition (Finset.univ : Finset (Fin (α.colLen 0)))) : SymmetricFunction F :=
    IncidenceAlgebra.mu ℤ ⊥ P • ∏ B : P.parts, powerSum F (blockPowerIndex α P B)
  let T := ∑ P ∈ Finset.univ.erase
    (⊤ : Finpartition (Finset.univ : Finset (Fin (α.colLen 0)))), A P
  let c : F := (-1 : F) ^ (α.colLen 0 - 1) * ((α.colLen 0 - 1).factorial : F)
  have hr : (r : F) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    exact (Finset.prod_pos (fun _ _ => Nat.factorial_pos _)).ne'
  have hc : c ≠ 0 := mul_ne_zero (isUnit_neg_one.pow _).ne_zero
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have ht : A ⊤ = c • powerSum F d := by
    dsimp only [A, c]
    rw [Finpartition.mu_bot_top _ hk, top_powerProduct F α hk d hd,
      ← Int.cast_smul_eq_zsmul F]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  have he := monomial_moebius_expansion F α
  change r • monomial F α = ∑ P, A P at he
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ ⊤), ht] at he
  have hmain : monomial F α = (c / (r : F)) • powerSum F d + (r : F)⁻¹ • T := by
    rw [← Nat.cast_smul_eq_nsmul F] at he
    have hh := congrArg (fun f : SymmetricFunction F => (r : F)⁻¹ • f) he
    rw [smul_smul, inv_mul_cancel₀ hr, one_smul, smul_add, smul_smul] at hh
    simpa only [T, div_eq_mul_inv, mul_comm, add_comm] using hh
  refine ⟨c / (r : F), (r : F)⁻¹ • T, rfl, div_ne_zero hc hr, hmain, ?_⟩
  let S := Algebra.adjoin F ((fun j : ℕ+ => powerSum F j) '' {j | j.val < d.val})
  apply S.smul_mem
  apply S.sum_mem
  intro P hP
  have hne : P ≠ ⊤ := (Finset.mem_erase.mp hP).1
  apply S.zsmul_mem
  apply S.prod_mem
  intro B _
  apply Algebra.subset_adjoin
  exact ⟨blockPowerIndex α P B, (blockPowerIndex_lt α P hne B).trans_eq hd.symm, rfl⟩

end SymmetricFunction
