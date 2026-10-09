import KlebersConjecture.SetPartitions.Counting
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Weighted sums by kernel partitions and block labels

Arbitrary weights reindex by exact kernel fibers. Multiplicative weights constant on
partition blocks factor into independent sums over the labels of each block.

## Main results

* `sum_blockConstant_eq_kernels` separates a weighted sum into coarser exact kernels.
* `sum_blockConstant_eq_labels` reindexes a weighted sum by block labels.
* `sum_blockConstant_prod` factors a product weight into one label sum per block.

## Implementation notes

The sums range over the standard finite partition type and ordinary maps on a finite
index type. Empty products and the empty partition follow their standard conventions.
-/

noncomputable section

namespace Finpartition

open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α S : Type*} [Fintype α]

/-- A weighted sum over block-constant maps separates into its exact coarser kernels. -/
theorem sum_blockConstant_eq_kernels [AddCommMonoid S]
    (P : Finpartition (Finset.univ : Finset (ι))) (w : (ι → α) → S) :
    (∑ f : {f : ι → α // P ≤ kernelPartition f}, w f.val) =
      ∑ Q : {Q : Finpartition (Finset.univ : Finset (ι)) // P ≤ Q},
        ∑ f : {f : ι → α // kernelPartition f = Q.val}, w f.val := by
  calc
    _ = ∑ q : Σ Q : {Q : Finpartition (Finset.univ : Finset (ι)) // P ≤ Q},
        {f : ι → α // kernelPartition f = Q.val}, w q.2.val :=
      Fintype.sum_equiv (P.blockConstantKernelEquiv α) _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_sigma _

/-- Reading the labels of each block preserves any weighted sum of constant maps. -/
theorem sum_blockConstant_eq_labels [AddCommMonoid S]
    (P : Finpartition (Finset.univ : Finset (ι))) (w : (ι → α) → S) :
    (∑ f : {f : ι → α // P ≤ kernelPartition f}, w f.val) =
      ∑ g : P.parts → α, w (P.labelMap g) := by
  apply Fintype.sum_equiv (P.blockConstantEquiv α)
  intro f
  exact congrArg w (P.labelMap_blockValues f.val f.property).symm

/-- All maps split into exact kernel fibers, with their original weights retained. -/
theorem sum_eq_sum_kernelFibers [AddCommMonoid S] (w : (ι → α) → S) :
    (∑ f : ι → α, w f) =
      ∑ P : Finpartition (Finset.univ : Finset (ι)),
        ∑ f : {f : ι → α // kernelPartition f = P}, w f.val := by
  calc
    _ = ∑ q : Σ P : Finpartition (Finset.univ : Finset (ι)),
        {f : ι → α // kernelPartition f = P}, w q.2.val :=
      Fintype.sum_equiv (kernelFiberEquiv ι α).symm _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_sigma _

omit [Fintype α] in
private theorem prod_labelMap [CommMonoid S]
    (P : Finpartition (Finset.univ : Finset (ι))) (a : ι → α → S)
    (g : P.parts → α) :
    (∏ i : ι, a i (P.labelMap g i)) =
      ∏ B : P.parts, ∏ i ∈ B.val, a i (g B) := by
  have he : (∏ i : ι, a i (P.labelMap g i)) =
      ∏ B : P.parts, ∏ i ∈ B.val, a i (P.labelMap g i) := by
    have h := Finset.prod_biUnion (f := fun i => a i (P.labelMap g i)) P.disjoint
    rw [P.biUnion_parts] at h
    exact h.trans (Finset.prod_coe_sort P.parts
      (fun B => ∏ i ∈ B, a i (P.labelMap g i))).symm
  rw [he]
  apply Finset.prod_congr rfl
  intro B _
  apply Finset.prod_congr rfl
  intro i hi
  have h := P.blockValues_eq_of_mem (P.labelMap g) (P.le_kernelPartition_labelMap g) B i hi
  rw [P.blockValues_labelMap] at h
  exact congrArg (a i) h.symm

/-- Summing a product over constant maps factors into independent sums over block labels. -/
theorem sum_blockConstant_prod [CommSemiring S]
    (P : Finpartition (Finset.univ : Finset (ι))) (a : ι → α → S) :
    (∑ f : {f : ι → α // P ≤ kernelPartition f}, ∏ i : ι, a i (f.val i)) =
      ∏ B ∈ P.parts, ∑ x : α, ∏ i ∈ B, a i x := by
  calc
    _ = ∑ g : P.parts → α, ∏ i : ι, a i (P.labelMap g i) :=
      sum_blockConstant_eq_labels P (fun f => ∏ i : ι, a i (f i))
    _ = _ := by
      simp_rw [prod_labelMap]
      rw [← Fintype.prod_sum (fun (B : P.parts) (x : α) => ∏ i ∈ B.val, a i x)]
      exact Finset.prod_coe_sort P.parts (fun B => ∑ x : α, ∏ i ∈ B, a i x)

end Finpartition
