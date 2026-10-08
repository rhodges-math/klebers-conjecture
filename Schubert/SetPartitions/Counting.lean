import Schubert.SetPartitions.Basic
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Counting maps by their equality patterns

Maps constant on partition blocks are arbitrary labels of the blocks. Maps with exactly
that kernel partition are injective labels of the blocks.

## Main results

* `Finpartition.blockConstantEquiv`: constant maps correspond to block labels.
* `Finpartition.exactKernelEquiv`: exact kernels correspond to injective block labels.
* `Finpartition.card_blockConstant`: the number of constant maps is a power.
* `Finpartition.card_exactKernel`: the number with exact kernel is a descending factorial.

## Implementation notes

The index type is an arbitrary finite type. Kernel fibers use the standard equivalence
and embedding carriers, including the empty index type.
-/

namespace Finpartition

open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}

/-- The block containing an argument, considered as an element of the finite block type. -/
def blockOf (P : Finpartition (Finset.univ : Finset (ι))) (i : ι) : P.parts :=
  ⟨P.part i, P.part_mem.mpr (Finset.mem_univ i)⟩

/-- Equality of block indices is membership in a common block. -/
theorem blockOf_eq_iff (P : Finpartition (Finset.univ : Finset (ι))) (i j : ι) :
    P.blockOf i = P.blockOf j ↔ i ∈ P.part j := by
  rw [Subtype.ext_iff]
  exact (P.mem_part_iff_part_eq_part (Finset.mem_univ i) (Finset.mem_univ j)).symm

/-- A chosen representative of a nonempty block. -/
private noncomputable def blockRepresentative
    (P : Finpartition (Finset.univ : Finset (ι))) (s : P.parts) : ι :=
  Classical.choose (P.nonempty_of_mem_parts s.property)

/-- The chosen representative belongs to its block. -/
private theorem blockRepresentative_mem (P : Finpartition (Finset.univ : Finset (ι)))
    (s : P.parts) : P.blockRepresentative s ∈ s.val :=
  Classical.choose_spec (P.nonempty_of_mem_parts s.property)

/-- The block of its chosen representative is the original block. -/
@[simp] private theorem blockOf_blockRepresentative
    (P : Finpartition (Finset.univ : Finset (ι))) (s : P.parts) :
    P.blockOf (P.blockRepresentative s) = s := by
  apply Subtype.ext
  exact P.part_eq_of_mem s.property (P.blockRepresentative_mem s)

/-- A block labeling induces a map on arguments. -/
def labelMap (P : Finpartition (Finset.univ : Finset (ι))) (g : P.parts → α) :
    ι → α := fun i => g (P.blockOf i)

/-- A map gives each block the value at its chosen representative. -/
noncomputable def blockValues (P : Finpartition (Finset.univ : Finset (ι)))
    (f : ι → α) : P.parts → α := fun s => f (P.blockRepresentative s)

/-- For a constant map, the value assigned to a block is its value at any member. -/
theorem blockValues_eq_of_mem
    (P : Finpartition (Finset.univ : Finset (ι))) (f : ι → α)
    (hf : P ≤ kernelPartition f) (s : P.parts) (i : ι) (hi : i ∈ s.val) :
    P.blockValues f s = f i :=
  (le_kernelPartition_iff P f).mp hf s.val s.property (P.blockRepresentative s)
    (P.blockRepresentative_mem s) i hi

/-- Reading the values of a block labeling recovers every label. -/
@[simp] theorem blockValues_labelMap
    (P : Finpartition (Finset.univ : Finset (ι))) (g : P.parts → α) :
    P.blockValues (P.labelMap g) = g := by
  funext s
  simp only [blockValues, labelMap, blockOf_blockRepresentative]

/-- A map induced by block labels is constant on each block. -/
theorem le_kernelPartition_labelMap
    (P : Finpartition (Finset.univ : Finset (ι))) (g : P.parts → α) :
    P ≤ kernelPartition (P.labelMap g) := by
  rw [le_iff_mem_part]
  intro i j hij
  apply (mem_part_kernelPartition _ i j).mpr
  exact congrArg g ((P.blockOf_eq_iff i j).mpr hij).symm

/-- Reading and then labeling recovers a map constant on every block. -/
theorem labelMap_blockValues
    (P : Finpartition (Finset.univ : Finset (ι))) (f : ι → α)
    (hf : P ≤ kernelPartition f) : P.labelMap (P.blockValues f) = f := by
  funext i
  exact (le_kernelPartition_iff P f).mp hf (P.part i)
    (P.part_mem.mpr (Finset.mem_univ i)) (P.blockRepresentative (P.blockOf i))
    (P.blockRepresentative_mem (P.blockOf i)) i (P.mem_part (Finset.mem_univ i))

/-- Maps constant on blocks correspond to arbitrary block labelings. -/
noncomputable def blockConstantEquiv
    (P : Finpartition (Finset.univ : Finset (ι))) (α : Type*) :
    {f : ι → α // P ≤ kernelPartition f} ≃ (P.parts → α) where
  toFun f := P.blockValues f.val
  invFun g := ⟨P.labelMap g, P.le_kernelPartition_labelMap g⟩
  left_inv f := Subtype.ext (P.labelMap_blockValues f.val f.property)
  right_inv g := P.blockValues_labelMap g

/-- Distinct blocks have distinct values when the kernel is exact. -/
theorem blockValues_injective
    (P : Finpartition (Finset.univ : Finset (ι))) (f : ι → α)
    (hf : kernelPartition f = P) : Function.Injective (P.blockValues f) := by
  intro s t hst
  apply Subtype.ext
  have hparts := (part_kernelPartition_eq_iff f
    (P.blockRepresentative s) (P.blockRepresentative t)).mpr hst
  rw [hf] at hparts
  have hs := congrArg Subtype.val (P.blockOf_blockRepresentative s)
  have ht := congrArg Subtype.val (P.blockOf_blockRepresentative t)
  exact hs.symm.trans (hparts.trans ht)

/-- An injective labeling has exactly the prescribed kernel partition. -/
theorem kernelPartition_labelMap
    (P : Finpartition (Finset.univ : Finset (ι))) (g : P.parts → α)
    (hg : Function.Injective g) : kernelPartition (P.labelMap g) = P := by
  apply le_antisymm _ (P.le_kernelPartition_labelMap g)
  rw [le_iff_mem_part]
  intro i j hij
  have heq := (mem_part_kernelPartition _ i j).mp hij
  exact (P.blockOf_eq_iff i j).mp (hg heq).symm

/-- Maps with exact kernel correspond to injective block labelings. -/
noncomputable def exactKernelEquiv
    (P : Finpartition (Finset.univ : Finset (ι))) (α : Type*) :
    {f : ι → α // kernelPartition f = P} ≃ (P.parts ↪ α) where
  toFun f := ⟨P.blockValues f.val, P.blockValues_injective f.val f.property⟩
  invFun g := ⟨P.labelMap g, P.kernelPartition_labelMap g g.injective⟩
  left_inv f := Subtype.ext (P.labelMap_blockValues f.val (le_of_eq f.property.symm))
  right_inv g := by
    apply DFunLike.ext
    intro s
    exact congrFun (P.blockValues_labelMap g) s

/-- Constant maps into `Fin x` are counted by one independent choice for each block. -/
theorem card_blockConstant (P : Finpartition (Finset.univ : Finset (ι))) (x : ℕ) :
    Fintype.card {f : ι → Fin x // P ≤ kernelPartition f} = x ^ P.parts.card := by
  rw [Fintype.card_congr (P.blockConstantEquiv (Fin x))]
  simp

/-- Maps into `Fin x` with exact kernel are counted by a descending factorial. -/
theorem card_exactKernel (P : Finpartition (Finset.univ : Finset (ι))) (x : ℕ) :
    Fintype.card {f : ι → Fin x // kernelPartition f = P} =
      x.descFactorial P.parts.card := by
  rw [Fintype.card_congr (P.exactKernelEquiv (Fin x)), Fintype.card_embedding_eq]
  simp

/-- Constant maps decompose uniquely according to their exact, coarser kernel partition. -/
noncomputable def blockConstantKernelEquiv
    (P : Finpartition (Finset.univ : Finset (ι))) (α : Type*) :
    {f : ι → α // P ≤ kernelPartition f} ≃
      Σ Q : {Q : Finpartition (Finset.univ : Finset (ι)) // P ≤ Q},
        {f : ι → α // kernelPartition f = Q.val} where
  toFun f := ⟨⟨kernelPartition f.val, f.property⟩, ⟨f.val, rfl⟩⟩
  invFun q := ⟨q.2.val, q.2.property.symm ▸ q.1.property⟩
  left_inv f := rfl
  right_inv q := by
    rcases q with ⟨⟨Q, hQ⟩, ⟨f, hf⟩⟩
    change kernelPartition f = Q at hf
    subst Q
    rfl

/-- All maps decompose uniquely by their exact kernel partition. -/
noncomputable def kernelFiberEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] (α : Type*) :
    (Σ P : Finpartition (Finset.univ : Finset (ι)),
      {f : ι → α // kernelPartition f = P}) ≃ (ι → α) :=
  Equiv.sigmaFiberEquiv kernelPartition

/-- Counting constant maps by their exact kernels gives the coarsening incidence identity. -/
theorem pow_eq_sum_descFactorial
    (P : Finpartition (Finset.univ : Finset (ι))) (x : ℕ) :
    x ^ P.parts.card =
      ∑ Q : {Q : Finpartition (Finset.univ : Finset (ι)) // P ≤ Q},
        x.descFactorial Q.val.parts.card := by
  rw [← card_blockConstant P x, Fintype.card_congr (P.blockConstantKernelEquiv (Fin x)),
    Fintype.card_sigma]
  exact Finset.sum_congr rfl fun Q _ => card_exactKernel Q.val x

/-- Maps with discrete kernel are precisely embeddings of the finite argument type. -/
def discreteKernelEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Type*} :
    {f : ι → σ // kernelPartition f = ⊥} ≃ (ι ↪ σ) where
  toFun f := ⟨f.val, by
    intro i j hij
    have hm := (mem_part_kernelPartition f.val i j).mpr hij.symm
    have he := congrArg (fun P : Finpartition (Finset.univ : Finset (ι)) =>
      i ∈ P.part j) f.property
    have hb := Eq.mp he hm
    simpa only [part_bot_univ, Finset.mem_singleton] using hb⟩
  invFun f := ⟨f, kernelPartition_eq_bot f f.injective⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Finpartition
