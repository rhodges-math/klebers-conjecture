import Mathlib.Order.Partition.Finpartition
import Mathlib.Order.Interval.Finset.Defs

/-!
# Finite set partitions and equality patterns

Partitions of finite sets carry the refinement lattice. The kernel partition of a map
records exactly which arguments have equal images.

## Main results

* `Finpartition.mem_part_kernelPartition`: the equality pattern of a map.
* `Finpartition.le_kernelPartition_iff`: refinement means constancy on each block.

## Implementation notes

Partitions use Mathlib's `Finpartition` carrier on finite sets. The lattice and locally
finite order instances apply to every finite subset of an arbitrary decidable type.
-/

namespace Finpartition

variable {ι : Type*} [DecidableEq ι]

/-- Finite set partitions form a lattice, with joins given by common coarsenings. -/
noncomputable instance instLattice (s : Finset ι) :
    Lattice (Finpartition s) := by
  classical
  exact Lattice.mkDual
    (fun P Q => (Finset.univ.filter fun R => P ≤ R ∧ Q ≤ R).inf id)
    (fun P Q => Finset.le_inf_iff.mpr fun R hR => (Finset.mem_filter.mp hR).2.1)
    (fun P Q => Finset.le_inf_iff.mpr fun R hR => (Finset.mem_filter.mp hR).2.2)
    (fun P Q R hP hQ => Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ R, hP, hQ⟩))

/-- Every interval in the refinement order on partitions of a finite set is finite. -/
noncomputable instance instLocallyFiniteOrder (s : Finset ι) :
    LocallyFiniteOrder (Finpartition s) := by
  classical
  exact Fintype.toLocallyFiniteOrder

variable [Fintype ι] {α : Type*}

/-- The partition of `ι` into fibers of a map. -/
noncomputable def kernelPartition (f : ι → α) :
    Finpartition (Finset.univ : Finset (ι)) := by
  classical
  exact ofSetoid (Setoid.ker f)

/-- Two arguments belong to the same kernel block exactly when their images agree. -/
@[simp] theorem mem_part_kernelPartition (f : ι → α) (i j : ι) :
    i ∈ (kernelPartition f).part j ↔ f j = f i := by
  classical
  exact mem_part_ofSetoid_iff_rel

/-- Equality of kernel blocks is equality of the images of their arguments. -/
theorem part_kernelPartition_eq_iff (f : ι → α) (i j : ι) :
    (kernelPartition f).part i = (kernelPartition f).part j ↔ f i = f j := by
  rw [← mem_part_iff_part_eq_part (P := kernelPartition f) (a := i) (b := j)
    (by simp) (by simp), mem_part_kernelPartition, eq_comm]

/-- Refinement preserves the relation of membership in a common block. -/
theorem le_iff_mem_part {P Q : Finpartition (Finset.univ : Finset (ι))} :
    P ≤ Q ↔ ∀ i j : ι, i ∈ P.part j → i ∈ Q.part j := by
  constructor
  · intro h i j hij
    obtain ⟨s, hs, hsubset⟩ := h (P.part_mem.mpr (Finset.mem_univ j))
    have hj : j ∈ s := hsubset (P.mem_part (Finset.mem_univ j))
    rw [Q.part_eq_of_mem hs hj]
    exact hsubset hij
  · intro h s hs
    obtain ⟨j, hj⟩ := P.nonempty_of_mem_parts hs
    refine ⟨Q.part j, Q.part_mem.mpr (Finset.mem_univ j), ?_⟩
    intro i hi
    apply h i j
    rwa [P.part_eq_of_mem hs hj]

/-- Refining a kernel partition means that the map is constant on every block. -/
theorem le_kernelPartition_iff (P : Finpartition (Finset.univ : Finset (ι)))
    (f : ι → α) :
    P ≤ kernelPartition f ↔ ∀ s ∈ P.parts, ∀ i ∈ s, ∀ j ∈ s, f i = f j := by
  rw [le_iff_mem_part]
  constructor
  · intro h s hs i hi j hj
    have hij : i ∈ P.part j := by rwa [P.part_eq_of_mem hs hj]
    exact ((mem_part_kernelPartition f i j).mp (h i j hij)).symm
  · intro h i j hij
    apply (mem_part_kernelPartition f i j).mpr
    exact h (P.part j) (P.part_mem.mpr (Finset.mem_univ j)) j
      (P.mem_part (Finset.mem_univ j)) i hij

/-- A block of the discrete partition consists of its single argument. -/
@[simp] theorem part_bot_univ (i : ι) :
    (⊥ : Finpartition (Finset.univ : Finset (ι))).part i = {i} := by
  apply part_eq_of_mem
  · simp [parts_bot]
  · simp

/-- The kernel of an injective map is the discrete partition. -/
theorem kernelPartition_eq_bot (f : ι → α) (hf : Function.Injective f) :
    kernelPartition f = ⊥ := by
  apply le_antisymm _ bot_le
  rw [le_iff_mem_part]
  intro i j hij
  have heq := hf ((mem_part_kernelPartition f i j).mp hij)
  simp [heq]

/-- The kernel of a constant map is the indiscrete partition, including the empty set. -/
@[simp] theorem kernelPartition_const (x : α) :
    kernelPartition (fun _ : ι => x) = ⊤ := by
  apply le_antisymm le_top
  rw [le_iff_mem_part]
  intro i j _
  simp

/-- Every partition on an empty finite index type is discrete. -/
theorem eq_bot_univ_of_isEmpty [IsEmpty ι]
    (P : Finpartition (Finset.univ : Finset ι)) : P = ⊥ := by
  apply le_antisymm _ bot_le
  rw [le_iff_mem_part]
  intro i
  exact isEmptyElim i

/-- On the empty set every partition is discrete. -/
theorem eq_bot_univ_zero (P : Finpartition (Finset.univ : Finset (Fin 0))) : P = ⊥ :=
  eq_bot_univ_of_isEmpty P

/-- The kernel of a map from the empty set is its unique partition. -/
@[simp] theorem kernelPartition_zero (f : Fin 0 → α) : kernelPartition f = ⊥ :=
  eq_bot_univ_zero _

end Finpartition
