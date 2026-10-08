import Schubert.ComplementaryProducts.GapBlocks
import Schubert.SetPartitions.Basic

/-! # The worked examples

The gap vector, rectangular complement, tails and fixed-gap projection of the partition
`(6,5,4,3,2)` in the rectangle `(7^5)`, and two set partitions of `{1,2,3,4}` with the refinement
between them.

## Main results

* `GapExample.gap_shape` and `GapExample.gap_complementShape`: both partitions of the pair have
  gap vector `(4,2)`.
* `GapExample.rectComplement_shape`: the complement of `(6,5,4,3,2)` is `(5,4,3,2,1)`.
* `GapExample.tails_add`: the tails `(4,3,2)` and `(3,2,1)` add up to `(7,5,3)`.
* `GapExample.gapProjection_eq`: the projection `Π_(4,2)` is `π_9 ∘ π_11`.
* `GapExample.firstRowProjection_eleven` and `GapExample.gapProjection_shape`: the two
  projection steps applied to `s_(6,5,4,3,2) s_(5,4,3,2,1)`.
* `SetPartitionExample.mem_parts_pairs` and `SetPartitionExample.refines`: the blocks of
  `{{1,3},{2,4}}`, and `{{1},{2},{3,4}}` refines `{{1,2},{3,4}}`.

## Implementation notes

Rows of Young diagrams are numbered from `0`, and the elements `1, 2, 3, 4` of the paper's ground
set are the elements `0, 1, 2, 3` of `Fin 4`. A set partition is given as the partition into the
fibers of a map on `Fin 4`.
-/

noncomputable section

namespace ComplementaryProducts

open SymmetricFunction

namespace GapExample

/-- The partition `(6,5,4,3,2)`. -/
def shape : YoungDiagram := YoungDiagram.ofRowLensFin ![6, 5, 4, 3, 2] (by decide)

/-- The partition `(5,4,3,2,1)`. -/
def complementShape : YoungDiagram := YoungDiagram.ofRowLensFin ![5, 4, 3, 2, 1] (by decide)

/-- The partition `(5,4,3,2)`. -/
def shapeTailOne : YoungDiagram := YoungDiagram.ofRowLensFin ![5, 4, 3, 2] (by decide)

/-- The partition `(4,3,2,1)`. -/
def complementTailOne : YoungDiagram := YoungDiagram.ofRowLensFin ![4, 3, 2, 1] (by decide)

/-- The partition `(4,3,2)`. -/
def shapeTail : YoungDiagram := YoungDiagram.ofRowLensFin ![4, 3, 2] (by decide)

/-- The partition `(3,2,1)`. -/
def complementTail : YoungDiagram := YoungDiagram.ofRowLensFin ![3, 2, 1] (by decide)

/-- The partition `(7,5,3)`. -/
def tailSum : YoungDiagram := YoungDiagram.ofRowLensFin ![7, 5, 3] (by decide)

/-- The row lengths of a diagram given by a finite list of row lengths. -/
private theorem rowLen_ofRowLensFin_eq {n : ℕ} (f : Fin n → ℕ) (hf : Antitone f) (i : ℕ) :
    (YoungDiagram.ofRowLensFin f hf).rowLen i = if h : i < n then f ⟨i, h⟩ else 0 := by
  split_ifs with h
  · exact YoungDiagram.rowLen_ofRowLensFin f hf ⟨i, h⟩
  · exact YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le f hf (by omega)

/-- Two diagrams with the same row lengths are equal. -/
private theorem ext_rowLen {μ ν : YoungDiagram} (h : ∀ i, μ.rowLen i = ν.rowLen i) : μ = ν :=
  YoungDiagram.rowLen_injective (funext h)

/-- The row lengths of `(6,5,4,3,2)`. -/
private theorem rowLen_shape (i : ℕ) :
    shape.rowLen i = if h : i < 5 then ![6, 5, 4, 3, 2] ⟨i, h⟩ else 0 :=
  rowLen_ofRowLensFin_eq _ _ i

/-- The partition `(6,5,4,3,2)` fits in the rectangle `(7^5)`. -/
theorem shape_le_rectangle : shape ≤ YoungDiagram.rectangle 5 7 := by
  rw [YoungDiagram.le_iff_forall_rowLen_le]
  intro i
  rw [rowLen_shape, YoungDiagram.rowLen_rectangle]
  by_cases hi : i < 5
  · interval_cases i <;> simp
  · simp [hi]

/-- The complement of `(6,5,4,3,2)` in `(7^5)` is `(5,4,3,2,1)`. -/
theorem rectComplement_shape : YoungDiagram.rectComplement 5 7 shape = complementShape := by
  apply ext_rowLen
  intro i
  rw [YoungDiagram.rowLen_rectComplement, rowLen_shape, complementShape,
    rowLen_ofRowLensFin_eq]
  by_cases hi : i < 5
  · interval_cases i <;> simp
  · simp [hi]

/-- The gap vector of `(6,5,4,3,2)` in `(7^5)` is `(4,2)`. -/
theorem gap_shape : gap 5 shape = ![4, 2] := by
  funext i
  fin_cases i <;> simp [gap_apply, rowLen_shape]

/-- The gap vector of the complement `(5,4,3,2,1)` is `(4,2)` as well. -/
theorem gap_complementShape : gap 5 complementShape = ![4, 2] := by
  funext i
  fin_cases i <;> simp [gap_apply, complementShape, rowLen_ofRowLensFin_eq]

/-- The tail of `(6,5,4,3,2)` is `(4,3,2)`. -/
theorem dropRows_shape : shape.dropRows 2 = shapeTail := by
  apply ext_rowLen
  intro i
  rw [YoungDiagram.rowLen_dropRows, rowLen_shape, shapeTail, rowLen_ofRowLensFin_eq]
  by_cases hi : i < 3
  · interval_cases i <;> simp
  · simp [hi, show ¬ 2 + i < 5 by omega]

/-- The tail of `(5,4,3,2,1)` is `(3,2,1)`. -/
theorem dropRows_complementShape : complementShape.dropRows 2 = complementTail := by
  apply ext_rowLen
  intro i
  rw [YoungDiagram.rowLen_dropRows, complementShape, complementTail, rowLen_ofRowLensFin_eq,
    rowLen_ofRowLensFin_eq]
  by_cases hi : i < 3
  · interval_cases i <;> simp
  · simp [hi, show ¬ 2 + i < 5 by omega]

/-- The two tails add up to `(7,5,3)`. -/
theorem tails_add : shapeTail + complementTail = tailSum := by
  apply ext_rowLen
  intro i
  rw [YoungDiagram.rowLen_add, shapeTail, complementTail, tailSum, rowLen_ofRowLensFin_eq,
    rowLen_ofRowLensFin_eq, rowLen_ofRowLensFin_eq]
  by_cases hi : i < 3
  · interval_cases i <;> simp
  · simp [hi]

/-- For the gap vector `(4,2)` and width `7`, the projection `Π_g` is `π_9 ∘ π_11`. -/
theorem gapProjection_eq (R : Type*) [CommRing R] :
    gapProjection R 5 7 ![4, 2] =
      (firstRowProjection R 9).comp (firstRowProjection R 11) := by
  apply LinearMap.ext
  intro f
  rw [gapProjection_apply]
  simp [List.ofFn_succ]

/-- The first projection step: `π_11(s_(6,5,4,3,2) s_(5,4,3,2,1)) = s_(5,4,3,2) s_(4,3,2,1)`. -/
theorem firstRowProjection_eleven (R : Type*) [CommRing R] [Nontrivial R] :
    firstRowProjection R 11 (schur R shape * schur R complementShape) =
      schur R shapeTailOne * schur R complementTailOne := by
  have htop : topRow (schur R shape * schur R complementShape) = 11 := by
    rw [topRow_schur_mul_schur, rowLen_shape, complementShape, rowLen_ofRowLensFin_eq]
    simp
  have h := firstRowProjection_schur_mul_schur (R := R) shape complementShape
  rw [htop] at h
  have h1 : shape.dropRows 1 = shapeTailOne := by
    apply ext_rowLen
    intro i
    rw [YoungDiagram.rowLen_dropRows, rowLen_shape, shapeTailOne, rowLen_ofRowLensFin_eq]
    by_cases hi : i < 4
    · interval_cases i <;> simp
    · simp [hi, show ¬ 1 + i < 5 by omega]
  have h2 : complementShape.dropRows 1 = complementTailOne := by
    apply ext_rowLen
    intro i
    rw [YoungDiagram.rowLen_dropRows, complementShape, complementTailOne,
      rowLen_ofRowLensFin_eq, rowLen_ofRowLensFin_eq]
    by_cases hi : i < 4
    · interval_cases i <;> simp
    · simp [hi, show ¬ 1 + i < 5 by omega]
  simpa only [Nat.cast_ofNat, h1, h2] using h

/-- Applying `Π_(4,2)` to `s_(6,5,4,3,2) s_(5,4,3,2,1)` gives `s_(4,3,2) s_(3,2,1)`. -/
theorem gapProjection_shape (R : Type*) [CommRing R] :
    gapProjection R 5 7 ![4, 2] (schur R shape * schur R complementShape) =
      schur R shapeTail * schur R complementTail := by
  have hg : ValidGap 5 7 ![4, 2] := by
    rw [← gap_shape]
    exact validGap_gap shape_le_rectangle
  have h := (gapProjection_of_gap_eq R 5 7 ![4, 2] hg shape shape_le_rectangle gap_shape).1
  rw [rectComplement_shape] at h
  simpa only [show (5 : ℕ) / 2 = 2 from rfl, dropRows_shape, dropRows_complementShape] using h

end GapExample

namespace SetPartitionExample

/-- The set partition `{{1,3},{2,4}}`: the fibers of `1 ↦ 0, 2 ↦ 1, 3 ↦ 0, 4 ↦ 1`. -/
def pairs : Finpartition (Finset.univ : Finset (Fin 4)) :=
  Finpartition.kernelPartition ![0, 1, 0, 1]

/-- The set partition `{{1},{2},{3,4}}`. -/
def singletonsAndPair : Finpartition (Finset.univ : Finset (Fin 4)) :=
  Finpartition.kernelPartition ![0, 1, 2, 2]

/-- The set partition `{{1,2},{3,4}}`. -/
def twoPairs : Finpartition (Finset.univ : Finset (Fin 4)) :=
  Finpartition.kernelPartition ![0, 0, 1, 1]

/-- The blocks of a kernel partition are the blocks of its elements. -/
private theorem mem_parts_iff (P : Finpartition (Finset.univ : Finset (Fin 4)))
    (s : Finset (Fin 4)) : s ∈ P.parts ↔ ∃ i, P.part i = s := by
  constructor
  · intro hs
    obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts hs
    exact ⟨i, P.part_eq_of_mem hs hi⟩
  · rintro ⟨i, rfl⟩
    exact P.part_mem.mpr (Finset.mem_univ i)

/-- The blocks of a kernel partition, computed from the map. -/
private theorem part_kernelPartition (f : Fin 4 → ℕ) (i : Fin 4) :
    (Finpartition.kernelPartition f).part i = Finset.univ.filter (fun j => f j = f i) := by
  ext j
  simp [Finpartition.mem_part_kernelPartition, eq_comm]

/-- The blocks of `{{1,3},{2,4}}` are `{1,3}` and `{2,4}`. -/
theorem mem_parts_pairs (s : Finset (Fin 4)) :
    s ∈ pairs.parts ↔ s = {0, 2} ∨ s = {1, 3} := by
  rw [mem_parts_iff, pairs]
  simp only [part_kernelPartition]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> decide
  · rintro (rfl | rfl)
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩

/-- The blocks of `{{1},{2},{3,4}}` are `{1}`, `{2}` and `{3,4}`. -/
theorem mem_parts_singletonsAndPair (s : Finset (Fin 4)) :
    s ∈ singletonsAndPair.parts ↔ s = {0} ∨ s = {1} ∨ s = {2, 3} := by
  rw [mem_parts_iff, singletonsAndPair]
  simp only [part_kernelPartition]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> decide
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨2, by decide⟩

/-- The blocks of `{{1,2},{3,4}}` are `{1,2}` and `{3,4}`. -/
theorem mem_parts_twoPairs (s : Finset (Fin 4)) :
    s ∈ twoPairs.parts ↔ s = {0, 1} ∨ s = {2, 3} := by
  rw [mem_parts_iff, twoPairs]
  simp only [part_kernelPartition]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> decide
  · rintro (rfl | rfl)
    · exact ⟨0, by decide⟩
    · exact ⟨2, by decide⟩

/-- The set partition `{{1},{2},{3,4}}` refines `{{1,2},{3,4}}`. -/
theorem refines : singletonsAndPair ≤ twoPairs := by
  rw [Finpartition.le_iff_mem_part]
  intro i j hij
  rw [singletonsAndPair, Finpartition.mem_part_kernelPartition] at hij
  rw [twoPairs, Finpartition.mem_part_kernelPartition]
  fin_cases i <;> fin_cases j <;> simp_all

end SetPartitionExample

end ComplementaryProducts
