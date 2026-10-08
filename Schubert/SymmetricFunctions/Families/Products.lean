import Schubert.SymmetricFunctions.Families.Families

/-!
# Products of the standard symmetric-function families

The row lengths of a diagram index products of elementary, complete, and power-sum functions.

## Main results

* `isHomogeneous_completeProd`: complete products have the diagram's degree.
* `isHomogeneous_elementaryProd`: elementary products have the diagram's degree.
* `isHomogeneous_powerSumProd`: power-sum products have the diagram's degree.
-/

noncomputable section

namespace SymmetricFunction

/-- The product of complete functions indexed by the row lengths of a diagram. -/
def completeProd (R : Type*) [CommSemiring R] (μ : YoungDiagram) : SymmetricFunction R :=
  (μ.rowLens.map (fun k : ℕ => complete R (k : ℤ))).prod

/-- The product of elementary functions indexed by the row lengths of a diagram. -/
def elementaryProd (R : Type*) [CommSemiring R] (μ : YoungDiagram) : SymmetricFunction R :=
  (μ.rowLens.map (elementary R)).prod

/-- The product of positive power sums indexed by the nonempty rows of a diagram. -/
def powerSumProd (R : Type*) [CommSemiring R] (μ : YoungDiagram) : SymmetricFunction R :=
  (μ.rowLens.attach.map (fun k => powerSum R ⟨k.val, μ.pos_of_mem_rowLens k.val k.property⟩)).prod

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The complete product of the empty diagram is one. -/
theorem completeProd_bot : completeProd R ⊥ = 1 := by
  simp [completeProd, YoungDiagram.rowLens]

/-- The elementary product of the empty diagram is one. -/
theorem elementaryProd_bot : elementaryProd R ⊥ = 1 := by
  simp [elementaryProd, YoungDiagram.rowLens]

/-- The power-sum product of the empty diagram is one. -/
theorem powerSumProd_bot : powerSumProd R ⊥ = 1 := by
  unfold powerSumProd
  apply List.prod_eq_one
  intro f hf
  obtain ⟨k, _, _⟩ := List.mem_map.mp hf
  have hk := k.property
  simp only [YoungDiagram.rowLens, YoungDiagram.colLen_bot, List.range_zero,
    List.map_nil, List.not_mem_nil] at hk

/-- Coefficient-ring maps preserve complete products. -/
theorem map_completeProd (φ : R →+* S) (μ : YoungDiagram) :
    map φ (completeProd R μ) = completeProd S μ := by
  simp only [completeProd, map_list_prod, List.map_map, Function.comp_def, map_complete]

/-- Coefficient-ring maps preserve elementary products. -/
theorem map_elementaryProd (φ : R →+* S) (μ : YoungDiagram) :
    map φ (elementaryProd R μ) = elementaryProd S μ := by
  simp only [elementaryProd, map_list_prod, List.map_map, Function.comp_def, map_elementary]

/-- Coefficient-ring maps preserve power-sum products. -/
theorem map_powerSumProd (φ : R →+* S) (μ : YoungDiagram) :
    map φ (powerSumProd R μ) = powerSumProd S μ := by
  unfold powerSumProd
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact map_powerSum φ _

/-- Complete products are homogeneous of the number of cells in their diagram. -/
theorem isHomogeneous_completeProd (μ : YoungDiagram) :
    IsHomogeneous (completeProd R μ) μ.card := by
  unfold completeProd
  apply isHomogeneous_iff_component.mpr
  simpa only [List.map_id, YoungDiagram.sum_rowLens_eq_card] using
    (isHomogeneous_iff_component.mp
      (@IsHomogeneous.list_prod R _ ℕ μ.rowLens (fun k => complete R (k : ℤ)) id
        (fun k _ => @isHomogeneous_complete_nat R _ k)))

/-- Elementary products are homogeneous of the number of cells in their diagram. -/
theorem isHomogeneous_elementaryProd (μ : YoungDiagram) :
    IsHomogeneous (elementaryProd R μ) μ.card := by
  unfold elementaryProd
  apply isHomogeneous_iff_component.mpr
  simpa only [List.map_id, YoungDiagram.sum_rowLens_eq_card] using
    (isHomogeneous_iff_component.mp
      (@IsHomogeneous.list_prod R _ ℕ μ.rowLens (elementary R) id
        (fun k _ => @isHomogeneous_elementary R _ k)))

/-- Power-sum products are homogeneous of the number of cells in their diagram. -/
theorem isHomogeneous_powerSumProd (μ : YoungDiagram) :
    IsHomogeneous (powerSumProd R μ) μ.card := by
  unfold powerSumProd
  apply isHomogeneous_iff_component.mpr
  simpa only [List.attach_map_subtype_val, YoungDiagram.sum_rowLens_eq_card] using
    (isHomogeneous_iff_component.mp
      (@IsHomogeneous.list_prod R _ _ μ.rowLens.attach
        (fun k => powerSum R ⟨k.val, μ.pos_of_mem_rowLens k.val k.property⟩) Subtype.val
        (fun k _ => @isHomogeneous_powerSum R _
          ⟨k.val, μ.pos_of_mem_rowLens k.val k.property⟩)))

/-- Complete products belong to the filtration of their diagram's size. -/
theorem completeProd_mem_degreeFiltration (μ : YoungDiagram) :
    completeProd R μ ∈ degreeFiltration R μ.card := by
  exact IsHomogeneous.mem_degreeFiltration (@isHomogeneous_completeProd R _ μ)

/-- Elementary products belong to the filtration of their diagram's size. -/
theorem elementaryProd_mem_degreeFiltration (μ : YoungDiagram) :
    elementaryProd R μ ∈ degreeFiltration R μ.card := by
  exact IsHomogeneous.mem_degreeFiltration (@isHomogeneous_elementaryProd R _ μ)

/-- Power-sum products belong to the filtration of their diagram's size. -/
theorem powerSumProd_mem_degreeFiltration (μ : YoungDiagram) :
    powerSumProd R μ ∈ degreeFiltration R μ.card := by
  exact IsHomogeneous.mem_degreeFiltration (@isHomogeneous_powerSumProd R _ μ)

end SymmetricFunction
