import Schubert.SymmetricFunctions.Bases.ProductBasis
import Schubert.SymmetricFunctions.Presentations.CompletePresentation

/-! # The complete symmetric-function basis

The positive complete presentation transports polynomial monomials to row products
indexed by Young diagrams, with all row multiplicities retained.

## Main results

* `SymmetricFunction.exists_completeBasis` gives the basis of complete products.
-/

noncomputable section

namespace SymmetricFunction

/-- Complete products form a basis over every commutative ring. -/
theorem exists_completeBasis (R : Type*) [CommRing R] :
    ∃ b : Module.Basis YoungDiagram R (SymmetricFunction R),
      ∀ μ, b μ = completeProd R μ := by
  obtain ⟨e, he⟩ := exists_completePresentation R
  obtain ⟨b, hb⟩ := exists_rowProductBasis R (fun n => complete R (n.val : ℤ)) e he
  refine ⟨b, ?_⟩
  intro μ
  rw [hb, completeProd]
  change (μ.rowLens.attach.map
    (fun (k : {k // k ∈ μ.rowLens}) => complete R (k.val : ℤ))).prod =
      (μ.rowLens.map (fun (k : ℕ) => complete R (k : ℤ))).prod
  exact congrArg List.prod
    (List.attach_map_val (l := μ.rowLens) (f := fun (k : ℕ) => complete R (k : ℤ)))

/-- The basis of row products of complete symmetric functions. -/
def completeBasis (R : Type*) [CommRing R] :
    Module.Basis YoungDiagram R (SymmetricFunction R) :=
  (exists_completeBasis R).choose

/-- A diagram indexes its row-length product of complete functions. -/
@[simp]
theorem completeBasis_apply {R : Type*} [CommRing R] (μ : YoungDiagram) :
    completeBasis R μ = completeProd R μ := (exists_completeBasis R).choose_spec μ

end SymmetricFunction
