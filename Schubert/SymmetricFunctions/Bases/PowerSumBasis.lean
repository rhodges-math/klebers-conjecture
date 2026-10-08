import Schubert.SymmetricFunctions.Bases.ProductBasis
import Schubert.SymmetricFunctions.Presentations.PowerSumPresentation

/-! # The power-sum basis

The positive power-sum presentation transports polynomial monomials to row products
indexed by Young diagrams.

## Main results

* `SymmetricFunction.exists_powerSumBasis` gives the basis of power-sum products.
-/

noncomputable section

namespace SymmetricFunction

/-- Power-sum products form a basis over every rational algebra. -/
theorem exists_powerSumBasis (R : Type*) [CommRing R] [Algebra ℚ R] :
    ∃ b : Module.Basis YoungDiagram R (SymmetricFunction R),
      ∀ μ, b μ = powerSumProd R μ := by
  obtain ⟨e, he⟩ := exists_powerSumPresentation R
  obtain ⟨b, hb⟩ := exists_rowProductBasis R (powerSum R) e he
  exact ⟨b, fun μ => hb μ⟩

/-- The basis of row products of positive power sums. -/
def powerSumBasis (R : Type*) [CommRing R] [Algebra ℚ R] :
    Module.Basis YoungDiagram R (SymmetricFunction R) :=
  (exists_powerSumBasis R).choose

/-- A diagram indexes its row-length product of power sums. -/
@[simp]
theorem powerSumBasis_apply {R : Type*} [CommRing R] [Algebra ℚ R] (μ : YoungDiagram) :
    powerSumBasis R μ = powerSumProd R μ := (exists_powerSumBasis R).choose_spec μ

end SymmetricFunction
