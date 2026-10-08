import Schubert.ComplementaryProducts.Indices
import Schubert.SymmetricFunctions.Families.Schur
import Schubert.SymmetricFunctions.SymplecticCharacters.Basic

/-! # Unordered products of symmetric functions

Commutativity defines Schur, monomial and symplectic products on unordered pairs of diagrams,
including pairs with repeated entries.

## Main results

* `ComplementaryProducts.schurPairProduct_mk` evaluates a Schur pair product.
* `ComplementaryProducts.monomialPairProduct_mk` evaluates a monomial pair product.
* `ComplementaryProducts.symplecticPairProduct_mk` evaluates a symplectic-character pair product.
-/

noncomputable section

namespace ComplementaryProducts

/-- Multiply the Schur functions indexed by an unordered pair of diagrams. -/
def schurPairProduct (R : Type*) [CommRing R] :
    Sym2 YoungDiagram → SymmetricFunction R :=
  Sym2.lift ⟨fun α β => SymmetricFunction.schur R α * SymmetricFunction.schur R β,
    fun _ _ => mul_comm _ _⟩

/-- Multiply the monomial functions indexed by an unordered pair of diagrams. -/
def monomialPairProduct (R : Type*) [CommRing R] :
    Sym2 YoungDiagram → SymmetricFunction R :=
  Sym2.lift ⟨fun α β => SymmetricFunction.monomial R α * SymmetricFunction.monomial R β,
    fun _ _ => mul_comm _ _⟩

/-- Multiply symplectic universal characters indexed by an unordered pair of diagrams. -/
def symplecticPairProduct (R : Type*) [CommRing R] :
    Sym2 YoungDiagram → SymmetricFunction R :=
  Sym2.lift ⟨fun α β =>
    SymmetricFunction.symplecticCharacter R α * SymmetricFunction.symplecticCharacter R β,
    fun _ _ => mul_comm _ _⟩

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A Schur pair product is the product of the two Schur functions. -/
theorem schurPairProduct_mk (α β : YoungDiagram) :
    schurPairProduct R s(α, β) =
      SymmetricFunction.schur R α * SymmetricFunction.schur R β := rfl

/-- A monomial pair product is the product of the two monomial functions. -/
theorem monomialPairProduct_mk (α β : YoungDiagram) :
    monomialPairProduct R s(α, β) =
      SymmetricFunction.monomial R α * SymmetricFunction.monomial R β := rfl

/-- A symplectic pair product is the product of its two symplectic characters. -/
theorem symplecticPairProduct_mk (α β : YoungDiagram) :
    symplecticPairProduct R s(α, β) =
      SymmetricFunction.symplecticCharacter R α * SymmetricFunction.symplecticCharacter R β := rfl

/-- Coefficient-ring maps preserve Schur pair products. -/
theorem map_schurPairProduct (φ : R →+* S) (p : Sym2 YoungDiagram) :
    SymmetricFunction.map φ (schurPairProduct R p) = schurPairProduct S p := by
  refine Sym2.ind (fun α β => ?_) p
  rw [schurPairProduct_mk, schurPairProduct_mk, map_mul,
    SymmetricFunction.map_schur, SymmetricFunction.map_schur]

/-- Coefficient-ring maps preserve monomial pair products. -/
theorem map_monomialPairProduct (φ : R →+* S) (p : Sym2 YoungDiagram) :
    SymmetricFunction.map φ (monomialPairProduct R p) = monomialPairProduct S p := by
  refine Sym2.ind (fun α β => ?_) p
  rw [monomialPairProduct_mk, monomialPairProduct_mk, map_mul,
    SymmetricFunction.map_monomial, SymmetricFunction.map_monomial]

/-- Coefficient-ring maps preserve universal-character pair products. -/
theorem map_symplecticPairProduct (φ : R →+* S) (p : Sym2 YoungDiagram) :
    SymmetricFunction.map φ (symplecticPairProduct R p) = symplecticPairProduct S p := by
  refine Sym2.ind (fun α β => ?_) p
  rw [symplecticPairProduct_mk, symplecticPairProduct_mk, map_mul,
    SymmetricFunction.map_symplecticCharacter, SymmetricFunction.map_symplecticCharacter]

/-- Pairing with the empty diagram leaves a Schur function. -/
theorem schurPairProduct_bot (α : YoungDiagram) :
    schurPairProduct R s(α, ⊥) = SymmetricFunction.schur R α := by
  rw [schurPairProduct_mk, SymmetricFunction.schur_bot, mul_one]

/-- Pairing with the empty diagram leaves a monomial function. -/
theorem monomialPairProduct_bot (α : YoungDiagram) :
    monomialPairProduct R s(α, ⊥) = SymmetricFunction.monomial R α := by
  rw [monomialPairProduct_mk, SymmetricFunction.monomial_bot, mul_one]

/-- Pairing with the empty diagram leaves a universal character. -/
theorem symplecticPairProduct_bot (α : YoungDiagram) :
    symplecticPairProduct R s(α, ⊥) = SymmetricFunction.symplecticCharacter R α := by
  rw [symplecticPairProduct_mk, SymmetricFunction.symplecticCharacter_bot, mul_one]

end ComplementaryProducts
