import Schubert.ComplementaryProducts.Products
import Schubert.Partitions.SingleShapes
import Schubert.SymmetricFunctions.Families.PowerSumIdentities
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic

/-! # Complementary monomial products in characteristic two

Over every commutative ring `m_(1)^2 = m_(2) + 2 m_(1,1)`. In characteristic two this makes the
two complementary products in a row of length two equal, so the family of complementary monomial
products is linearly dependent.

## Main results

* `monomial_singleRow_one_sq_eq_add` gives `m_(1)^2 = m_(2) + 2 m_(1,1)` over every commutative
  ring.
* `monomial_singleRow_one_sq_charP_two` gives `m_(1)^2 = m_(2)` in characteristic two.
* `not_monomial_linearIndependent_charP_two` gives dependence of the complementary family of the
  row of length two over every commutative ring of characteristic two.
* `monomial_singleRow_one_sq`, `monomialPairProduct_char_two` and
  `not_monomial_linearIndependent_char_two` state these facts over `ZMod 2`.
-/

noncomputable section

namespace ComplementaryProducts

open SymmetricFunction

/-- The square of the degree-one monomial function: `m_(1)^2 = m_(2) + 2 m_(1,1)`. -/
theorem monomial_singleRow_one_sq_eq_add (R : Type*) [CommRing R] :
    monomial R (YoungDiagram.singleRow 1) ^ 2 =
      monomial R (YoungDiagram.singleRow 2) +
        2 * monomial R (YoungDiagram.singleColumn 2) := by
  have h := powerSum_one_sq R
  rw [powerSum_eq_monomial_singleRow, powerSum_eq_monomial_singleRow, elementary_eq_monomial,
    YoungDiagram.diagramOf_ones_eq_singleColumn] at h
  simpa only [PNat.val_ofNat] using h

/-- In characteristic two the degree-one monomial function squares to `m_(2)`. -/
theorem monomial_singleRow_one_sq_charP_two (R : Type*) [CommRing R] [CharP R 2] :
    monomial R (YoungDiagram.singleRow 1) ^ 2 = monomial R (YoungDiagram.singleRow 2) := by
  have h2 : (2 : SymmetricFunction R) = 0 := by
    rw [← map_ofNat (algebraMap R (SymmetricFunction R)) 2, CharTwo.two_eq_zero, map_zero]
  rw [monomial_singleRow_one_sq_eq_add, h2, zero_mul, add_zero]

/-- In characteristic two the two complementary monomial products in the row of length two
coincide. -/
theorem monomialPairProduct_charP_two (R : Type*) [CommRing R] [CharP R 2] :
    monomialPairProduct R s(⊥, YoungDiagram.rectangle 1 2) =
      monomialPairProduct R
        s(YoungDiagram.rectangle 1 1, YoungDiagram.rectangle 1 1) := by
  rw [monomialPairProduct_mk, monomialPairProduct_mk, monomial_bot, one_mul, ← pow_two]
  exact (monomial_singleRow_one_sq_charP_two R).symm

/-- Over every commutative ring of characteristic two, the complementary monomial products of
the row of length two are linearly dependent. -/
theorem not_monomial_linearIndependent_charP_two (R : Type*) [CommRing R] [CharP R 2] :
    ¬ LinearIndependent R (fun p : complementaryPairs 1 2 =>
      monomialPairProduct R (p : Sym2 YoungDiagram)) := by
  classical
  have : Nontrivial R := CharP.nontrivial_of_char_ne_one (R := R) (v := 2) (by norm_num)
  have hbot : YoungDiagram.rectComplement 1 2 ⊥ = YoungDiagram.rectangle 1 2 := by
    apply YoungDiagram.rowLen_injective
    funext i
    simp
  have hrow : YoungDiagram.rectComplement 1 2 (YoungDiagram.rectangle 1 1) =
      YoungDiagram.rectangle 1 1 := by
    apply YoungDiagram.rowLen_injective
    funext i
    by_cases hi : i < 1
    · have hi0 : i = 0 := by omega
      subst i
      simp
    · simp [hi]
  have hle : YoungDiagram.rectangle 1 1 ≤ YoungDiagram.rectangle 1 2 := by
    intro ⟨i, j⟩ hij
    have h := (YoungDiagram.mem_rectangle 1 1 i j).mp hij
    exact (YoungDiagram.mem_rectangle 1 2 i j).mpr ⟨h.1, by omega⟩
  let p : complementaryPairs 1 2 := ⟨s(⊥, YoungDiagram.rectangle 1 2), by
    rw [← hbot]
    exact mk_mem_complementaryPairs bot_le⟩
  let q : complementaryPairs 1 2 :=
    ⟨s(YoungDiagram.rectangle 1 1, YoungDiagram.rectangle 1 1), by
      simpa only [hrow] using mk_mem_complementaryPairs hle⟩
  intro hli
  have he : p = q := hli.injective (monomialPairProduct_charP_two R)
  have he' := congrArg Subtype.val he
  change s(⊥, YoungDiagram.rectangle 1 2) =
    s(YoungDiagram.rectangle 1 1, YoungDiagram.rectangle 1 1) at he'
  have hz : (⊥ : YoungDiagram) = YoungDiagram.rectangle 1 1 := by
    rcases Sym2.eq_iff.mp he' with h | h <;> exact h.1
  have hc := congrArg YoungDiagram.card hz
  simp [YoungDiagram.card] at hc

/-- The characteristic-two monomial of a single cell squares to the monomial of a two-cell row. -/
theorem monomial_singleRow_one_sq :
    monomial (ZMod 2) (YoungDiagram.singleRow 1) ^ 2 =
      monomial (ZMod 2) (YoungDiagram.singleRow 2) :=
  monomial_singleRow_one_sq_charP_two (ZMod 2)

/-- The two complementary monomial products in the row of length two coincide over `ZMod 2`. -/
theorem monomialPairProduct_char_two :
    monomialPairProduct (ZMod 2) s(⊥, YoungDiagram.rectangle 1 2) =
      monomialPairProduct (ZMod 2)
        s(YoungDiagram.rectangle 1 1, YoungDiagram.rectangle 1 1) :=
  monomialPairProduct_charP_two (ZMod 2)

/-- Over `ZMod 2` the complementary monomial products of the row of length two are dependent. -/
theorem not_monomial_linearIndependent_char_two :
    ¬ LinearIndependent (ZMod 2) (fun p : complementaryPairs 1 2 =>
      monomialPairProduct (ZMod 2) (p : Sym2 YoungDiagram)) :=
  not_monomial_linearIndependent_charP_two (ZMod 2)

end ComplementaryProducts
