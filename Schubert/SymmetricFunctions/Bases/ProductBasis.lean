import Schubert.Partitions.Multiplicities
import Schubert.SymmetricFunctions.Families.Products
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Bases of row products

A polynomial presentation on positive generators gives a basis of products indexed by the
full row multiset of each Young diagram.

## Main results

* `SymmetricFunction.exists_rowProductBasis` transports the standard polynomial monomial basis.
-/

noncomputable section

private theorem finsupp_prod_map_toMultiset {α M : Type*} [CommMonoid M]
    (d : α →₀ ℕ) (g : α → M) :
    (d.toMultiset.map g).prod = d.prod (fun a n => g a ^ n) := by
  classical
  induction d using Finsupp.induction with
  | zero => simp [Finsupp.toMultiset_zero]
  | @single_add a n d ha hn ih =>
    rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.prod_add, ih,
      Finsupp.toMultiset_single, ← Multiset.coe_mapAddMonoidHom,
      (Multiset.mapAddMonoidHom g).map_nsmul, Multiset.prod_nsmul,
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ => pow_add _),
      Finsupp.prod_single_index (h := fun x n => g x ^ n) (pow_zero _)]
    simp

namespace SymmetricFunction

/-- Transport polynomial monomials and reindex them by positive row multiplicities. -/
def rowProductBasis (R : Type*) [CommSemiring R]
    (e : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R) :
    Module.Basis YoungDiagram R (SymmetricFunction R) :=
  ((MvPolynomial.basisMonomials ℕ+ R).map e.toLinearEquiv).reindex
    YoungDiagram.rowMultiplicityEquiv.symm

/-- A normalized presentation gives the product of all positive row generators. -/
theorem rowProductBasis_apply (R : Type*) [CommSemiring R] (g : ℕ+ → SymmetricFunction R)
    (e : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R)
    (he : ∀ k, e (MvPolynomial.X k) = g k) (μ : YoungDiagram) :
    rowProductBasis R e μ = (μ.rowLens.attach.map
      (fun k => g ⟨k.val, μ.pos_of_mem_rowLens k.val k.property⟩)).prod := by
  classical
  have heval : e.toAlgHom = MvPolynomial.aeval g := by
    apply MvPolynomial.algHom_ext
    intro k
    rw [MvPolynomial.aeval_X]
    exact he k
  have hm : (YoungDiagram.rowMultiplicityEquiv μ).toMultiset =
      (μ.rowLens : Multiset ℕ).attach.map (fun k =>
        (⟨k.val, μ.pos_of_mem_rowLens k.val (Multiset.mem_coe.mp k.property)⟩ : ℕ+)) := by
    apply Multiset.map_injective PNat.coe_injective
    rw [YoungDiagram.rowMultiplicityEquiv_toMultiset]
    exact ((Multiset.map_map (fun k : ℕ+ => k.val)
      (fun k : {x // x ∈ (μ.rowLens : Multiset ℕ)} =>
        (⟨k.val, μ.pos_of_mem_rowLens k.val (Multiset.mem_coe.mp k.property)⟩ : ℕ+))
      (μ.rowLens : Multiset ℕ).attach).trans (Multiset.attach_map_val _)).symm
  rw [rowProductBasis, Module.Basis.reindex_apply, Equiv.symm_symm, Module.Basis.map_apply]
  change e.toAlgHom (MvPolynomial.monomial (YoungDiagram.rowMultiplicityEquiv μ) 1) = _
  rw [heval, MvPolynomial.aeval_monomial,
    map_one, one_mul, ← finsupp_prod_map_toMultiset, hm]
  exact (congrArg Multiset.prod (Multiset.map_map g
    (fun k : {x // x ∈ (μ.rowLens : Multiset ℕ)} =>
      (⟨k.val, μ.pos_of_mem_rowLens k.val (Multiset.mem_coe.mp k.property)⟩ : ℕ+))
    (μ.rowLens : Multiset ℕ).attach)).trans (by rfl)

/-- Polynomial generators give a basis of products indexed by all positive row lengths. -/
theorem exists_rowProductBasis (R : Type*) [CommRing R]
    (g : ℕ+ → SymmetricFunction R)
    (e : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R)
    (he : ∀ k, e (MvPolynomial.X k) = g k) :
    ∃ b : Module.Basis YoungDiagram R (SymmetricFunction R), ∀ μ,
      b μ = (μ.rowLens.attach.map
        (fun k => g ⟨k.val, μ.pos_of_mem_rowLens k.val k.property⟩)).prod :=
  ⟨rowProductBasis R e, rowProductBasis_apply R g e he⟩

end SymmetricFunction
