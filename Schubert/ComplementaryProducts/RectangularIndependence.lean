import Schubert.ComplementaryProducts.GapBlocks
import Schubert.ComplementaryProducts.Products
import Schubert.ComplementaryProducts.SplittingIndependence
import Mathlib.Data.Finset.Max

/-! # Rectangular independence from componentwise splittings

Gap projection isolates the largest gap of a finite relation. The injective tail map
identifies the isolated block with a subfamily of componentwise splitting products.

## Main results

* `rectangular_independent_of_splittings` transfers splitting independence to rectangular pairs.
* `kleber_linearIndependent` gives rectangular independence over every commutative ring.
-/

noncomputable section

namespace ComplementaryProducts

/-- All diagrams in a complementary pair have the same rectangular gap. -/
theorem gap_eq_of_mem_complementary {a b : ℕ} {p : Sym2 YoungDiagram}
    (hp : p ∈ complementaryPairs a b) {μ ν : YoungDiagram} (hμ : μ ∈ p) (hν : ν ∈ p) :
    gap a μ = gap a ν := by
  obtain ⟨ρ, hρ, rfl⟩ := (mem_complementaryPairs a b p).mp hp
  have he := (gap_rectComplement a b ρ hρ).2
  rcases Sym2.mem_iff.mp hμ with rfl | rfl <;>
    rcases Sym2.mem_iff.mp hν with rfl | rfl
  · rfl
  · exact he.symm
  · exact he
  · rfl

/-- Independence of componentwise splitting products implies rectangular independence. -/
theorem rectangular_independent_of_splittings (R : Type*) [CommRing R] (a b : ℕ)
    (hsplit : ∀ θ : YoungDiagram,
      LinearIndependent R (fun p : splittings θ => schurPairProduct R p.val)) :
    LinearIndependent R (fun p : complementaryPairs a b => schurPairProduct R p.val) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc p
  by_contra hp
  let P := ↥(complementaryPairs a b)
  let gaps (q : P) := gap a q.val.out.1
  have hgap (q : P) (μ : YoungDiagram) (hμ : μ ∈ q.val) : gap a μ = gaps q :=
    gap_eq_of_mem_complementary q.property hμ (Sym2.out_fst_mem q.val)
  let S := Finset.univ.filter (fun q : P => c q ≠ 0)
  have hS : S.Nonempty := ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
  obtain ⟨q0, hq0, hmax⟩ := S.exists_max_image (fun q => toLex (gaps q)) hS
  let g := gaps q0
  have hg : ValidGap a b g := validGap_gap
    (le_of_mem_complementaryPair q0.property (Sym2.out_fst_mem q0.val))
  let B := {q : P // gaps q = g}
  let f : B → splittings (gapShape a b g hg) := fun q =>
    ⟨Sym2.map (fun μ : YoungDiagram => μ.dropRows (a / 2)) q.val.val, by
      obtain ⟨μ, hμ, he⟩ := (mem_complementaryPairs a b q.val.val).mp q.val.property
      have hm : gap a μ = g := (hgap q.val μ
        (by rw [he]; exact Sym2.mem_mk_left _ _)).trans q.property
      rw [he, Sym2.map_mk]
      exact (gapProjection_of_gap_eq R a b g hg μ hμ hm).2⟩
  let j : B → {q : complementaryPairs a b // ∀ μ ∈ q.val, gap a μ = g} := fun q =>
    ⟨q.val, fun μ hμ => (hgap q.val μ hμ).trans q.property⟩
  have hf : Function.Injective f := by
    intro u v huv
    have ht : Sym2.map (fun μ : YoungDiagram => μ.dropRows (a / 2)) (j u).val.val =
        Sym2.map (fun μ : YoungDiagram => μ.dropRows (a / 2)) (j v).val.val :=
      congrArg Subtype.val huv
    have he := tailPair_injective a b g ht
    have heP : (j u).val = (j v).val := Subtype.ext_iff.mp he
    exact Subtype.ext heP
  have hli := (hsplit (gapShape a b g hg)).comp f hf
  have hkill (q : P) (hq : gaps q ≠ g) :
      c q • gapProjection R a b g (schurPairProduct R q.val) = 0 := by
    by_cases hz : c q = 0
    · rw [hz, zero_smul]
    have hm := hmax q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)
    have hl : toLex (gaps q) < toLex g := lt_of_le_of_ne hm
      (by intro he; exact hq (congrArg ofLex he))
    obtain ⟨μ, hμ, he⟩ := (mem_complementaryPairs a b q.val).mp q.property
    have hμg := hgap q μ (by rw [he]; exact Sym2.mem_mk_left _ _)
    rw [he, schurPairProduct_mk, gapProjection_of_gap_lt R a b g μ hμ
      (by rw [hμg]; exact hl), smul_zero]
  have hproject := congrArg (gapProjection R a b g) hc
  rw [map_sum, map_zero] at hproject
  simp only [map_smul] at hproject
  have hz : (∑ q : {q : P // gaps q ≠ g},
      c q.val • gapProjection R a b g (schurPairProduct R q.val.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    exact hkill q.val q.property
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun q : P => gaps q = g)
    (fun q => c q • gapProjection R a b g (schurPairProduct R q.val))
  rw [hz, add_zero] at hsum
  have hblock : (∑ q : B, c q.val • schurPairProduct R (f q).val) = 0 := by
    rw [← hproject, ← hsum]
    apply Finset.sum_congr rfl
    intro q _
    congr 1
    change schurPairProduct R
      (Sym2.map (fun μ : YoungDiagram => μ.dropRows (a / 2)) q.val.val) =
        gapProjection R a b g (schurPairProduct R q.val.val)
    obtain ⟨μ, hμ, he⟩ := (mem_complementaryPairs a b q.val.val).mp q.val.property
    have hm : gap a μ = g := (hgap q.val μ
      (by rw [he]; exact Sym2.mem_mk_left _ _)).trans q.property
    rw [he, Sym2.map_mk, schurPairProduct_mk, schurPairProduct_mk]
    exact (gapProjection_of_gap_eq R a b g hg μ hμ hm).1.symm
  have hc0 := Fintype.linearIndependent_iff.mp hli (fun q : B => c q.val) hblock
    (⟨q0, rfl⟩ : B)
  exact (Finset.mem_filter.mp hq0).2 hc0

/-- Schur products indexed by unordered complementary pairs are linearly independent. -/
theorem kleber_linearIndependent (R : Type*) [CommRing R] (a b : ℕ)
    (_ha : 0 < a) (_hb : 0 < b) :
    LinearIndependent R (fun p : complementaryPairs a b =>
      schurPairProduct R (p : Sym2 YoungDiagram)) :=
  rectangular_independent_of_splittings R a b (splitting_linearIndependent R)

end ComplementaryProducts
