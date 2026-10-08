import Schubert.ComplementaryProducts.Gap
import Schubert.ComplementaryProducts.Indices
import Schubert.Partitions.Rows

/-!
# Fixed-gap tails of complementary pairs

Complementation preserves opposite-row differences. Removing half the rows gives the
prescribed gap shape, and the unordered tail pair retains every fixed-gap complementary pair.

## Main results

* `gap_rectComplement`: a contained diagram has a valid complement-invariant gap.
* `dropRows_add_dropRows_complement`: complementary tails sum to the gap shape.
* `tailPair_injective`: the unordered tail map is injective in a fixed gap family.
-/

noncomputable section

namespace ComplementaryProducts

/-- A contained diagram has a valid gap vector, unchanged by rectangular complementation. -/
theorem gap_rectComplement (a b : ℕ) (μ : YoungDiagram)
    (hμ : μ ≤ YoungDiagram.rectangle a b) :
    ValidGap a b (gap a μ) ∧ gap a (YoungDiagram.rectComplement a b μ) = gap a μ := by
  refine ⟨validGap_gap hμ, ?_⟩
  funext i
  have hi : i.val < a := by have := i.isLt; omega
  have hr : a - 1 - i.val < a := by omega
  have he : a - 1 - (a - 1 - i.val) = i.val := by omega
  rw [gap_apply, gap_apply, YoungDiagram.rowLen_rectComplement,
    YoungDiagram.rowLen_rectComplement, ite_eq_left hi, ite_eq_left hr, he]
  have hb := YoungDiagram.rowLen_le_of_le_rectangle hμ i.val
  have hbr := YoungDiagram.rowLen_le_of_le_rectangle hμ (a - 1 - i.val)
  omega

/-- Half-row deletions of a fixed-gap complementary pair sum to its prescribed shape. -/
theorem dropRows_add_dropRows_complement (a b : ℕ) (g : Fin (a / 2) → ℕ)
    (hg : ValidGap a b g) (μ : YoungDiagram) (hμ : μ ≤ YoungDiagram.rectangle a b)
    (hgap : gap a μ = g) :
    μ.dropRows (a / 2) + (YoungDiagram.rectComplement a b μ).dropRows (a / 2) =
      gapShape a b g hg := by
  apply YoungDiagram.rowLen_injective
  funext i
  rw [YoungDiagram.rowLen_add, YoungDiagram.rowLen_dropRows,
    YoungDiagram.rowLen_dropRows, YoungDiagram.rowLen_rectComplement]
  by_cases hi : i < a - a / 2
  · have ht : a / 2 + i < a := by omega
    rw [ite_eq_left ht, rowLen_gapShape a b g hg ⟨i, hi⟩]
    dsimp only at *
    split_ifs with hp
    · have he : a - 1 - (a / 2 + i) = a / 2 + i := by omega
      rw [he]
      have hb := YoungDiagram.rowLen_le_of_le_rectangle hμ (a / 2 + i)
      omega
    · have hj : a - a / 2 - 1 - i < a / 2 := by omega
      have he : a - 1 - (a - a / 2 - 1 - i) = a / 2 + i := by omega
      have he' : a - 1 - (a / 2 + i) = a - a / 2 - 1 - i := by omega
      have hd := congrFun hgap ⟨a - a / 2 - 1 - i, hj⟩
      rw [gap_apply] at hd
      dsimp only at hd
      rw [he] at hd
      have hb := YoungDiagram.rowLen_le_of_le_rectangle hμ (a - a / 2 - 1 - i)
      have hl := μ.rowLen_anti (a - a / 2 - 1 - i) (a / 2 + i) (by omega)
      rw [he']
      omega
  · have ht : ¬a / 2 + i < a := by omega
    rw [ite_eq_right ht, rowLen_gapShape_eq_zero a b g hg (by omega),
      YoungDiagram.rowLen_eq_zero_of_le_rectangle hμ (by omega)]

/-- Equal gaps and equal tails recover the entire diagrams. -/
theorem eq_of_gap_dropRows {a : ℕ} {μ ν : YoungDiagram}
    (hg : gap a μ = gap a ν) (ht : μ.dropRows (a / 2) = ν.dropRows (a / 2)) : μ = ν := by
  have hr (i : ℕ) (hi : a / 2 ≤ i) : μ.rowLen i = ν.rowLen i := by
    have h := congrArg (fun ρ : YoungDiagram => ρ.rowLen (i - a / 2)) ht
    rw [YoungDiagram.rowLen_dropRows, YoungDiagram.rowLen_dropRows,
      Nat.add_sub_of_le hi] at h
    exact h
  apply YoungDiagram.rowLen_injective
  funext i
  by_cases hi : a / 2 ≤ i
  · exact hr i hi
  · have hil : i < a / 2 := by omega
    have hrev : a / 2 ≤ a - 1 - i := by omega
    have hrows := hr (a - 1 - i) hrev
    have hd := congrFun hg ⟨i, hil⟩
    rw [gap_apply, gap_apply] at hd
    dsimp only at hd
    rw [hrows] at hd
    have hm := μ.rowLen_anti i (a - 1 - i) (by omega)
    have hn := ν.rowLen_anti i (a - 1 - i) (by omega)
    omega

/-- The unordered tail map is injective on the complementary pairs with a fixed gap. -/
theorem tailPair_injective (a b : ℕ) (g : Fin (a / 2) → ℕ) :
    Function.Injective (fun p : {p : complementaryPairs a b //
        ∀ μ ∈ (p : Sym2 YoungDiagram), gap a μ = g} =>
      Sym2.map (fun μ : YoungDiagram => μ.dropRows (a / 2)) (p.val : Sym2 YoungDiagram)) := by
  intro p q hpq
  obtain ⟨μ, hμ, hp⟩ := (mem_complementaryPairs a b (p.val : Sym2 YoungDiagram)).mp
    p.val.property
  obtain ⟨ν, hν, hq⟩ := (mem_complementaryPairs a b (q.val : Sym2 YoungDiagram)).mp
    q.val.property
  have hgm : gap a μ = g := p.property μ (by rw [hp]; exact Sym2.mem_mk_left _ _)
  have hgn : gap a ν = g := q.property ν (by rw [hq]; exact Sym2.mem_mk_left _ _)
  have hgcn : gap a (YoungDiagram.rectComplement a b ν) = g :=
    q.property _ (by rw [hq]; exact Sym2.mem_mk_right _ _)
  change Sym2.map (fun ρ : YoungDiagram => ρ.dropRows (a / 2))
    (p.val : Sym2 YoungDiagram) =
    Sym2.map (fun ρ : YoungDiagram => ρ.dropRows (a / 2)) (q.val : Sym2 YoungDiagram) at hpq
  rw [hp, hq, Sym2.map_mk, Sym2.map_mk] at hpq
  apply Subtype.ext
  apply Subtype.ext
  rw [hp, hq]
  rcases Sym2.eq_iff.mp hpq with ⟨h, _⟩ | ⟨h, _⟩
  · have he := eq_of_gap_dropRows (hgm.trans hgn.symm) h
    rw [he]
  · have he := eq_of_gap_dropRows (hgm.trans hgcn.symm) h
    rw [he]
    exact complementaryPair_complement hν

end ComplementaryProducts
