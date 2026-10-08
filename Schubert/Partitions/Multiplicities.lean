import Schubert.Partitions.Basic
import TauCeti.Combinatorics.Young.Diagram
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.PNat.Defs

/-! # Multiplicities of positive row lengths

A Young diagram is determined by the multiset of its positive row lengths. Those
multiplicities identify Young diagrams with finitely supported natural functions on
the positive natural numbers.

## Main results

* `YoungDiagram.exists_rowMultiplicityEquiv` gives the equivalence and its row-multiset formula.
* `YoungDiagram.rowMultiplicityEquiv` selects that standard equivalence.

## Implementation notes

Zero row lengths are omitted. The target is the standard finitely supported function type
on positive natural numbers, with natural multiplicities.
-/

noncomputable section

namespace YoungDiagram

/-- Young diagrams correspond to positive-part multiplicities, preserving the full row multiset. -/
theorem exists_rowMultiplicityEquiv :
    ∃ e : YoungDiagram ≃ (ℕ+ →₀ ℕ),
      ∀ μ, (e μ).toMultiset.map (fun k : ℕ+ => k.val) = (μ.rowLens : Multiset ℕ) := by
  let f : YoungDiagram → Multiset ℕ+ := fun μ =>
    (μ.rowLens : Multiset ℕ).attach.map (fun k =>
      (⟨k.val, μ.pos_of_mem_rowLens k.val (Multiset.mem_coe.mp k.property)⟩ : ℕ+))
  have hdown (μ : YoungDiagram) :
      (f μ).map (fun k : ℕ+ => k.val) = (μ.rowLens : Multiset ℕ) := by
    exact (Multiset.map_map (fun k : ℕ+ => k.val)
      (fun k : {x // x ∈ (μ.rowLens : Multiset ℕ)} =>
        (⟨k.val, μ.pos_of_mem_rowLens k.val (Multiset.mem_coe.mp k.property)⟩ : ℕ+))
      (μ.rowLens : Multiset ℕ).attach).trans (Multiset.attach_map_val _)
  have hinj : Function.Injective f := by
    intro μ ν h
    have hrows : (μ.rowLens : Multiset ℕ) = (ν.rowLens : Multiset ℕ) := by
      rw [← hdown μ, ← hdown ν, h]
    have hl := congrArg (fun s : Multiset ℕ => s.sort (· ≥ ·)) hrows
    rw [YoungDiagram.sort_coe_rowLens, YoungDiagram.sort_coe_rowLens] at hl
    exact YoungDiagram.equivListRowLens.injective (Subtype.ext hl)
  have hsurj : Function.Surjective f := by
    intro s
    let l := (s.map (fun k : ℕ+ => k.val)).sort (· ≥ ·)
    have hs : l.SortedGE := (Multiset.pairwise_sort _ _).sortedGE
    have hpos : ∀ k ∈ l, 0 < k := by
      intro k hk
      obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp ((Multiset.mem_sort (· ≥ ·)).mp hk)
      exact r.property
    refine ⟨YoungDiagram.ofRowLens l hs, ?_⟩
    apply Multiset.map_injective PNat.coe_injective
    rw [hdown, YoungDiagram.rowLens_ofRowLens_eq_self hpos]
    exact Multiset.sort_eq _ _
  let e := (Equiv.ofBijective f ⟨hinj, hsurj⟩).trans Multiset.toFinsupp.toEquiv
  refine ⟨e, ?_⟩
  intro μ
  change (Multiset.toFinsupp (f μ)).toMultiset.map (fun k : ℕ+ => k.val) = _
  rw [Multiset.toFinsupp_toMultiset, hdown]

/-- The standard equivalence between Young diagrams and positive row-length multiplicities. -/
def rowMultiplicityEquiv : YoungDiagram ≃ (ℕ+ →₀ ℕ) :=
  exists_rowMultiplicityEquiv.choose

/-- The multiplicity equivalence preserves the multiset of all positive row lengths. -/
theorem rowMultiplicityEquiv_toMultiset (μ : YoungDiagram) :
    (rowMultiplicityEquiv μ).toMultiset.map (fun k : ℕ+ => k.val) =
      (μ.rowLens : Multiset ℕ) :=
  exists_rowMultiplicityEquiv.choose_spec μ

end YoungDiagram
