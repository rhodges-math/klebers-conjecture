import Schubert.Partitions.Rectangle
import Mathlib.Data.Sym.Sym2

/-!
# Finite families of unordered diagram pairs

Componentwise splittings have a prescribed sum. Rectangular complementary pairs consist of
a contained diagram and its rotated complement.

## Main results

* `mem_splittings` characterizes splittings by their componentwise sum.
* `mem_complementaryPairs` characterizes rectangular complementary pairs.
* `complementaryPair_eq_iff` recovers a pair's representative up to complementation.
-/

open scoped Classical

namespace ComplementaryProducts

/-- The unordered pairs of diagrams whose componentwise sum is `θ`. -/
noncomputable def splittings (θ : YoungDiagram) : Finset (Sym2 YoungDiagram) :=
  (((YoungDiagram.finite_Iic θ).toFinset.product (YoungDiagram.finite_Iic θ).toFinset).filter
    (fun q => q.1 + q.2 = θ)).image (fun q => s(q.1, q.2))

/-- Membership in the splitting family is exactly the prescribed sum condition. -/
theorem mem_splittings (θ : YoungDiagram) (p : Sym2 YoungDiagram) :
    p ∈ splittings θ ↔ ∃ α β, p = s(α, β) ∧ α + β = θ := by
  constructor
  · intro hp
    obtain ⟨⟨α, β⟩, h, he⟩ := Finset.mem_image.mp hp
    exact ⟨α, β, he.symm, (Finset.mem_filter.mp h).2⟩
  · rintro ⟨α, β, rfl, h⟩
    apply Finset.mem_image.mpr
    refine ⟨(α, β), Finset.mem_filter.mpr ⟨?_, h⟩, rfl⟩
    apply Finset.mem_product.mpr
    constructor
    · simpa using (h ▸ YoungDiagram.le_self_add α β)
    · simpa using (h ▸ YoungDiagram.le_add_self α β)

/-- An explicitly presented pair is a splitting precisely when its sum is the target. -/
@[simp] theorem mk_mem_splittings (θ α β : YoungDiagram) :
    s(α, β) ∈ splittings θ ↔ α + β = θ := by
  rw [mem_splittings]
  constructor
  · rintro ⟨γ, δ, h, hs⟩
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hs
    · simpa [add_comm] using hs
  · exact fun h => ⟨α, β, rfl, h⟩

/-- Every member diagram of a splitting is contained in its componentwise sum. -/
theorem le_of_mem_splitting {θ μ : YoungDiagram} {p : Sym2 YoungDiagram}
    (hp : p ∈ splittings θ) (hμ : μ ∈ p) : μ ≤ θ := by
  obtain ⟨α, β, rfl, h⟩ := (mem_splittings θ p).mp hp
  have hα : α ≤ θ := h ▸ YoungDiagram.le_self_add α β
  have hβ : β ≤ θ := h ▸ YoungDiagram.le_add_self α β
  rcases Sym2.mem_iff.mp hμ with rfl | rfl
  · exact hα
  · exact hβ

/-- The sizes of the diagrams in a splitting sum to the target's size. -/
theorem card_add_of_mem_splittings {θ α β : YoungDiagram}
    (h : s(α, β) ∈ splittings θ) : α.card + β.card = θ.card := by
  rw [← YoungDiagram.card_add, (mk_mem_splittings θ α β).mp h]

/-- Every diagram admits the splitting into itself and the empty diagram. -/
theorem splittings_nonempty (θ : YoungDiagram) : (splittings θ).Nonempty := by
  refine ⟨s(θ, ⊥), (mk_mem_splittings θ θ ⊥).mpr ?_⟩
  simpa only [← YoungDiagram.zero_eq_bot] using add_zero θ

/-- Fixing one member of a splitting determines the other member. -/
theorem splitting_recovery {θ μ ν ρ : YoungDiagram}
    (hν : s(μ, ν) ∈ splittings θ) (hρ : s(μ, ρ) ∈ splittings θ) : ν = ρ := by
  have h := (mk_mem_splittings θ μ ν).mp hν
  have h' := (mk_mem_splittings θ μ ρ).mp hρ
  exact _root_.add_left_cancel (h.trans h'.symm)

/-- The empty diagram has just the pair of empty diagrams as its splitting. -/
@[simp] theorem splittings_bot : splittings ⊥ = {s(⊥, ⊥)} := by
  ext p
  rw [mem_splittings, Finset.mem_singleton]
  constructor
  · rintro ⟨μ, ν, rfl, h⟩
    have hμ : μ = ⊥ := le_bot_iff.mp (h ▸ YoungDiagram.le_self_add μ ν)
    have hν : ν = ⊥ := le_bot_iff.mp (h ▸ YoungDiagram.le_add_self μ ν)
    rw [hμ, hν]
  · rintro rfl
    refine ⟨⊥, ⊥, rfl, ?_⟩
    simpa only [← YoungDiagram.zero_eq_bot] using add_zero (0 : YoungDiagram)

/-- The unordered pairs of diagrams complementary in an `a` by `b` rectangle. -/
noncomputable def complementaryPairs (a b : ℕ) : Finset (Sym2 YoungDiagram) :=
  (YoungDiagram.finite_Iic (YoungDiagram.rectangle a b)).toFinset.image
    (fun μ => s(μ, YoungDiagram.rectComplement a b μ))

/-- A complementary pair is represented by a contained diagram and its complement. -/
theorem mem_complementaryPairs (a b : ℕ) (p : Sym2 YoungDiagram) :
    p ∈ complementaryPairs a b ↔
      ∃ μ ≤ YoungDiagram.rectangle a b, p = s(μ, YoungDiagram.rectComplement a b μ) := by
  simp only [complementaryPairs, Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_Iic]
  constructor
  · rintro ⟨μ, hμ, h⟩
    exact ⟨μ, hμ, h.symm⟩
  · rintro ⟨μ, hμ, h⟩
    exact ⟨μ, hμ, h.symm⟩

/-- A contained diagram and its complement form a member of the complementary family. -/
theorem mk_mem_complementaryPairs {a b : ℕ} {μ : YoungDiagram}
    (hμ : μ ≤ YoungDiagram.rectangle a b) :
    s(μ, YoungDiagram.rectComplement a b μ) ∈ complementaryPairs a b :=
  (mem_complementaryPairs a b _).mpr ⟨μ, hμ, rfl⟩

/-- Every diagram occurring in a complementary pair is contained in the rectangle. -/
theorem le_of_mem_complementaryPair {a b : ℕ} {μ : YoungDiagram} {p : Sym2 YoungDiagram}
    (hp : p ∈ complementaryPairs a b) (hμ : μ ∈ p) :
    μ ≤ YoungDiagram.rectangle a b := by
  obtain ⟨ν, hν, rfl⟩ := (mem_complementaryPairs a b p).mp hp
  rcases Sym2.mem_iff.mp hμ with rfl | rfl
  · exact hν
  · exact YoungDiagram.rectComplement_le_rectangle a b ν

/-- Choosing the other diagram represents the same unordered complementary pair. -/
theorem complementaryPair_complement {a b : ℕ} {μ : YoungDiagram}
    (hμ : μ ≤ YoungDiagram.rectangle a b) :
    s(YoungDiagram.rectComplement a b μ,
      YoungDiagram.rectComplement a b (YoungDiagram.rectComplement a b μ)) =
      s(μ, YoungDiagram.rectComplement a b μ) := by
  rw [YoungDiagram.rectComplement_rectComplement hμ]
  exact Sym2.eq_swap

/-- Complementary pairs agree exactly up to choosing the other member as representative. -/
theorem complementaryPair_eq_iff {a b : ℕ} {μ ν : YoungDiagram}
    (hν : ν ≤ YoungDiagram.rectangle a b) :
    s(μ, YoungDiagram.rectComplement a b μ) = s(ν, YoungDiagram.rectComplement a b ν) ↔
      μ = ν ∨ μ = YoungDiagram.rectComplement a b ν := by
  rw [Sym2.eq_iff]
  constructor
  · intro h
    exact h.imp And.left And.left
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, YoungDiagram.rectComplement_rectComplement hν⟩

/-- Complementary pairs are distinct when neither choice of representative agrees. -/
theorem complementaryPair_ne_iff {a b : ℕ} {μ ν : YoungDiagram}
    (hν : ν ≤ YoungDiagram.rectangle a b) :
    s(μ, YoungDiagram.rectComplement a b μ) ≠ s(ν, YoungDiagram.rectComplement a b ν) ↔
      μ ≠ ν ∧ μ ≠ YoungDiagram.rectComplement a b ν := by
  exact (not_congr (complementaryPair_eq_iff (μ := μ) hν)).trans not_or

/-- Either member of a complementary pair recovers the entire unordered pair. -/
theorem complementaryPair_recovery {a b : ℕ} {μ : YoungDiagram} {p : Sym2 YoungDiagram}
    (hp : p ∈ complementaryPairs a b) (hμ : μ ∈ p) :
    p = s(μ, YoungDiagram.rectComplement a b μ) := by
  obtain ⟨ν, hν, rfl⟩ := (mem_complementaryPairs a b p).mp hp
  rcases Sym2.mem_iff.mp hμ with rfl | rfl
  · rfl
  · exact (complementaryPair_complement hν).symm

/-- An explicitly presented pair is complementary exactly when its second member is the
rectangular complement of its contained first member. -/
theorem mk_mem_complementaryPairs_iff (a b : ℕ) (μ ν : YoungDiagram) :
    s(μ, ν) ∈ complementaryPairs a b ↔
      μ ≤ YoungDiagram.rectangle a b ∧ ν = YoungDiagram.rectComplement a b μ := by
  constructor
  · intro hp
    exact ⟨le_of_mem_complementaryPair hp (Sym2.mem_mk_left μ ν),
      Sym2.congr_right.mp (complementaryPair_recovery hp (Sym2.mem_mk_left μ ν))⟩
  · rintro ⟨hμ, rfl⟩
    exact mk_mem_complementaryPairs hμ

/-- The two diagrams of a complementary pair have total size `a * b`. -/
theorem card_add_of_complementaryPair {a b : ℕ} {μ ν : YoungDiagram}
    (hp : s(μ, ν) ∈ complementaryPairs a b) : μ.card + ν.card = a * b := by
  have hμ := le_of_mem_complementaryPair hp (Sym2.mem_mk_left μ ν)
  have h := complementaryPair_recovery hp (Sym2.mem_mk_left μ ν)
  have he := Sym2.congr_right.mp h
  rw [he]
  exact YoungDiagram.card_add_rectComplement hμ

/-- Every rectangle has a complementary pair, including rectangles with zero dimensions. -/
theorem complementaryPairs_nonempty (a b : ℕ) : (complementaryPairs a b).Nonempty :=
  ⟨s(YoungDiagram.rectangle a b,
      YoungDiagram.rectComplement a b (YoungDiagram.rectangle a b)),
    mk_mem_complementaryPairs le_rfl⟩

/-- An empty rectangle has just the pair of empty diagrams as its complementary family. -/
theorem complementaryPairs_eq_singleton {a b : ℕ}
    (h : YoungDiagram.rectangle a b = ⊥) : complementaryPairs a b = {s(⊥, ⊥)} := by
  have hc : YoungDiagram.rectComplement a b ⊥ = ⊥ :=
    le_bot_iff.mp (h ▸ YoungDiagram.rectComplement_le_rectangle a b ⊥)
  ext p
  rw [mem_complementaryPairs, Finset.mem_singleton]
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    have he : μ = ⊥ := le_bot_iff.mp (h ▸ hμ)
    rw [he, hc]
  · rintro rfl
    exact ⟨⊥, h.symm ▸ le_rfl, by rw [hc]⟩

/-- A rectangle with no rows has only the empty complementary pair. -/
@[simp] theorem complementaryPairs_zero_left (b : ℕ) :
    complementaryPairs 0 b = {s(⊥, ⊥)} := by
  apply complementaryPairs_eq_singleton
  apply YoungDiagram.rowLen_injective
  funext i
  simp

/-- A rectangle with no columns has only the empty complementary pair. -/
@[simp] theorem complementaryPairs_zero_right (a : ℕ) :
    complementaryPairs a 0 = {s(⊥, ⊥)} := by
  apply complementaryPairs_eq_singleton
  apply YoungDiagram.rowLen_injective
  funext i
  simp

end ComplementaryProducts
