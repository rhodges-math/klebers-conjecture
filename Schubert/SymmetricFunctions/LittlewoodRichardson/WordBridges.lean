import Schubert.Partitions.Skew.Word
import Schubert.SymmetricFunctions.LittlewoodRichardson.FiniteAlphabet.Word

/-! # Positive and zero-based lattice words

Subtracting one from positive labels identifies lattice inequalities with finite-alphabet
prefix inequalities. The converse for one alphabet requires a bound on all labels.

## Main results

* `isLatticeWord_iff_latticeFrom` gives the bounded-alphabet bridge.
* `isLatticeWord_iff_all_latticeFrom` tests all finite alphabets without a label bound.

## Implementation notes

Positive labels start at one; finite-alphabet labels start at zero. An empty alphabet can
only represent the empty positive word under the bounded-alphabet hypothesis.
-/

namespace YoungDiagram

open SymmetricFunction.FiniteAlphabet
open SymmetricFunction.FiniteAlphabet.LittlewoodRichardson

private theorem count_take_natPred (w : List ℕ+) (k : ℕ) (i : ℕ+) :
    ((w.map PNat.natPred).take k).count i.natPred = (w.take k).count i := by
  rw [← List.map_take, List.count_map_of_injective _ _ PNat.natPred_injective]

/-- A positive lattice word is lattice from zero in every finite alphabet. -/
theorem isLatticeFrom_zero_of_latticeWord {w : List ℕ+} (h : IsLatticeWord w) (d : ℕ) :
    IsLatticeFrom (0 : IntWeight d) (w.map PNat.natPred) := by
  intro k hk
  refine antitone_of_succ fun i hi => ?_
  have hc := h k (by simpa only [List.length_map] using hk) (Nat.succPNat i)
  have he : (Nat.succPNat i + 1).natPred = i + 1 := by
    simp [PNat.natPred, PNat.add_coe]
  simp only [Pi.add_apply, Pi.zero_apply, zero_add]
  have hcur := count_take_natPred w k (Nat.succPNat i)
  have hnext := count_take_natPred w k (Nat.succPNat i + 1)
  simp only [Nat.natPred_succPNat] at hcur
  rw [he] at hnext
  rw [hcur, hnext]
  exact_mod_cast hc

/-- A bounded positive word is lattice exactly when its zero-based word is lattice from zero. -/
theorem isLatticeWord_iff_latticeFrom (w : List ℕ+) (d : ℕ)
    (hb : ∀ x ∈ w, x.val ≤ d) :
    IsLatticeWord w ↔ IsLatticeFrom (0 : IntWeight d) (w.map PNat.natPred) := by
  refine ⟨fun h => isLatticeFrom_zero_of_latticeWord h d, ?_⟩
  intro h k hk i
  by_cases hi : i.val < d
  · have hn : i.natPred + 1 < d := by rw [PNat.natPred_add_one]; exact hi
    have hs := h k (by simpa only [List.length_map] using hk)
      (show (⟨i.natPred, by omega⟩ : Fin d) ≤ ⟨i.natPred + 1, hn⟩ from
        Fin.mk_le_mk.mpr (Nat.le_succ _))
    have he : (i + 1).natPred = i.natPred + 1 := by
      have hp := i.pos
      simp only [PNat.natPred, PNat.add_coe, PNat.one_coe]
      omega
    simp only [Pi.add_apply, Pi.zero_apply, zero_add] at hs
    rw [← he, count_take_natPred, count_take_natPred] at hs
    exact_mod_cast hs
  · have hz : (w.take k).count (i + 1) = 0 := by
      apply List.count_eq_zero.mpr
      intro hm
      have hc := hb (i + 1) (List.mem_of_mem_take hm)
      simp only [PNat.add_coe, PNat.one_coe] at hc
      omega
    rw [hz]
    exact Nat.zero_le _

/-- Positive lattice words are precisely the words lattice from zero in every alphabet. -/
theorem isLatticeWord_iff_all_latticeFrom (w : List ℕ+) :
    IsLatticeWord w ↔
      ∀ d, IsLatticeFrom (0 : IntWeight d) (w.map PNat.natPred) := by
  refine ⟨fun h d => isLatticeFrom_zero_of_latticeWord h d, ?_⟩
  intro h k hk i
  have hs := h (i.val + 1) k (by simpa only [List.length_map] using hk)
    (show (⟨i.natPred, by have := PNat.natPred_add_one i; omega⟩ : Fin (i.val + 1)) ≤
      ⟨i.natPred + 1, by rw [PNat.natPred_add_one]; omega⟩ from Fin.mk_le_mk.mpr (Nat.le_succ _))
  have he : (i + 1).natPred = i.natPred + 1 := by
    have hp := i.pos
    simp only [PNat.natPred, PNat.add_coe, PNat.one_coe]
    omega
  simp only [Pi.add_apply, Pi.zero_apply, zero_add] at hs
  rw [← he, count_take_natPred, count_take_natPred] at hs
  exact_mod_cast hs

end YoungDiagram

namespace SymmetricFunction.FiniteAlphabet.LittlewoodRichardson

private theorem mem_rowsWord_lt {d : ℕ} {ν : YoungDiagram}
    (T : TauCeti.BoundedSSYT d ν) (r : ℕ) {x : ℕ} (hx : x ∈ rowsWord T.val r) : x < d := by
  induction r with
  | zero => simp [rowsWord] at hx
  | succ r ih =>
    rcases List.mem_append.mp hx with hx | hx
    · exact ih hx
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      have hc : c < ν.rowLen r := List.mem_range.mp (List.mem_reverse.mp hc)
      exact T.property r c (YoungDiagram.mem_iff_lt_rowLen.mpr hc)

/-- The bounded straight-tableau lattice rule is the positive reading-word condition. -/
theorem isLattice_iff_positive_word {d : ℕ} {ν : YoungDiagram}
    (T : TauCeti.BoundedSSYT d ν) :
    IsLattice (0 : IntWeight d) T.val ↔
      YoungDiagram.IsLatticeWord ((reverseRowWord T.val).map Nat.succPNat) := by
  have hb : ∀ x ∈ (reverseRowWord T.val).map Nat.succPNat, x.val ≤ d := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have hy := mem_rowsWord_lt T _ hy
    exact Nat.succ_le_of_lt hy
  rw [YoungDiagram.isLatticeWord_iff_latticeFrom _ d hb]
  simp only [List.map_map, Function.comp_def, Nat.natPred_succPNat, List.map_id_fun']
  exact (isLatticeFrom_iff _ _).symm

end SymmetricFunction.FiniteAlphabet.LittlewoodRichardson
