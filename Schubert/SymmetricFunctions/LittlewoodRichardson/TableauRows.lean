import Schubert.SymmetricFunctions.LittlewoodRichardson.TableauRowMaps

/-! # Saturated first-row removal for lattice tableaux

At a saturated first row, every zero occurs in that row. Deleting the row and decrementing
the letters identifies the lattice tableaux in successive alphabet sizes.

## Main results

* `saturated_tableau_count` preserves the number of tableaux after first-row removal.

## References

* Richard P. Stanley, *Enumerative Combinatorics*, vol. 2, Section 7.10.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, Section 9.
-/

noncomputable section

namespace SymmetricFunction.FiniteAlphabet.LittlewoodRichardson

open SemistandardYoungTableau

variable {N : ℕ} {α β ν : YoungDiagram}

private theorem lattice_prependRow_iff (U : TauCeti.BoundedSSYT N (β.dropRows 1))
    (hb : 0 < N → (α.rowLen 1 : ℤ) + content U.1 0 ≤ α.rowLen 0 + β.rowLen 0) :
    IsLattice (fun i : Fin (N + 1) => (α.rowLen i.val : ℤ)) (prependRow U).1 ↔
      IsLattice (fun i : Fin N => ((α.dropRows 1).rowLen i.val : ℤ)) U.1 := by
  constructor
  · intro h r i hi
    have hl := h (r + 1) (i + 1) (by omega)
    rw [weightAt_of_lt _ (by omega), weightAt_of_lt _ (by omega),
      countBelow_prependRow_succ, countBelow_prependRow_succ] at hl
    rw [weightAt_of_lt _ hi, weightAt_of_lt _ (by omega)]
    simpa only [YoungDiagram.rowLen_dropRows, Nat.add_comm 1] using hl
  · intro h r i hi
    rw [weightAt_of_lt _ hi, weightAt_of_lt _ (by omega)]
    cases r with
    | zero =>
      rw [countBelow_prependRow_succ, countBelow_zero, countBelow_zero]
      have ha := α.rowLen_anti i (i + 1) (Nat.le_succ i)
      exact_mod_cast ha
    | succ r =>
      cases i with
      | zero =>
        rw [countBelow_prependRow_succ, countBelow_prependRow_zero]
        have hc := countBelow_le_content U.1 (r + 1) 0
        have he := hb (by omega)
        simp only [Nat.zero_add]
        omega
      | succ i =>
        rw [countBelow_prependRow_succ, countBelow_prependRow_succ]
        have hl := h r i (by omega)
        rw [weightAt_of_lt _ (by omega), weightAt_of_lt _ (by omega)] at hl
        simpa only [YoungDiagram.rowLen_dropRows, Nat.add_comm 1] using hl

private theorem prependRow_conditions (hs : ν.rowLen 0 = α.rowLen 0 + β.rowLen 0)
    (U : TauCeti.BoundedSSYT N (β.dropRows 1)) :
    (IsLattice (fun i : Fin (N + 1) => (α.rowLen i.val : ℤ)) (prependRow U).1 ∧
      (fun i : Fin (N + 1) => (α.rowLen i.val : ℤ)) + weightVec (prependRow U) =
        (fun i : Fin (N + 1) => (ν.rowLen i.val : ℤ))) ↔
    (IsLattice (fun i : Fin N => ((α.dropRows 1).rowLen i.val : ℤ)) U.1 ∧
      (fun i : Fin N => ((α.dropRows 1).rowLen i.val : ℤ)) + weightVec U =
        (fun i : Fin N => ((ν.dropRows 1).rowLen i.val : ℤ))) := by
  have hweight :
      ((fun i : Fin (N + 1) => (α.rowLen i.val : ℤ)) + weightVec (prependRow U) =
        (fun i : Fin (N + 1) => (ν.rowLen i.val : ℤ))) ↔
      ((fun i : Fin N => ((α.dropRows 1).rowLen i.val : ℤ)) + weightVec U =
        (fun i : Fin N => ((ν.dropRows 1).rowLen i.val : ℤ))) := by
    constructor
    · intro h
      funext i
      have he := congrFun h i.succ
      simpa only [Pi.add_apply, weightVec, Fin.val_succ, content_prependRow_succ,
        YoungDiagram.rowLen_dropRows, Nat.add_comm 1] using he
    · intro h
      funext i
      obtain ⟨i, hi⟩ := i
      cases i with
      | zero =>
        simp only [Pi.add_apply, weightVec, content_prependRow_zero]
        exact_mod_cast hs.symm
      | succ i =>
        have he := congrFun h ⟨i, by omega⟩
        simpa only [Pi.add_apply, weightVec, content_prependRow_succ,
          YoungDiagram.rowLen_dropRows, Nat.add_comm 1] using he
  constructor
  · rintro ⟨hl, hw⟩
    have ht := hweight.mp hw
    refine ⟨(lattice_prependRow_iff U ?_).mp hl, ht⟩
    intro hN
    have he := congrFun ht ⟨0, hN⟩
    have ha := ν.rowLen_anti 0 1 (by omega)
    simp only [Pi.add_apply, weightVec, YoungDiagram.rowLen_dropRows] at he
    rw [hs] at ha
    exact he ▸ (by exact_mod_cast ha)
  · rintro ⟨hl, hw⟩
    refine ⟨(lattice_prependRow_iff U ?_).mpr hl, hweight.mpr hw⟩
    intro hN
    have he := congrFun hw ⟨0, hN⟩
    have ha := ν.rowLen_anti 0 1 (by omega)
    simp only [Pi.add_apply, weightVec, YoungDiagram.rowLen_dropRows] at he
    rw [hs] at ha
    exact he ▸ (by exact_mod_cast ha)

/-- Saturated lattice tableaux are equinumerous after deleting the first row and letter. -/
theorem saturated_tableau_count (N : ℕ) (α β ν : YoungDiagram)
    (hs : ν.rowLen 0 = α.rowLen 0 + β.rowLen 0) :
    Fintype.card {T : TauCeti.BoundedSSYT (N + 1) β //
      IsLattice (fun i : Fin (N + 1) => (α.rowLen i.val : ℤ)) T.1 ∧
      (fun i : Fin (N + 1) => (α.rowLen i.val : ℤ)) + weightVec T =
        (fun i : Fin (N + 1) => (ν.rowLen i.val : ℤ))} =
    Fintype.card {U : TauCeti.BoundedSSYT N (β.dropRows 1) //
      IsLattice (fun i : Fin N => ((α.dropRows 1).rowLen i.val : ℤ)) U.1 ∧
      (fun i : Fin N => ((α.dropRows 1).rowLen i.val : ℤ)) + weightVec U =
        (fun i : Fin N => ((ν.dropRows 1).rowLen i.val : ℤ))} := by
  classical
  let P (T : TauCeti.BoundedSSYT (N + 1) β) : Prop :=
    IsLattice (fun i : Fin (N + 1) => (α.rowLen i.val : ℤ)) T.1 ∧
      (fun i : Fin (N + 1) => (α.rowLen i.val : ℤ)) + weightVec T =
        (fun i : Fin (N + 1) => (ν.rowLen i.val : ℤ))
  let Q (U : TauCeti.BoundedSSYT N (β.dropRows 1)) : Prop :=
    IsLattice (fun i : Fin N => ((α.dropRows 1).rowLen i.val : ℤ)) U.1 ∧
      (fun i : Fin N => ((α.dropRows 1).rowLen i.val : ℤ)) + weightVec U =
        (fun i : Fin N => ((ν.dropRows 1).rowLen i.val : ℤ))
  have hz (T : TauCeti.BoundedSSYT (N + 1) β) (hT : P T) : ∀ j, T.1 0 j = 0 := by
    apply firstRow_zero_of_content
    have he := congrFun hT.2 (0 : Fin (N + 1))
    simp only [Pi.add_apply, weightVec, Fin.val_zero] at he
    rw [hs, Nat.cast_add] at he
    exact_mod_cast (add_left_cancel he)
  have he : {T // P T} ≃ {U // Q U} :=
    { toFun := fun T => ⟨SemistandardYoungTableau.deleteRow T.1, by
        apply (prependRow_conditions hs (SemistandardYoungTableau.deleteRow T.1)).mp
        rw [SemistandardYoungTableau.prependRow_deleteRow T.1 (hz T.1 T.2)]
        exact T.2⟩
      invFun := fun U => ⟨prependRow U.1, (prependRow_conditions hs U.1).mpr U.2⟩
      left_inv := fun T => Subtype.ext (prependRow_deleteRow T.1 (hz T.1 T.2))
      right_inv := fun U => Subtype.ext (SemistandardYoungTableau.deleteRow_prependRow U.1) }
  exact Fintype.card_congr he

end SymmetricFunction.FiniteAlphabet.LittlewoodRichardson
