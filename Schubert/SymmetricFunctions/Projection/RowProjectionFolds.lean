import Schubert.SymmetricFunctions.Projection.FirstRowProducts
import Mathlib.Data.List.OfFn

/-! # Successive first-row projections of products

Successive projections at the input row sums delete the corresponding initial rows.
Projection at a larger row after a matching prefix annihilates the product.

## Main results

* `firstRowProjection_fold_product` computes a fold at the input row sums.
* `firstRowProjection_fold_eq_zero` annihilates a product at its first larger row.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommRing R]

/-- A fold of projections at successive row sums deletes those initial rows. -/
theorem firstRowProjection_fold_product (k : ℕ) (rows : Fin k → ℤ)
    (α β : YoungDiagram)
    (hrows : ∀ i, rows i = ((α.rowLen i.val + β.rowLen i.val : ℕ) : ℤ)) :
    (List.ofFn rows).foldl (fun f n => firstRowProjection R n f)
      (schur R α * schur R β) = schur R (α.dropRows k) * schur R (β.dropRows k) := by
  induction k with
  | zero => simp only [List.ofFn_zero, List.foldl_nil, YoungDiagram.dropRows_zero]
  | succ k ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    rw [ih (fun i => rows i.castSucc) (fun i => hrows i.castSucc)]
    have hlast := hrows (Fin.last k)
    simp only [Fin.val_last] at hlast
    rw [hlast]
    have hs : ((α.rowLen k + β.rowLen k : ℕ) : ℤ) =
        (((α.dropRows k).rowLen 0 + (β.dropRows k).rowLen 0 : ℕ) : ℤ) := by
      simp only [YoungDiagram.rowLen_dropRows, Nat.add_zero]
    rw [hs, firstRowProjection_product_sum]
    simp only [YoungDiagram.dropRows_dropRows]

/-- A larger selected row after a matching prefix annihilates a Schur product. -/
theorem firstRowProjection_fold_eq_zero (k : ℕ) (rows : Fin k → ℤ)
    (α β : YoungDiagram) (t : Fin k)
    (hbefore : ∀ i, i < t → rows i = ((α.rowLen i.val + β.rowLen i.val : ℕ) : ℤ))
    (hlarge : ((α.rowLen t.val + β.rowLen t.val : ℕ) : ℤ) < rows t) :
    (List.ofFn rows).foldl (fun f n => firstRowProjection R n f)
      (schur R α * schur R β) = 0 := by
  induction k with
  | zero => exact Fin.elim0 t
  | succ k ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    by_cases ht : t.val < k
    · let t' : Fin k := ⟨t.val, ht⟩
      have he : t'.castSucc = t := Fin.ext rfl
      have hp := ih (fun i => rows i.castSucc) t'
        (fun i hi => hbefore i.castSucc (by exact hi))
        (by simpa only [he, Fin.val_castSucc] using hlarge)
      rw [hp, map_zero]
    · have he : t = Fin.last k := by
        apply Fin.ext
        simp only [Fin.val_last]
        have := t.isLt
        omega
      rw [firstRowProjection_fold_product k (fun i => rows i.castSucc) α β
        (fun i => hbefore i.castSucc (by rw [he]; exact i.isLt))]
      apply firstRowProjection_product_above
      simpa only [he, Fin.val_last, YoungDiagram.rowLen_dropRows, Nat.add_zero] using hlarge

end SymmetricFunction
