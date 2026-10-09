import KlebersConjecture.SymmetricFunctions.Families.Schur
import KlebersConjecture.SymmetricFunctions.Components
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Elementary
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Complete
import KlebersConjecture.Partitions.Bounds
import KlebersConjecture.Partitions.SingleShapes
import KlebersConjecture.SymmetricFunctions.ForMathlib.CompleteCoefficients

/-!
# Elementary, complete, and power-sum symmetric functions

Column and row Schur functions define the elementary and complete families.
Positive single-row monomials define the power sums.
Elementary indices are natural numbers. Complete indices are integers, with negative indices
interpreted as zero. Power-sum indices are positive natural numbers.

## Main definitions

* `elementary` is indexed by natural numbers.
* `complete` is indexed by integers and vanishes at negative indices.
* `powerSum` is indexed by positive natural numbers.

## Main results

* `restrict_elementary`: restriction gives an elementary symmetric polynomial.
* `restrict_complete_nat`: restriction gives a complete homogeneous polynomial.
* `complete_neg`: complete functions of negative index vanish.

## Implementation notes

Elementary functions use natural indices, including the identity in degree zero. Complete
functions use integer indices so that every Jacobi--Trudi entry is defined; negative indices
are zero. Power sums use positive indices, since the zeroth finite power sum counts the
variables and has no stable scalar value independent of the alphabet.
The casts of natural complete indices are normalized to single-row Schur functions.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, §2.
-/

noncomputable section

namespace SymmetricFunction

/-- The elementary symmetric function of natural degree. -/
def elementary (R : Type*) [CommSemiring R] (k : ℕ) : SymmetricFunction R :=
  schur R (YoungDiagram.singleColumn k)

/-- The complete symmetric function, with negative indices interpreted as zero. -/
def complete (R : Type*) [CommSemiring R] (k : ℤ) : SymmetricFunction R :=
  if 0 ≤ k then schur R (YoungDiagram.singleRow k.toNat) else 0

/-- The power-sum symmetric function of positive degree. -/
def powerSum (R : Type*) [CommSemiring R] (k : ℕ+) : SymmetricFunction R :=
  monomial R (YoungDiagram.singleRow k.val)

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Elementary functions are column Schur functions. -/
theorem elementary_eq_schur_singleColumn (k : ℕ) :
    elementary R k = schur R (YoungDiagram.singleColumn k) := rfl

/-- Positive power sums are single-row monomial functions. -/
theorem powerSum_eq_monomial_singleRow (k : ℕ+) :
    powerSum R k = monomial R (YoungDiagram.singleRow k.val) := rfl

/-- A nonnegative complete function is the corresponding row Schur function. -/
@[simp]
theorem complete_natCast_eq_schur (k : ℕ) :
    complete R (k : ℤ) = schur R (YoungDiagram.singleRow k) := by
  simp only [complete, Int.natCast_nonneg, ite_true, Int.toNat_natCast]

/-- Nonnegative complete functions are the single-row Schur functions. -/
theorem complete_nat (k : ℕ) :
    complete R (k : ℤ) = schur R (TauCeti.diagramOf (Nat.Partition.indiscrete k)) := by
  simp [complete]

/-- Complete functions of negative index vanish. -/
theorem complete_neg (k : ℤ) (hk : k < 0) : complete R k = 0 := by
  simp only [complete, ite_eq_right (not_le.mpr hk)]

/-- Restriction of an elementary function is the elementary symmetric polynomial. -/
theorem restrict_elementary (n k : ℕ) :
    restrict R n (elementary R k) = MvPolynomial.esymm (Fin n) R k := by
  rw [elementary, ← YoungDiagram.diagramOf_ones_eq_singleColumn,
    restrict_schur_diagramOf, TauCeti.schurPoly_ones]

/-- Restriction of a nonnegative complete function is the complete homogeneous polynomial. -/
theorem restrict_complete_nat (n k : ℕ) :
    restrict R n (complete R (k : ℤ)) = MvPolynomial.hsymm (Fin n) R k := by
  rw [complete_nat, restrict_schur_diagramOf, TauCeti.schurPoly_indiscrete]

/-- Restriction includes the zero convention at negative complete indices. -/
theorem restrict_complete (n : ℕ) (k : ℤ) :
    restrict R n (complete R k) =
      if 0 ≤ k then MvPolynomial.hsymm (Fin n) R k.toNat else 0 := by
  by_cases hk : 0 ≤ k
  · rw [ite_eq_left hk]
    have h := restrict_complete_nat (R := R) n k.toNat
    simpa only [Int.toNat_of_nonneg hk] using h
  · rw [complete_neg k (lt_of_not_ge hk), map_zero, ite_eq_right hk]

/-- Elementary functions are homogeneous in their natural degree. -/
theorem isHomogeneous_elementary (k : ℕ) : IsHomogeneous (elementary R k) k := by
  rw [elementary]
  exact (congrArg (IsHomogeneous (schur R (YoungDiagram.singleColumn k)))
    (YoungDiagram.card_singleColumn k)).mp
      (@isHomogeneous_schur R _ (YoungDiagram.singleColumn k))

/-- A nonnegative complete function is homogeneous in its natural degree. -/
theorem isHomogeneous_complete_nat (k : ℕ) : IsHomogeneous (complete R (k : ℤ)) k := by
  rw [complete_natCast_eq_schur]
  exact (congrArg (IsHomogeneous (schur R (YoungDiagram.singleRow k)))
    (YoungDiagram.card_singleRow k)).mp
      (@isHomogeneous_schur R _ (YoungDiagram.singleRow k))

/-- Power sums are homogeneous in their positive degree. -/
theorem isHomogeneous_powerSum (k : ℕ+) : IsHomogeneous (powerSum R k) k.val := by
  rw [powerSum]
  exact (congrArg (IsHomogeneous (monomial R (YoungDiagram.singleRow k.val)))
    (YoungDiagram.card_singleRow k.val)).mp
      (@isHomogeneous_monomial R _ (YoungDiagram.singleRow k.val))

/-- Elementary functions belong to the filtration of their degree. -/
theorem elementary_mem_degreeFiltration (k : ℕ) :
    elementary R k ∈ degreeFiltration R k := by
  exact IsHomogeneous.mem_degreeFiltration (R := R) (f := elementary R k) (d := k)
    (isHomogeneous_elementary (R := R) k)

/-- Nonnegative complete functions belong to the filtration of their degree. -/
theorem complete_nat_mem_degreeFiltration (k : ℕ) :
    complete R (k : ℤ) ∈ degreeFiltration R k := by
  exact IsHomogeneous.mem_degreeFiltration (R := R) (f := complete R (k : ℤ)) (d := k)
    (isHomogeneous_complete_nat (R := R) k)

/-- Power sums belong to the filtration of their degree. -/
theorem powerSum_mem_degreeFiltration (k : ℕ+) :
    powerSum R k ∈ degreeFiltration R k.val := by
  exact IsHomogeneous.mem_degreeFiltration (R := R) (f := powerSum R k) (d := k.val)
    (isHomogeneous_powerSum (R := R) k)

/-- Coefficient-ring homomorphisms preserve elementary functions. -/
theorem map_elementary (φ : R →+* S) (k : ℕ) :
    map φ (elementary R k) = elementary S k := by
  unfold elementary
  exact map_schur φ _

/-- Coefficient-ring homomorphisms preserve complete functions. -/
theorem map_complete (φ : R →+* S) (k : ℤ) : map φ (complete R k) = complete S k := by
  unfold complete
  split_ifs <;> first | exact map_schur φ _ | exact map_zero _

/-- Coefficient-ring homomorphisms preserve positive power sums. -/
theorem map_powerSum (φ : R →+* S) (k : ℕ+) :
    map φ (powerSum R k) = powerSum S k := map_monomial φ _

/-- The elementary function of degree zero is one. -/
theorem elementary_zero : elementary R 0 = 1 := by
  apply ext_restrict
  intro n
  rw [restrict_elementary, map_one, MvPolynomial.esymm_zero]

/-- The complete function of degree zero is one. -/
theorem complete_zero : complete R 0 = 1 := by
  apply ext_restrict
  intro n
  rw [show (0 : ℤ) = (0 : ℕ) from rfl, restrict_complete_nat, map_one,
    MvPolynomial.hsymm_zero]

open scoped Classical in
/-- The power-sum coefficients indicate the single-row exponent diagram. -/
theorem coeff_powerSum (k : ℕ+) (d : ℕ →₀ ℕ) :
    coeff R d (powerSum R k) =
      if exponentDiagram d = TauCeti.diagramOf (Nat.Partition.indiscrete k.val) then 1 else 0 :=
  by
    rw [powerSum, ← YoungDiagram.diagramOf_indiscrete_eq_singleRow]
    exact coeff_monomial _ _

/-- Elementary coefficients vanish outside their degree. -/
theorem coeff_elementary_eq_zero (k : ℕ) (d : ℕ →₀ ℕ) (hd : d.degree ≠ k) :
    coeff R d (elementary R k) = 0 :=
  IsHomogeneous.coeff_eq_zero (isHomogeneous_elementary k) hd

/-- Nonnegative complete coefficients vanish outside their degree. -/
theorem coeff_complete_nat_eq_zero (k : ℕ) (d : ℕ →₀ ℕ) (hd : d.degree ≠ k) :
    coeff R d (complete R (k : ℤ)) = 0 :=
  IsHomogeneous.coeff_eq_zero (isHomogeneous_complete_nat k) hd


/-- Every monomial of the complete function's degree has coefficient one. -/
theorem coeff_complete_nat (k : ℕ) (d : ℕ →₀ ℕ) :
    coeff R d (complete R (k : ℤ)) = if d.degree = k then 1 else 0 := by
  classical
  let μ := exponentDiagram d
  let c := TauCeti.rowLenWeight (μ.colLen 0) μ
  have hc : Finsupp.embDomain (variableEmbedding (μ.colLen 0)) c = rowExponent μ := by
    rw [Finsupp.embDomain_eq_mapDomain]
    rfl
  have hd : c.degree = d.degree := by
    rw [← Finsupp.degree_mapDomain (variableEmbedding (μ.colLen 0)) c]
    change (rowExponent μ).degree = d.degree
    rw [degree_rowExponent, card_exponentDiagram]
  rw [coeff_eq_rowExponent d, ← hc, ← coeff_restrict,
    restrict_complete_nat, MvPolynomial.coeff_hsymm, hd]

/-- Complete coefficients include the negative-index zero convention. -/
theorem coeff_complete (k : ℤ) (d : ℕ →₀ ℕ) :
    coeff R d (complete R k) = if 0 ≤ k ∧ d.degree = k.toNat then 1 else 0 := by
  by_cases hk : 0 ≤ k
  · have h := coeff_complete_nat (R := R) k.toNat d
    simpa only [Int.toNat_of_nonneg hk, hk, true_and] using h
  · rw [complete_neg k (lt_of_not_ge hk), coeff_zero]
    simp only [hk, false_and, ite_false]

private theorem weightPartition_single {n k : ℕ} (i : Fin n) (hk : k ≠ 0) :
    TauCeti.weightPartition (Finsupp.single i k) (Finsupp.degree_single i k) =
      Nat.Partition.indiscrete k := by
  classical
  apply Nat.Partition.ext
  rw [TauCeti.weightPartition_parts, Nat.Partition.indiscrete_parts hk]
  simp [Finsupp.support_single _ hk]

private theorem finitePowerSum_eq_monomial (n : ℕ) (k : ℕ+) :
    MvPolynomial.psum (Fin n) R k.val =
      MvPolynomial.msymm (Fin n) R (Nat.Partition.indiscrete k.val) := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.psum, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
  by_cases hd : d.degree = k.val
  · rw [TauCeti.coeff_msymm R _ hd]
    by_cases hshape : TauCeti.weightPartition d hd = Nat.Partition.indiscrete k.val
    · have hc : d.support.card = 1 := by
        have hc := congrArg (fun ν : k.val.Partition => ν.parts.card) hshape
        simpa only [TauCeti.weightPartition_parts, Multiset.card_map,
          Nat.Partition.indiscrete_parts k.ne_zero, Multiset.card_singleton,
          Finset.card] using hc
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
      have hs : d = Finsupp.single i (d i) := by
        ext j
        by_cases hj : j = i
        · subst j
          simp
        · have hj' : j ∉ d.support := by simp only [hi, Finset.mem_singleton, hj, not_false_eq_true]
          simp only [Finsupp.notMem_support_iff.mp hj', Finsupp.single_eq_of_ne hj]
      have hv : d i = k.val := by
        simpa only [Finsupp.degree_single] using
          (congrArg Finsupp.degree hs).symm.trans hd
      rw [ite_eq_left hshape, Finset.sum_eq_single i]
      · simp only [← hv, ← hs, ite_true]
      · intro j _ hj
        apply ite_eq_right
        intro h
        have hh := congrArg (fun f : Fin n →₀ ℕ => f i) h
        simp only [Finsupp.single_eq_of_ne (Ne.symm hj), hv] at hh
        exact k.ne_zero hh.symm
      · exact fun h => (h (Finset.mem_univ _)).elim
    · rw [ite_eq_right hshape]
      apply Finset.sum_eq_zero
      intro i _
      apply ite_eq_right
      intro h
      apply hshape
      subst d
      exact weightPartition_single i k.ne_zero
  · rw [TauCeti.coeff_msymm_eq_zero_of_degree_ne R _ hd]
    apply Finset.sum_eq_zero
    intro i _
    apply ite_eq_right
    intro h
    apply hd
    rw [← h, Finsupp.degree_single]

/-- Restriction of a positive power sum gives the finite power-sum polynomial. -/
theorem restrict_powerSum (n : ℕ) (k : ℕ+) :
    restrict R n (powerSum R k) = MvPolynomial.psum (Fin n) R k.val := by
  rw [powerSum, ← YoungDiagram.diagramOf_indiscrete_eq_singleRow,
    restrict_monomial_diagramOf, finitePowerSum_eq_monomial]

private theorem column_rowLen (μ : YoungDiagram) (h : μ.rowLen 0 ≤ 1) (i : ℕ) :
    μ.rowLen i = if i < μ.card then 1 else 0 := by
  rw [YoungDiagram.card_eq_colLen_of_rowLen_le_one h]
  by_cases hi : i < μ.colLen 0
  · rw [ite_eq_left hi]
    have hp : 0 < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp
      (YoungDiagram.mem_iff_lt_colLen.mpr hi)
    have hl := (μ.rowLen_anti 0 i (Nat.zero_le i)).trans h
    omega
  · rw [ite_eq_right hi, YoungDiagram.rowLen_eq_zero_of_colLen_le (Nat.le_of_not_gt hi)]

private theorem kostka_column_eq_zero (μ : YoungDiagram) (hμ : μ.rowLen 0 ≤ 1)
    (ν : μ.card.Partition) (hν : ν ≠ TauCeti.shapePartition μ) :
    TauCeti.kostkaNumber (TauCeti.shapePartition μ) ν = 0 := by
  by_contra hk
  have hd := TauCeti.dominates_of_kostkaNumber_ne_zero hk
  have hfirst := TauCeti.dominates_iff.mp hd 1
  have htake (l : List ℕ) : (l.take 1).sum = l.getD 0 0 := by cases l <;> rfl
  rw [htake, htake, ← TauCeti.rowLen_diagramOf, ← TauCeti.rowLen_diagramOf,
    TauCeti.diagramOf_shapePartition] at hfirst
  have hc : (TauCeti.diagramOf ν).rowLen 0 ≤ 1 := hfirst.trans hμ
  apply hν
  apply TauCeti.diagramOf_injective
  rw [TauCeti.diagramOf_shapePartition]
  apply YoungDiagram.rowLen_injective
  funext i
  rw [column_rowLen _ hc, column_rowLen _ hμ, TauCeti.card_diagramOf]

private theorem schur_column_eq_monomial (μ : YoungDiagram) (hμ : μ.rowLen 0 ≤ 1) :
    schur R μ = monomial R μ := by
  classical
  rw [schur, Finset.sum_eq_single (TauCeti.shapePartition μ)]
  · rw [TauCeti.kostkaNumber_self, Nat.cast_one, one_smul, TauCeti.diagramOf_shapePartition]
  · intro ν _ hν
    rw [kostka_column_eq_zero μ hμ ν hν, Nat.cast_zero, zero_smul]
  · exact fun h => (h (Finset.mem_univ _)).elim

/-- An elementary symmetric function is the monomial function of its column diagram. -/
theorem elementary_eq_monomial (k : ℕ) :
    elementary R k = monomial R (TauCeti.diagramOf (TauCeti.Nat.Partition.ones k)) := by
  rw [elementary, ← YoungDiagram.diagramOf_ones_eq_singleColumn]
  exact schur_column_eq_monomial (R := R) _ (TauCeti.rowLen_diagramOf_ones_le_one k 0)

open scoped Classical in
/-- Elementary coefficients indicate the squarefree column exponent diagram. -/
theorem coeff_elementary (k : ℕ) (d : ℕ →₀ ℕ) :
    coeff R d (elementary R k) =
      if exponentDiagram d = TauCeti.diagramOf (TauCeti.Nat.Partition.ones k) then 1 else 0 := by
  rw [elementary_eq_monomial, coeff_monomial]

end SymmetricFunction
