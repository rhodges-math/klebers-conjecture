import KlebersConjecture.SymmetricFunctions.Families.Families
import KlebersConjecture.SymmetricFunctions.ForMathlib.WeightedEvaluation
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous

/-!
# Existence of the elementary symmetric-function presentation

Finite elementary presentations and weighted degree projections give the stable presentation.

## Main results

* `exists_elementaryPresentation`: elementary functions freely generate the stable algebra.
-/

noncomputable section

namespace SymmetricFunction

variable (R : Type*) [CommRing R]

/-- Evaluation at the first finitely many positive elementary functions. -/
private def finiteElementaryEval (N : ℕ) :
    MvPolynomial (Fin N) R →ₐ[R] SymmetricFunction R :=
  MvPolynomial.aeval (fun i : Fin N => elementary R (i.val + 1))

private theorem restrict_finiteElementaryEval (n N : ℕ) (p : MvPolynomial (Fin N) R) :
    restrict R n (finiteElementaryEval R N p) =
      MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin n) R (i.val + 1)) p := by
  have h : (restrict R n).comp (finiteElementaryEval R N) =
      MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin n) R (i.val + 1)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [finiteElementaryEval, AlgHom.comp_apply, MvPolynomial.aeval_X,
      restrict_elementary]
  exact AlgHom.congr_fun h p

private theorem finiteElementaryEval_injective (N : ℕ) :
    Function.Injective (finiteElementaryEval R N) := by
  intro p q h
  apply MvPolynomial.esymmAlgHom_fin_injective R (le_refl N)
  apply Subtype.ext
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.esymmAlgHom_apply,
    ← restrict_finiteElementaryEval, ← restrict_finiteElementaryEval, h]

private theorem restrict_component (n j : ℕ) (f : SymmetricFunction R) :
    restrict R n (homogeneousComponent R j f) =
      MvPolynomial.homogeneousComponent j (restrict R n f) := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_restrict, coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent,
    coeff_restrict]
  simp only [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]

private theorem component_finiteElementaryEval (N j : ℕ) (p : MvPolynomial (Fin N) R) :
    homogeneousComponent R j (finiteElementaryEval R N p) =
      finiteElementaryEval R N
        (MvPolynomial.weightedHomogeneousComponent (fun i : Fin N => i.val + 1) j p) := by
  apply ext_restrict
  intro n
  rw [restrict_component, restrict_finiteElementaryEval, restrict_finiteElementaryEval]
  exact MvPolynomial.homogeneousComponent_aeval_weighted (R := R) (S := R)
    (fun i : Fin N => i.val + 1)
    (fun i : Fin N => MvPolynomial.esymm (Fin n) R (i.val + 1))
    (fun i => @MvPolynomial.isHomogeneous_esymm (Fin n) R _ _ (i.val + 1)) p j

/-- The inclusion of the first positive generator indices. -/
private def positiveGenerator (N : ℕ) (i : Fin N) : ℕ+ := ⟨i.val + 1, Nat.succ_pos _⟩

private theorem positiveGenerator_injective (N : ℕ) :
    Function.Injective (positiveGenerator N) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg PNat.val h
  change i.val + 1 = j.val + 1 at hv
  omega

private theorem exists_finiteGenerators (p : MvPolynomial ℕ+ R) :
    ∃ N : ℕ, ∃ q : MvPolynomial (Fin N) R, MvPolynomial.rename (positiveGenerator N) q = p := by
  classical
  let N := p.vars.sup PNat.val
  refine ⟨N, ?_⟩
  apply MvPolynomial.exists_rename_eq_of_vars_subset_range p (positiveGenerator N)
    (positiveGenerator_injective N)
  intro k hk
  have hle : k.val ≤ N := Finset.le_sup (f := PNat.val) hk
  have hpos := k.pos
  refine ⟨⟨k.val - 1, by omega⟩, ?_⟩
  apply Subtype.ext
  change k.val - 1 + 1 = k.val
  omega

private theorem eval_positiveGenerator (N : ℕ) (q : MvPolynomial (Fin N) R) :
    MvPolynomial.aeval (fun k : ℕ+ => elementary R k.val)
        (MvPolynomial.rename (positiveGenerator N) q) = finiteElementaryEval R N q := by
  rw [MvPolynomial.aeval_rename]
  rfl

private theorem elementaryEval_injective :
    Function.Injective (MvPolynomial.aeval (R := R) (fun k : ℕ+ => elementary R k.val)) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨N, q, hq⟩ := exists_finiteGenerators R p
  have hzero : finiteElementaryEval R N q = finiteElementaryEval R N 0 := by
    rw [map_zero, ← eval_positiveGenerator, hq, hp]
  have hqzero := finiteElementaryEval_injective R N hzero
  rw [← hq, hqzero, map_zero]

private theorem elementaryEval_surjective :
    Function.Surjective (MvPolynomial.aeval (R := R) (fun k : ℕ+ => elementary R k.val)) := by
  intro f
  obtain ⟨D, hD⟩ := exists_mem_degreeFiltration f
  obtain ⟨q, hq⟩ := (MvPolynomial.esymmAlgHom_fin_bijective R D).surjective
    ⟨restrict R D f, isSymmetric_restrict D f⟩
  have heval : restrict R D (finiteElementaryEval R D q) = restrict R D f := by
    rw [restrict_finiteElementaryEval, ← MvPolynomial.esymmAlgHom_apply]
    exact congrArg Subtype.val hq
  have hhigh (j : ℕ) (hj : D < j) :
      MvPolynomial.weightedHomogeneousComponent (fun i : Fin D => i.val + 1) j q = 0 := by
    apply finiteElementaryEval_injective R D
    rw [map_zero, ← component_finiteElementaryEval]
    have hc : restrict R D (homogeneousComponent R j (finiteElementaryEval R D q)) = 0 := by
      rw [restrict_component, heval]
      exact MvPolynomial.homogeneousComponent_eq_zero j (restrict R D f)
        ((totalDegree_restrict_le f hD).trans_lt hj)
    have hinj (p q' : MvPolynomial (Fin D) R)
        (h : restrict R D (finiteElementaryEval R D p) =
          restrict R D (finiteElementaryEval R D q')) : p = q' := by
      apply MvPolynomial.esymmAlgHom_fin_injective R (le_refl D)
      apply Subtype.ext
      simpa only [MvPolynomial.esymmAlgHom_apply, restrict_finiteElementaryEval] using h
    have hcomp : MvPolynomial.weightedHomogeneousComponent
        (fun i : Fin D => i.val + 1) j q = 0 := by
      apply hinj
      rw [← component_finiteElementaryEval, hc, map_zero, map_zero]
    rw [component_finiteElementaryEval, hcomp, map_zero]
  have hg : HasDegreeBound (finiteElementaryEval R D q).val D := by
    intro d hd
    have hc : homogeneousComponent R d.degree (finiteElementaryEval R D q) = 0 := by
      rw [component_finiteElementaryEval, hhigh d.degree hd, map_zero]
    have he := congrArg (coeff R d) hc
    change coeff R d (finiteElementaryEval R D q) = 0
    simpa only [coeff_homogeneousComponent, ite_true, coeff_zero] using he
  refine ⟨MvPolynomial.rename (positiveGenerator D) q, ?_⟩
  rw [eval_positiveGenerator]
  exact restrict_inj_of_degreeBound hg hD heval

/-- The positive elementary functions give a polynomial presentation over any commutative ring. -/
theorem exists_elementaryPresentation :
    ∃ e : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R,
      ∀ n : ℕ+, e (MvPolynomial.X n) = elementary R n.val := by
  refine ⟨AlgEquiv.ofBijective (MvPolynomial.aeval (fun k : ℕ+ => elementary R k.val))
    ⟨elementaryEval_injective R, elementaryEval_surjective R⟩, ?_⟩
  intro n
  exact MvPolynomial.aeval_X _ n


/-- The canonical presentation evaluates positive elementary generators. -/
def elementaryPresentation : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R :=
  AlgEquiv.ofBijective (MvPolynomial.aeval (fun k : ℕ+ => elementary R k.val))
    ⟨elementaryEval_injective R, elementaryEval_surjective R⟩

/-- The elementary presentation has the natural evaluation homomorphism. -/
theorem elementaryPresentation_toAlgHom :
    (elementaryPresentation R).toAlgHom =
      MvPolynomial.aeval (fun k : ℕ+ => elementary R k.val) := rfl

/-- Positive elementary generators are the images of polynomial generators. -/
@[simp]
theorem elementaryPresentation_apply_X (n : ℕ+) :
    elementaryPresentation R (MvPolynomial.X n) = elementary R n.val :=
  MvPolynomial.aeval_X _ n

/-- A normalized elementary presentation has the expected inverse on generators. -/
theorem symm_elementary_eq_X (e : MvPolynomial ℕ+ R ≃ₐ[R] SymmetricFunction R)
    (he : ∀ n : ℕ+, e (MvPolynomial.X n) = elementary R n.val) (n : ℕ+) :
    e.symm (elementary R n.val) = MvPolynomial.X n := by
  rw [← he, e.symm_apply_apply]

end SymmetricFunction
