import Schubert.SymmetricFunctions.Restriction

/-! # Transfer from finite alphabets

Restriction to `n` variables is injective on symmetric functions of degree at most `n`.
The restrictions to all finite alphabets jointly determine a symmetric function.

## Main results

* `SymmetricFunction.restrict_inj_of_degreeBound` gives bounded restriction injectivity.
* `SymmetricFunction.ext_restrict` identifies functions from all finite restrictions.
-/

noncomputable section

namespace SymmetricFunction

variable {R : Type*} [CommSemiring R]

/-- A permutation of exponents preserves the coefficient of a symmetric function. -/
theorem coeff_mapDomain_perm (f : SymmetricFunction R) (e : Equiv.Perm ℕ) (d : ℕ →₀ ℕ) :
    coeff R (d.mapDomain e) f = coeff R d f := by
  have h := MvPowerSeries.coeff_embDomain_rename e.toEmbedding f.val d
  change MvPowerSeries.coeff (Finsupp.embDomain e.toEmbedding d)
    (MvPowerSeries.renameEquiv R e (toPowerSeries R f)) =
      MvPowerSeries.coeff d (toPowerSeries R f) at h
  rw [f.isSymmetricSeries e, Finsupp.embDomain_eq_mapDomain] at h
  exact h

private theorem exists_perm_embDomain {n : ℕ} (d : ℕ →₀ ℕ) (hd : d.degree ≤ n) :
    ∃ e : Equiv.Perm ℕ, ∃ k : Fin n →₀ ℕ,
      d.mapDomain e = Finsupp.embDomain (variableEmbedding n) k := by
  classical
  have hcard : d.support.card ≤ d.degree := by
    calc
      d.support.card = ∑ i ∈ d.support, (1 : ℕ) := by simp
      _ ≤ ∑ i ∈ d.support, d i := by
        apply Finset.sum_le_sum
        intro i hi
        have hpos := Finsupp.mem_support_iff.mp hi
        omega
      _ = d.degree := rfl
  have hfinite : Fintype.card d.support ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using hcard.trans hd
  obtain ⟨j⟩ := Function.Embedding.nonempty_of_card_le hfinite
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair
    (fun i : d.support => (i : ℕ)) (fun i : d.support => (j i).val)
    Subtype.val_injective (Fin.val_injective.comp j.injective)
  have hs : ↑(d.mapDomain e).support ⊆ Set.range (variableEmbedding n) := by
    intro i hi
    change i ∈ (d.mapDomain e.toEmbedding).support at hi
    rw [Finsupp.support_mapDomain_embedding] at hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hi
    exact ⟨j ⟨a, ha⟩, (he ⟨a, ha⟩).symm⟩
  refine ⟨e, (d.mapDomain e).comapDomain (variableEmbedding n)
    (variableEmbedding n).injective.injOn, ?_⟩
  exact (Finsupp.embDomain_comapDomain hs).symm

/-- Equality after restriction implies equality when both degree bounds fit the alphabet. -/
theorem restrict_inj_of_degreeBound {n : ℕ} {f g : SymmetricFunction R}
    (hf : f ∈ degreeFiltration R n) (hg : g ∈ degreeFiltration R n)
    (hfg : restrict R n f = restrict R n g) : f = g := by
  apply ext
  intro d
  by_cases hd : n < d.degree
  · rw [(mem_degreeFiltration_iff n f).mp hf d hd,
      (mem_degreeFiltration_iff n g).mp hg d hd]
  · obtain ⟨e, k, he⟩ := exists_perm_embDomain d (Nat.le_of_not_gt hd)
    rw [← coeff_mapDomain_perm f e d, ← coeff_mapDomain_perm g e d, he,
      ← coeff_restrict n k f, ← coeff_restrict n k g, hfg]

/-- Restriction is injective on the submodule of degree at most the alphabet size. -/
theorem restrict_injective_on_bound (n : ℕ) :
    Function.Injective (fun f : degreeFiltration R n => restrict R n f.val) := by
  intro f g hfg
  exact Subtype.ext (restrict_inj_of_degreeBound f.property g.property hfg)

/-- A symmetric function is determined by its restrictions to all finite alphabets. -/
theorem ext_restrict {f g : SymmetricFunction R}
    (h : ∀ n, restrict R n f = restrict R n g) : f = g := by
  obtain ⟨d, hd⟩ := exists_mem_degreeFiltration f
  obtain ⟨k, hk⟩ := exists_mem_degreeFiltration g
  exact restrict_inj_of_degreeBound (hd.mono (le_max_left d k))
    (hk.mono (le_max_right d k)) (h (max d k))

end SymmetricFunction
