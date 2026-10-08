import Schubert.ComplementaryProducts.Products
import Schubert.SymmetricFunctions.Presentations.MonomialPowerSumCoefficients
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Algebra.Rat

/-! # Independence of complementary monomial products

The largest supported power-sum generator isolates every complementary pair with a
non-row member. Its square isolates the remaining row self-pair.

## Main results

* `monomial_linearIndependent` proves independence over characteristic-zero fields.
* `monomial_linearIndependent_int` proves independence over the integers.
-/

noncomputable section

open scoped Classical

namespace ComplementaryProducts

open SymmetricFunction

/-- A row-external coefficient isolates one pair when pairs share no member diagram. -/
private theorem isolate_monomial_pair_coeff {R I : Type*} [CommRing R] [Algebra ℚ R]
    [Fintype I] (n : ℕ+) (α β : I → YoungDiagram) (c a b : I → R)
    (f g : I → SymmetricFunction R)
    (hsum : (∑ i, c i • (monomial R (α i) * monomial R (β i))) = 0)
    (hα : ∀ i, monomial R (α i) = a i • powerSum R n + f i)
    (hβ : ∀ i, monomial R (β i) = b i • powerSum R n + g i)
    (hf : ∀ i, ((powerSumPresentation R).symm (f i)).degreeOf n = 0)
    (hg : ∀ i, ((powerSumPresentation R).symm (g i)).degreeOf n = 0)
    (huniq : ∀ i j μ, μ ∈ s(α i, β i) → μ ∈ s(α j, β j) → i = j)
    (i : I) (μ : YoungDiagram)
    (hμ : μ ≠ TauCeti.diagramOf (Nat.Partition.indiscrete n.val))
    (hm : μ ∈ s(α i, β i)) :
    c i * (a i * (if μ = β i then 1 else 0) + b i * (if μ = α i then 1 else 0)) = 0 := by
  classical
  have hh := congrArg (fun f => coeff R (rowExponent μ) (powerSumCoeff R n 1 f)) hsum
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hh
  have hterm (j : I) :
      coeff R (rowExponent μ) (powerSumCoeff R n 1 (monomial R (α j) * monomial R (β j))) =
      a j * (if μ = β j then 1 else 0) + b j * (if μ = α j then 1 else 0) :=
    coeff_linear_monomial_product n _ _ μ _ _ _ _ (hα j) (hβ j) (hf j) (hg j) hμ
  simp only [hterm] at hh
  rw [Finset.sum_eq_single i] at hh
  · exact hh
  · intro j _ hji
    have hma : μ ≠ α j := fun he => hji (huniq j i μ
      (he.symm ▸ Sym2.mem_mk_left _ _) hm)
    have hmb : μ ≠ β j := fun he => hji (huniq j i μ
      (he.symm ▸ Sym2.mem_mk_right _ _) hm)
    simp only [ite_eq_right hma, ite_eq_right hmb, mul_zero, zero_add]
  · intro hn
    exact (hn (Finset.mem_univ i)).elim

/-- Nonzero top coefficients force both members of an isolated pair to be the distinguished row. -/
private theorem pair_eq_row_pair_of_cross_coeff {F : Type*} [Field F] [CharZero F]
    (α β ρ : YoungDiagram) (c a b : F) (hc : c ≠ 0) (ha : a ≠ 0)
    (hb : β = ρ → b ≠ 0)
    (heq : β = α → b = a)
    (hiso : ∀ μ, μ ≠ ρ → μ ∈ s(α, β) →
      c * (a * (if μ = β then 1 else 0) + b * (if μ = α then 1 else 0)) = 0) :
    α = ρ ∧ β = ρ := by
  classical
  by_contra hnot
  by_cases hbr : β = ρ
  · have har : α ≠ ρ := fun he => hnot ⟨he, hbr⟩
    have hz := hiso α har (Sym2.mem_mk_left _ _)
    have hne : α ≠ β := by rw [hbr]; exact har
    simp only [ite_eq_right hne, ite_true, mul_zero, mul_one, zero_add] at hz
    exact (mul_ne_zero hc (hb hbr)) hz
  · have hz := hiso β hbr (Sym2.mem_mk_right _ _)
    by_cases hab : β = α
    · rw [heq hab] at hz
      simp only [ite_true, mul_one, hab] at hz
      have htwo : (2 : F) ≠ 0 := by norm_num
      apply mul_ne_zero hc (mul_ne_zero htwo ha)
      linear_combination hz
    · simp only [ite_true, ite_eq_right hab, mul_one, mul_zero, add_zero] at hz
      exact (mul_ne_zero hc ha) hz

/-- The maximal row pair leaves a single coefficient, detected by the squared generator. -/
private theorem no_relation_with_maximal_row_pair {F I : Type*} [Field F] [CharZero F]
    [Fintype I] (n : ℕ+) (m : ℕ) (α β : I → YoungDiagram) (c : I → F) (i₀ : I)
    (hsum : (∑ i, c i • (monomial F (α i) * monomial F (β i))) = 0)
    (hnonzero : ∀ i, c i ≠ 0)
    (htotal : ∀ i, (α i).card + (β i).card = m)
    (hA : ∀ i, (α i).card ≤ n.val) (hB : ∀ i, (β i).card ≤ n.val)
    (huniq : ∀ i j μ, μ ∈ s(α i, β i) → μ ∈ s(α j, β j) → i = j)
    (htop₀ : (α i₀).card = n.val)
    (hkill : ∀ i, (α i).card = n.val →
      ¬(α i = TauCeti.diagramOf (Nat.Partition.indiscrete n.val) ∧
        β i = TauCeti.diagramOf (Nat.Partition.indiscrete n.val)) → False) : False := by
  classical
  let ρ := TauCeti.diagramOf (Nat.Partition.indiscrete n.val)
  have hρ : ρ.card = n.val := TauCeti.card_diagramOf _
  have hself : α i₀ = ρ ∧ β i₀ = ρ := by
    by_contra hn
    exact hkill i₀ htop₀ hn
  have htwo : m = n.val + n.val := by
    have ht := htotal i₀
    rw [hself.1, hself.2, hρ] at ht
    exact ht.symm
  have hall (i : I) : i = i₀ := by
    have ht := htotal i
    have ha := hA i
    have hb := hB i
    rw [htwo] at ht
    have htop : (α i).card = n.val := by omega
    have hs : α i = ρ ∧ β i = ρ := by
      by_contra hn
      exact hkill i htop hn
    apply huniq i i₀ ρ
    · rw [← hs.1]
      exact Sym2.mem_mk_left _ _
    · rw [← hself.1]
      exact Sym2.mem_mk_left _ _
  rw [Finset.sum_eq_single i₀] at hsum
  · rw [hself.1, hself.2] at hsum
    dsimp only [ρ] at hsum
    rw [YoungDiagram.diagramOf_indiscrete_eq_singleRow, ← powerSum, ← pow_two] at hsum
    have hz := congrArg (powerSumCoeff F n 2) hsum
    simp only [map_smul, powerSumCoeff_generator_pow, ite_true, map_zero] at hz
    have hh := congrArg (coeff F 0) hz
    have hh0 : c i₀ = 0 := by
      simpa only [map_smul, coeff_one, ite_true, smul_eq_mul, mul_one, map_zero] using hh
    exact hnonzero i₀ hh0
  · intro j _ hj
    exact (hj (hall j)).elim
  · intro hn
    exact (hn (Finset.mem_univ i₀)).elim

/-- Complementary monomial products are independent over a characteristic-zero field. -/
theorem monomial_linearIndependent (F : Type*) [Field F] [CharZero F]
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    LinearIndependent F (fun p : complementaryPairs a b =>
      monomialPairProduct F (p : Sym2 YoungDiagram)) := by
  classical
  let : Algebra ℚ F := DivisionRing.toRatAlgebra
  let P := ↥(complementaryPairs a b)
  have hex (p : P) : ∃ α β : YoungDiagram,
      p.val = s(α, β) ∧ β.card ≤ α.card := by
    obtain ⟨μ, hμ, hp⟩ := (mem_complementaryPairs a b p.val).mp p.property
    by_cases h : (YoungDiagram.rectComplement a b μ).card ≤ μ.card
    · exact ⟨μ, YoungDiagram.rectComplement a b μ, hp, h⟩
    · exact ⟨YoungDiagram.rectComplement a b μ, μ,
        hp.trans Sym2.eq_swap, Nat.le_of_lt (Nat.lt_of_not_ge h)⟩
  choose α β hpair horder using hex
  have htotal (p : P) : (α p).card + (β p).card = a * b :=
    card_add_of_complementaryPair (hpair p ▸ p.property)
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  by_contra h
  push Not at h
  obtain ⟨p, hp⟩ := h
  let S := Finset.univ.filter (fun p : P => c p ≠ 0)
  have hS : S.Nonempty := ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
  obtain ⟨p₀, hp₀, hmax⟩ := S.exists_max_image (fun p => (α p).card) hS
  let I := ↥S
  let i₀ : I := ⟨p₀, hp₀⟩
  let e := (α p₀).card
  have he : 0 < e := by
    have ht := htotal p₀
    have ho := horder p₀
    have hab := Nat.mul_pos ha hb
    dsimp only [e]
    omega
  let n : ℕ+ := ⟨e, he⟩
  let ρ := TauCeti.diagramOf (Nat.Partition.indiscrete n.val)
  have hρ : ρ.card = e := TauCeti.card_diagramOf _
  have hA (i : I) : (α i.val).card ≤ e := hmax i.val i.property
  have hB (i : I) : (β i.val).card ≤ e := (horder i.val).trans (hA i)
  let D := {μ : YoungDiagram // μ.card ≤ e}
  have hdata (μ : D) := monomial_linear_powerSum (F := F) n μ.val μ.property
  choose u v hu hv hi using hdata
  let A (i : I) : D := ⟨α i.val, hA i⟩
  let B (i : I) : D := ⟨β i.val, hB i⟩
  have hnonzero (i : I) : c i.val ≠ 0 := (Finset.mem_filter.mp i.property).2
  have hsum : (∑ i : I, c i.val • (monomial F (α i.val) * monomial F (β i.val))) = 0 := by
    change (∑ i : S, c i.val • (monomial F (α i.val) * monomial F (β i.val))) = 0
    rw [Finset.sum_coe_sort S
      (fun p : P => c p • (monomial F (α p) * monomial F (β p)))]
    have hs : (∑ p ∈ S, c p • monomialPairProduct F p.val) =
        ∑ p : P, c p • monomialPairProduct F p.val := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro p _ hp
      have hz : c p = 0 := by
        by_contra hn
        exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
      rw [hz, zero_smul]
    rw [← hc, ← hs]
    apply Finset.sum_congr rfl
    intro p _
    rw [hpair p, monomialPairProduct_mk]
  have huniq (i j : I) (μ : YoungDiagram)
      (hμi : μ ∈ i.val.val) (hμj : μ ∈ j.val.val) : i = j := by
    apply Subtype.ext
    apply Subtype.ext
    exact (complementaryPair_recovery i.val.property hμi).trans
      (complementaryPair_recovery j.val.property hμj).symm
  have hisolate (i : I) (μ : YoungDiagram) (hμ : μ ≠ ρ) (hm : μ ∈ i.val.val) :
      c i.val * (u (A i) * (if μ = β i.val then 1 else 0) +
        u (B i) * (if μ = α i.val then 1 else 0)) = 0 := by
    apply isolate_monomial_pair_coeff n (fun i : I => α i.val) (fun i => β i.val)
      (fun i => c i.val) (fun i => u (A i)) (fun i => u (B i))
      (fun i => v (A i)) (fun i => v (B i)) hsum
      (fun i => hv (A i)) (fun i => hv (B i)) (fun i => hi (A i)) (fun i => hi (B i))
      (fun j k μ hj hk => huniq j k μ
        ((hpair j.val).symm ▸ hj) ((hpair k.val).symm ▸ hk)) i μ hμ
    exact hpair i.val ▸ hm
  have hkill (i : I) (htop : (α i.val).card = e)
      (hnot : ¬(α i.val = ρ ∧ β i.val = ρ)) : False := by
    apply hnot
    apply pair_eq_row_pair_of_cross_coeff _ _ ρ _ _ _ (hnonzero i) ((hu (A i)).mpr htop)
    · intro hbr
      apply (hu (B i)).mpr
      change (β i.val).card = e
      rw [hbr, hρ]
    · intro hab
      exact congrArg u (show B i = A i from Subtype.ext hab)
    · intro μ hμ hm
      exact hisolate i μ hμ ((hpair i.val).symm ▸ hm)
  exact no_relation_with_maximal_row_pair n (a * b)
    (fun i : I => α i.val) (fun i => β i.val) (fun i => c i.val) i₀ hsum hnonzero
    (fun i => htotal i.val) hA hB
    (fun i j μ hi hj => huniq i j μ
      ((hpair i.val).symm ▸ hi) ((hpair j.val).symm ▸ hj)) rfl hkill

/-- Complementary monomial products are independent over the integers. -/
theorem monomial_linearIndependent_int (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    LinearIndependent ℤ (fun p : complementaryPairs a b =>
      monomialPairProduct ℤ (p : Sym2 YoungDiagram)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc p
  have hh := congrArg (SymmetricFunction.map (Int.castRingHom ℚ)) hc
  simp only [map_sum, map_zsmul, map_monomialPairProduct, map_zero] at hh
  have hq : (∑ p : complementaryPairs a b,
      (c p : ℚ) • monomialPairProduct ℚ p.val) = 0 := by
    simpa only [Int.cast_smul_eq_zsmul] using hh
  have hz := Fintype.linearIndependent_iff.mp (monomial_linearIndependent ℚ a b ha hb)
    (fun p => (c p : ℚ)) hq p
  exact Int.cast_eq_zero.mp hz

end ComplementaryProducts
