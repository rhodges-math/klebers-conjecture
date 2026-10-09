# Statements of the paper and their Lean counterparts

Each statement of *Kleber's conjecture and complementary products of symmetric functions*
(Reuven Hodges and Hanzhang Yin, 2026), [arXiv:2607.12120](https://arxiv.org/abs/2607.12120),
with its status and the Lean declarations that formalize it, in the order of the paper. The
index covers every theorem, corollary, lemma, definition, example and remark of the paper,
the displayed equations its proofs cite, the definitions made in its prose, and the standard
results it recalls. Numbers are those printed in the paper (arXiv:2607.12120v1), and labels
are its LaTeX labels; a statement without a number is given with its section. A short note
follows a statement whose Lean statement or proof differs from the paper. Paths are
relative to the repository root.

| Statement | Label | Status |
| --- | --- | --- |
| The rectangular complement $\lambda^\vee$ (Section 1) | — | formalized |
| Theorem 1.1 (Kleber's conjecture) | `thm-rectangular` | formalized |
| The $\theta$-splittings $\mathrm{Split}(\theta)$ and the unordered complementary pairs (Section 1) | — | formalized |
| Theorem 1.2 | `thm-core` | formalized |
| The Koike–Terada universal characters $s\_{\[\lambda\]}$ (Section 1) | — | formalized |
| The $s\_{\[\lambda\]}$ form a basis, and the class of $s\_{\[\lambda\]}$ in $F\_{\le \lvert\lambda\rvert}/F\_{\le \lvert\lambda\rvert-1}$ is that of $s\_\lambda$ (Section 1) | — | formalized |
| The degree filtration $F\_{\le d}$ (Section 1) and the Littlewood–Richardson coefficients $c^\nu\_{\lambda,\mu}$ (Section 2.2) | — | formalized |
| Corollary 1.3 | `cor-koike-terada` | formalized |
| Theorem 1.4 | `thm-monomial` | formalized |
| The bases $m\_\lambda$, $h\_\lambda$, $s\_\lambda$ and $p\_\lambda$, the presentations $\Lambda\_R=R\[h\_1,h\_2,\ldots\]$ and $\Lambda\_{\mathbb{F}}=\mathbb{F}\[p\_1,p\_2,\ldots\]$, and $\Lambda\_R=R\otimes\_{\mathbb{Z}}\Lambda\_{\mathbb{Z}}$ (Section 2.1) | — | formalized |
| The monomial, complete, power-sum and Schur functions as defined in Section 2.1 | — | formalized |
| Equation (2.1): the Jacobi–Trudi identity | `eq-jacobi-trudi` | formalized |
| Coefficient extraction $\[h\_a^j\]\_{\mathrm{p}}$ and $\[p\_d^j\]\_{\mathrm{p}}$ (Section 2.1), and the derivations $\partial/\partial h\_n$ (Section 2.3) | — | formalized |
| $\mathrm{Top}(f)$ (Section 2.1) | — | formalized |
| The Littlewood–Richardson rule in skew-tableau form (Section 2.2) | — | formalized |
| Lemma 2.2 | `lem-row-removal` | formalized |
| Corollary 2.3 | `cor-top-product` | formalized |
| Definition 2.4 | — | formalized |
| Lemma 2.5 | `lem-jt-derivative` | formalized |
| Definition 3.1 | `def-first-row-projection` | formalized |
| Lemma 3.2 | `lem-top-row-projection` | formalized |
| Lemma 3.3 | `lem-oriented-block` | formalized |
| Lemma 3.7 | `lem-maximal-self-pair` | formalized |
| $\mathrm{gap}(\lambda)$ is a partition, and $\mathrm{gap}(\lambda^\vee)=\mathrm{gap}(\lambda)$ (Section 4) | — | formalized |
| Gap vectors, the shapes $\Theta\_g$ and the projections $\Pi\_g$ (Section 4) | — | formalized |
| Equation (4.1) | `eq-fixed-gap-tail-sum` | formalized |
| Example 4.2 | — | formalized |
| Lemma 4.3 | `lem-gap-block` | formalized |
| Lemma 4.4 | `lem-fixed-gap-injective` | formalized |
| Example 5.1 | — | formalized |
| The Möbius function of the lattice of set partitions: $\mu(\hat0,\hat1)=(-1)^{k-1}(k-1)!$ (Section 5) | — | formalized |
| Lemma 5.2 | `lem-monomial-top-p` | formalized |
| Remark 5.8 | — | formalized |

## Statements

### The rectangular complement $\lambda^\vee$ (Section 1)

Status: **formalized**

- `YoungDiagram.rectComplement` ([KlebersConjecture/Partitions/Rectangle.lean](../KlebersConjecture/Partitions/Rectangle.lean))
- `YoungDiagram.rowLen_rectComplement` ([KlebersConjecture/Partitions/Rectangle.lean](../KlebersConjecture/Partitions/Rectangle.lean))
- `YoungDiagram.rectComplement_rectComplement` ([KlebersConjecture/Partitions/Rectangle.lean](../KlebersConjecture/Partitions/Rectangle.lean))
- `YoungDiagram.mem_rectComplement_iff` ([KlebersConjecture/Partitions/Rectangle.lean](../KlebersConjecture/Partitions/Rectangle.lean))
- `YoungDiagram.card_add_rectComplement` ([KlebersConjecture/Partitions/Rectangle.lean](../KlebersConjecture/Partitions/Rectangle.lean))

### Theorem 1.1 (Kleber's conjecture) (`thm-rectangular`)

Status: **formalized**

- `ComplementaryProducts.kleber_linearIndependent` ([KlebersConjecture/Paper/RectangularIndependence.lean](../KlebersConjecture/Paper/RectangularIndependence.lean))
- `ComplementaryProducts.kleber_linearIndependent_tensor` ([KlebersConjecture/Paper/TensorIndependence.lean](../KlebersConjecture/Paper/TensorIndependence.lean))

### The $\theta$-splittings $\mathrm{Split}(\theta)$ and the unordered complementary pairs (Section 1)

Status: **formalized**

- `ComplementaryProducts.splittings` ([KlebersConjecture/Paper/Indices.lean](../KlebersConjecture/Paper/Indices.lean))
- `ComplementaryProducts.mem_splittings` ([KlebersConjecture/Paper/Indices.lean](../KlebersConjecture/Paper/Indices.lean))
- `ComplementaryProducts.complementaryPairs` ([KlebersConjecture/Paper/Indices.lean](../KlebersConjecture/Paper/Indices.lean))
- `ComplementaryProducts.mem_complementaryPairs` ([KlebersConjecture/Paper/Indices.lean](../KlebersConjecture/Paper/Indices.lean))
- `ComplementaryProducts.schurPairProduct_mk` ([KlebersConjecture/Paper/Products.lean](../KlebersConjecture/Paper/Products.lean))

### Theorem 1.2 (`thm-core`)

Status: **formalized**

- `ComplementaryProducts.splitting_linearIndependent` ([KlebersConjecture/Paper/SplittingIndependence.lean](../KlebersConjecture/Paper/SplittingIndependence.lean))
- `ComplementaryProducts.splitting_linearIndependent_tensor` ([KlebersConjecture/Paper/TensorIndependence.lean](../KlebersConjecture/Paper/TensorIndependence.lean))

### The Koike–Terada universal characters $s\_{\[\lambda\]}$ (Section 1)

Status: **formalized**

Here $s\_{\[\lambda\]}$ is the symplectic universal character, given by the integral Koike–Terada determinant with an undoubled first column.

- `SymmetricFunction.symplecticCharacter` ([KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Basic.lean](../KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Basic.lean))
- `SymmetricFunction.symplecticCharacter_eq_det` ([KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Basic.lean](../KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Basic.lean))

### The $s\_{\[\lambda\]}$ form a basis, and the class of $s\_{\[\lambda\]}$ in $F\_{\le \lvert\lambda\rvert}/F\_{\le \lvert\lambda\rvert-1}$ is that of $s\_\lambda$ (Section 1)

Status: **formalized**

Cited in the paper and proved here. The Jacobi–Trudi identity shows that $s\_{\[\lambda\]}-s\_\lambda$ has degree below $\lvert\lambda\rvert$, and unitriangularity then gives a basis over any commutative ring.

- `SymmetricFunction.symplecticCharacterBasis` ([KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Basis.lean](../KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Basis.lean))
- `SymmetricFunction.symplecticCharacter_sub_schur_mem` ([KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Grading.lean](../KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Grading.lean))
- `SymmetricFunction.exists_symplecticCharacterBasis` ([KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Basis.lean](../KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Basis.lean))
- `SymmetricFunction.symplecticCharacterBasis_apply` ([KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Basis.lean](../KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Basis.lean))
- `SymmetricFunction.symplecticCharacter_mem_degreeFiltration` ([KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Grading.lean](../KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Grading.lean))
- `SymmetricFunction.homogeneousComponent_symplecticCharacter` ([KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Grading.lean](../KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Grading.lean))
- `SymmetricFunction.symplecticCharacter_bot` ([KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Basic.lean](../KlebersConjecture/SymmetricFunctions/SymplecticCharacters/Basic.lean))

### The degree filtration $F\_{\le d}$ (Section 1) and the Littlewood–Richardson coefficients $c^\nu\_{\lambda,\mu}$ (Section 2.2)

Status: **formalized**

- `SymmetricFunction.degreeFiltration` ([KlebersConjecture/SymmetricFunctions/Grading.lean](../KlebersConjecture/SymmetricFunctions/Grading.lean))
- `SymmetricFunction.mem_degreeFiltration_iff` ([KlebersConjecture/SymmetricFunctions/Grading.lean](../KlebersConjecture/SymmetricFunctions/Grading.lean))
- `SymmetricFunction.lrCoeff` ([KlebersConjecture/SymmetricFunctions/LittlewoodRichardson/Coefficients.lean](../KlebersConjecture/SymmetricFunctions/LittlewoodRichardson/Coefficients.lean))
- `SymmetricFunction.schurBasis_repr_schur_mul_schur` ([KlebersConjecture/SymmetricFunctions/LittlewoodRichardson/Coefficients.lean](../KlebersConjecture/SymmetricFunctions/LittlewoodRichardson/Coefficients.lean))

### Corollary 1.3 (`cor-koike-terada`)

Status: **formalized**

Here $s\_{\[\lambda\]}$ is the symplectic universal character.

- `ComplementaryProducts.symplectic_linearIndependent` ([KlebersConjecture/Paper/UniversalProducts.lean](../KlebersConjecture/Paper/UniversalProducts.lean))
- `ComplementaryProducts.symplectic_linearIndependent_tensor` ([KlebersConjecture/Paper/TensorIndependence.lean](../KlebersConjecture/Paper/TensorIndependence.lean))

### Theorem 1.4 (`thm-monomial`)

Status: **formalized**

- `ComplementaryProducts.monomial_linearIndependent` ([KlebersConjecture/Paper/MonomialIndependence.lean](../KlebersConjecture/Paper/MonomialIndependence.lean))
- `ComplementaryProducts.monomial_linearIndependent_int` ([KlebersConjecture/Paper/MonomialIndependence.lean](../KlebersConjecture/Paper/MonomialIndependence.lean))
- `ComplementaryProducts.monomial_linearIndependent_tensor` ([KlebersConjecture/Paper/TensorIndependence.lean](../KlebersConjecture/Paper/TensorIndependence.lean))
- `ComplementaryProducts.monomial_linearIndependent_int_tensor` ([KlebersConjecture/Paper/TensorIndependence.lean](../KlebersConjecture/Paper/TensorIndependence.lean))

### The bases $m\_\lambda$, $h\_\lambda$, $s\_\lambda$ and $p\_\lambda$, the presentations $\Lambda\_R=R\[h\_1,h\_2,\ldots\]$ and $\Lambda\_{\mathbb{F}}=\mathbb{F}\[p\_1,p\_2,\ldots\]$, and $\Lambda\_R=R\otimes\_{\mathbb{Z}}\Lambda\_{\mathbb{Z}}$ (Section 2.1)

Status: **formalized**

Cited in the paper and proved here. Here $\Lambda\_R$ is defined as the bounded-degree symmetric power series over $R$, so $\Lambda\_R\cong R\otimes\_{\mathbb{Z}}\Lambda\_{\mathbb{Z}}$ is a theorem.

- `SymmetricFunction.monomialBasis` ([KlebersConjecture/SymmetricFunctions/Bases/MonomialBasis.lean](../KlebersConjecture/SymmetricFunctions/Bases/MonomialBasis.lean))
- `SymmetricFunction.completeBasis` ([KlebersConjecture/SymmetricFunctions/Bases/CompleteBasis.lean](../KlebersConjecture/SymmetricFunctions/Bases/CompleteBasis.lean))
- `SymmetricFunction.schurBasis` ([KlebersConjecture/SymmetricFunctions/Bases/SchurBasis.lean](../KlebersConjecture/SymmetricFunctions/Bases/SchurBasis.lean))
- `SymmetricFunction.powerSumBasis` ([KlebersConjecture/SymmetricFunctions/Bases/PowerSumBasis.lean](../KlebersConjecture/SymmetricFunctions/Bases/PowerSumBasis.lean))
- `SymmetricFunction.completePresentation` ([KlebersConjecture/SymmetricFunctions/Presentations/CompletePresentation.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompletePresentation.lean))
- `SymmetricFunction.baseChangeEquiv` ([KlebersConjecture/SymmetricFunctions/ScalarExtension/BaseChange.lean](../KlebersConjecture/SymmetricFunctions/ScalarExtension/BaseChange.lean))
- `SymmetricFunction.exists_monomialBasis` ([KlebersConjecture/SymmetricFunctions/Bases/MonomialBasis.lean](../KlebersConjecture/SymmetricFunctions/Bases/MonomialBasis.lean))
- `SymmetricFunction.monomialBasis_apply` ([KlebersConjecture/SymmetricFunctions/Bases/MonomialBasis.lean](../KlebersConjecture/SymmetricFunctions/Bases/MonomialBasis.lean))
- `SymmetricFunction.monomialBasis_repr_apply` ([KlebersConjecture/SymmetricFunctions/Bases/MonomialBasis.lean](../KlebersConjecture/SymmetricFunctions/Bases/MonomialBasis.lean))
- `SymmetricFunction.exists_completeBasis` ([KlebersConjecture/SymmetricFunctions/Bases/CompleteBasis.lean](../KlebersConjecture/SymmetricFunctions/Bases/CompleteBasis.lean))
- `SymmetricFunction.completeBasis_apply` ([KlebersConjecture/SymmetricFunctions/Bases/CompleteBasis.lean](../KlebersConjecture/SymmetricFunctions/Bases/CompleteBasis.lean))
- `SymmetricFunction.exists_schurBasis` ([KlebersConjecture/SymmetricFunctions/Bases/SchurBasis.lean](../KlebersConjecture/SymmetricFunctions/Bases/SchurBasis.lean))
- `SymmetricFunction.schurBasis_apply` ([KlebersConjecture/SymmetricFunctions/Bases/SchurBasis.lean](../KlebersConjecture/SymmetricFunctions/Bases/SchurBasis.lean))
- `SymmetricFunction.exists_powerSumBasis` ([KlebersConjecture/SymmetricFunctions/Bases/PowerSumBasis.lean](../KlebersConjecture/SymmetricFunctions/Bases/PowerSumBasis.lean))
- `SymmetricFunction.powerSumBasis_apply` ([KlebersConjecture/SymmetricFunctions/Bases/PowerSumBasis.lean](../KlebersConjecture/SymmetricFunctions/Bases/PowerSumBasis.lean))
- `SymmetricFunction.exists_completePresentation` ([KlebersConjecture/SymmetricFunctions/Presentations/CompletePresentation.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompletePresentation.lean))
- `SymmetricFunction.completePresentation_apply_X` ([KlebersConjecture/SymmetricFunctions/Presentations/CompletePresentation.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompletePresentation.lean))
- `SymmetricFunction.completePresentation_toAlgHom` ([KlebersConjecture/SymmetricFunctions/Presentations/CompletePresentation.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompletePresentation.lean))
- `SymmetricFunction.powerSumPresentation` ([KlebersConjecture/SymmetricFunctions/Presentations/PowerSumPresentation.lean](../KlebersConjecture/SymmetricFunctions/Presentations/PowerSumPresentation.lean))
- `SymmetricFunction.exists_powerSumPresentation` ([KlebersConjecture/SymmetricFunctions/Presentations/PowerSumPresentation.lean](../KlebersConjecture/SymmetricFunctions/Presentations/PowerSumPresentation.lean))
- `SymmetricFunction.powerSumPresentation_apply_X` ([KlebersConjecture/SymmetricFunctions/Presentations/PowerSumPresentation.lean](../KlebersConjecture/SymmetricFunctions/Presentations/PowerSumPresentation.lean))
- `SymmetricFunction.powerSumPresentation_toAlgHom` ([KlebersConjecture/SymmetricFunctions/Presentations/PowerSumPresentation.lean](../KlebersConjecture/SymmetricFunctions/Presentations/PowerSumPresentation.lean))
- `SymmetricFunction.exists_baseChangeEquiv` ([KlebersConjecture/SymmetricFunctions/ScalarExtension/BaseChange.lean](../KlebersConjecture/SymmetricFunctions/ScalarExtension/BaseChange.lean))
- `SymmetricFunction.baseChangeEquiv_tmul` ([KlebersConjecture/SymmetricFunctions/ScalarExtension/BaseChange.lean](../KlebersConjecture/SymmetricFunctions/ScalarExtension/BaseChange.lean))
- `SymmetricFunction.baseChangeEquiv_tmul_monomial` ([KlebersConjecture/SymmetricFunctions/ScalarExtension/BaseChange.lean](../KlebersConjecture/SymmetricFunctions/ScalarExtension/BaseChange.lean))
- `SymmetricFunction.baseChangeEquiv_toAlgHom` ([KlebersConjecture/SymmetricFunctions/ScalarExtension/BaseChange.lean](../KlebersConjecture/SymmetricFunctions/ScalarExtension/BaseChange.lean))
- `SymmetricFunction.elementaryPresentation` ([KlebersConjecture/SymmetricFunctions/Presentations/ElementaryPresentation.lean](../KlebersConjecture/SymmetricFunctions/Presentations/ElementaryPresentation.lean))
- `SymmetricFunction.exists_elementaryPresentation` ([KlebersConjecture/SymmetricFunctions/Presentations/ElementaryPresentation.lean](../KlebersConjecture/SymmetricFunctions/Presentations/ElementaryPresentation.lean))
- `SymmetricFunction.elementaryPresentation_apply_X` ([KlebersConjecture/SymmetricFunctions/Presentations/ElementaryPresentation.lean](../KlebersConjecture/SymmetricFunctions/Presentations/ElementaryPresentation.lean))
- `SymmetricFunction.elementaryBasis` ([KlebersConjecture/SymmetricFunctions/Bases/ElementaryBasis.lean](../KlebersConjecture/SymmetricFunctions/Bases/ElementaryBasis.lean))
- `SymmetricFunction.elementaryBasis_apply` ([KlebersConjecture/SymmetricFunctions/Bases/ElementaryBasis.lean](../KlebersConjecture/SymmetricFunctions/Bases/ElementaryBasis.lean))

### The monomial, complete, power-sum and Schur functions as defined in Section 2.1

Status: **formalized**

Here $s\_\lambda$ is defined by its Kostka expansion and shown to satisfy the bialternant formula $s\_\lambda a\_\delta=a\_{\lambda+\delta}$, which is proved in the Tau Ceti library.

- `SymmetricFunction.restrict_schur_eq_diagramSchurPoly` ([KlebersConjecture/SymmetricFunctions/Families/Schur.lean](../KlebersConjecture/SymmetricFunctions/Families/Schur.lean))
- `SymmetricFunction.restrict_schur_mul_alternant` ([KlebersConjecture/SymmetricFunctions/Families/Schur.lean](../KlebersConjecture/SymmetricFunctions/Families/Schur.lean))
- `SymmetricFunction.schur_eq_of_restrict_alternant` ([KlebersConjecture/SymmetricFunctions/Families/Schur.lean](../KlebersConjecture/SymmetricFunctions/Families/Schur.lean))
- `SymmetricFunction.restrict_monomial` ([KlebersConjecture/SymmetricFunctions/Families/Monomial.lean](../KlebersConjecture/SymmetricFunctions/Families/Monomial.lean))
- `SymmetricFunction.coeff_complete_nat` ([KlebersConjecture/SymmetricFunctions/Families/Families.lean](../KlebersConjecture/SymmetricFunctions/Families/Families.lean))
- `SymmetricFunction.restrict_complete_nat` ([KlebersConjecture/SymmetricFunctions/Families/Families.lean](../KlebersConjecture/SymmetricFunctions/Families/Families.lean))
- `SymmetricFunction.restrict_powerSum` ([KlebersConjecture/SymmetricFunctions/Families/Families.lean](../KlebersConjecture/SymmetricFunctions/Families/Families.lean))
- `SymmetricFunction.killCompl_restrict` ([KlebersConjecture/SymmetricFunctions/Restriction.lean](../KlebersConjecture/SymmetricFunctions/Restriction.lean))

### Equation (2.1): the Jacobi–Trudi identity (`eq-jacobi-trudi`)

Status: **formalized**

Cited in the paper and proved here, in finitely many variables from the bialternant formula, then by letting the number of variables grow.

- `SymmetricFunction.schur_eq_det_jacobiTrudiMatrix` ([KlebersConjecture/SymmetricFunctions/JacobiTrudi/JacobiTrudi.lean](../KlebersConjecture/SymmetricFunctions/JacobiTrudi/JacobiTrudi.lean))

### Coefficient extraction $\[h\_a^j\]\_{\mathrm{p}}$ and $\[p\_d^j\]\_{\mathrm{p}}$ (Section 2.1), and the derivations $\partial/\partial h\_n$ (Section 2.3)

Status: **formalized**

- `SymmetricFunction.completeCoeff` ([KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean))
- `SymmetricFunction.completeDegree` ([KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean))
- `SymmetricFunction.completeCoeff_generator_mul` ([KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean))
- `SymmetricFunction.mem_adjoin_complete_iff` ([KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean))
- `SymmetricFunction.powerSumCoeff` ([KlebersConjecture/SymmetricFunctions/Presentations/PowerSumCoefficients.lean](../KlebersConjecture/SymmetricFunctions/Presentations/PowerSumCoefficients.lean))
- `SymmetricFunction.completeDerivation` ([KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean))
- `SymmetricFunction.completeDerivation_generator` ([KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean))
- `SymmetricFunction.derivation_ext_complete` ([KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean))
- `SymmetricFunction.completeCoeff_reconstruction` ([KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean))
- `SymmetricFunction.completeCoeff_sum_mul_pow` ([KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean))
- `SymmetricFunction.completeCoeff_generator_pow` ([KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean))
- `SymmetricFunction.completeCoeff_mul_of_degreeOf_eq_zero` ([KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean))
- `SymmetricFunction.completeCoeff_mem_adjoin` ([KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean](../KlebersConjecture/SymmetricFunctions/Presentations/CompleteCalculus.lean))
- `SymmetricFunction.powerSumCoeff_reconstruction` ([KlebersConjecture/SymmetricFunctions/Presentations/PowerSumCoefficients.lean](../KlebersConjecture/SymmetricFunctions/Presentations/PowerSumCoefficients.lean))
- `SymmetricFunction.powerSumCoeff_sum_mul_pow` ([KlebersConjecture/SymmetricFunctions/Presentations/PowerSumCoefficients.lean](../KlebersConjecture/SymmetricFunctions/Presentations/PowerSumCoefficients.lean))
- `SymmetricFunction.powerSumCoeff_mem_adjoin` ([KlebersConjecture/SymmetricFunctions/Presentations/PowerSumCoefficients.lean](../KlebersConjecture/SymmetricFunctions/Presentations/PowerSumCoefficients.lean))

### $\mathrm{Top}(f)$ (Section 2.1)

Status: **formalized**

- `SymmetricFunction.topRow` ([KlebersConjecture/SymmetricFunctions/Projection/FirstRowProjection.lean](../KlebersConjecture/SymmetricFunctions/Projection/FirstRowProjection.lean))
- `SymmetricFunction.topRow_le_iff` ([KlebersConjecture/SymmetricFunctions/Projection/FirstRowProjection.lean](../KlebersConjecture/SymmetricFunctions/Projection/FirstRowProjection.lean))

### The Littlewood–Richardson rule in skew-tableau form (Section 2.2)

Status: **formalized**

Cited in the paper and proved here, by a sign-reversing involution after Stembridge on tableaux of straight shape, then a bijection to the skew tableaux of the paper.

- `SymmetricFunction.lrCoeff_eq_card_lrTableaux` ([KlebersConjecture/SymmetricFunctions/LittlewoodRichardson/TableauTranspose.lean](../KlebersConjecture/SymmetricFunctions/LittlewoodRichardson/TableauTranspose.lean))
- `SymmetricFunction.lrCoeff_eq_zero_of_not_le` ([KlebersConjecture/SymmetricFunctions/LittlewoodRichardson/Containment.lean](../KlebersConjecture/SymmetricFunctions/LittlewoodRichardson/Containment.lean))
- `SymmetricFunction.card_eq_of_lrCoeff_ne_zero` ([KlebersConjecture/SymmetricFunctions/LittlewoodRichardson/Containment.lean](../KlebersConjecture/SymmetricFunctions/LittlewoodRichardson/Containment.lean))

### Lemma 2.2 (`lem-row-removal`)

Status: **formalized**

The proof uses the straight-shape form of the Littlewood–Richardson rule, with tableaux of shape $\beta$ instead of shape $\nu/\alpha$.

- `SymmetricFunction.rowLen_zero_le_of_lrCoeff_ne_zero` ([KlebersConjecture/SymmetricFunctions/LittlewoodRichardson/RowRemoval.lean](../KlebersConjecture/SymmetricFunctions/LittlewoodRichardson/RowRemoval.lean))
- `SymmetricFunction.lrCoeff_eq_lrCoeff_dropRows` ([KlebersConjecture/SymmetricFunctions/LittlewoodRichardson/RowRemoval.lean](../KlebersConjecture/SymmetricFunctions/LittlewoodRichardson/RowRemoval.lean))

### Corollary 2.3 (`cor-top-product`)

Status: **formalized**

The lower bound uses $c^{\alpha+\beta}\_{\alpha,\beta}=1$ directly, without row removal.

- `SymmetricFunction.topRow_schur_mul_schur` ([KlebersConjecture/SymmetricFunctions/Projection/FirstRowProducts.lean](../KlebersConjecture/SymmetricFunctions/Projection/FirstRowProducts.lean))

### Definition 2.4

Status: **formalized**

- `SymmetricFunction.jacobiTrudiMatrix` ([KlebersConjecture/SymmetricFunctions/JacobiTrudi/JacobiTrudiMatrix.lean](../KlebersConjecture/SymmetricFunctions/JacobiTrudi/JacobiTrudiMatrix.lean))
- `YoungDiagram.removeFirstRowCol` ([KlebersConjecture/Partitions/Rows.lean](../KlebersConjecture/Partitions/Rows.lean))
- `SymmetricFunction.jacobiTrudiMatrix_apply` ([KlebersConjecture/SymmetricFunctions/JacobiTrudi/JacobiTrudiMatrix.lean](../KlebersConjecture/SymmetricFunctions/JacobiTrudi/JacobiTrudiMatrix.lean))
- `YoungDiagram.rowLen_removeFirstRowCol` ([KlebersConjecture/Partitions/Rows.lean](../KlebersConjecture/Partitions/Rows.lean))

### Lemma 2.5 (`lem-jt-derivative`)

Status: **formalized**

The Jacobi–Trudi determinant is expanded along the first row instead of the last column.

- `SymmetricFunction.degreeOf_schur` ([KlebersConjecture/SymmetricFunctions/Presentations/SchurCompleteCalculus.lean](../KlebersConjecture/SymmetricFunctions/Presentations/SchurCompleteCalculus.lean))
- `SymmetricFunction.completeCoeff_schur` ([KlebersConjecture/SymmetricFunctions/Presentations/SchurCompleteCalculus.lean](../KlebersConjecture/SymmetricFunctions/Presentations/SchurCompleteCalculus.lean))
- `SymmetricFunction.completeDerivation_schur` ([KlebersConjecture/SymmetricFunctions/Presentations/SchurCompleteCalculus.lean](../KlebersConjecture/SymmetricFunctions/Presentations/SchurCompleteCalculus.lean))

### Definition 3.1 (`def-first-row-projection`)

Status: **formalized**

- `SymmetricFunction.firstRowProjection` ([KlebersConjecture/SymmetricFunctions/Projection/FirstRowProjection.lean](../KlebersConjecture/SymmetricFunctions/Projection/FirstRowProjection.lean))
- `SymmetricFunction.firstRowProjection_schur` ([KlebersConjecture/SymmetricFunctions/Projection/FirstRowProjection.lean](../KlebersConjecture/SymmetricFunctions/Projection/FirstRowProjection.lean))

### Lemma 3.2 (`lem-top-row-projection`)

Status: **formalized**

- `SymmetricFunction.firstRowProjection_schur_mul_schur` ([KlebersConjecture/SymmetricFunctions/Projection/FirstRowProducts.lean](../KlebersConjecture/SymmetricFunctions/Projection/FirstRowProducts.lean))

### Lemma 3.3 (`lem-oriented-block`)

Status: **formalized**

- `ComplementaryProducts.oriented_linearIndependent` ([KlebersConjecture/Paper/OrientedIndependence.lean](../KlebersConjecture/Paper/OrientedIndependence.lean))

### Lemma 3.7 (`lem-maximal-self-pair`)

Status: **formalized**

- `ComplementaryProducts.coeff_eq_zero_of_maximal_self_pair` ([KlebersConjecture/Paper/MaximalSelfPair.lean](../KlebersConjecture/Paper/MaximalSelfPair.lean))

### $\mathrm{gap}(\lambda)$ is a partition, and $\mathrm{gap}(\lambda^\vee)=\mathrm{gap}(\lambda)$ (Section 4)

Status: **formalized**

- `ComplementaryProducts.gap_rectComplement` ([KlebersConjecture/Paper/GapTails.lean](../KlebersConjecture/Paper/GapTails.lean))

### Gap vectors, the shapes $\Theta\_g$ and the projections $\Pi\_g$ (Section 4)

Status: **formalized**

- `ComplementaryProducts.gap` ([KlebersConjecture/Paper/Gap.lean](../KlebersConjecture/Paper/Gap.lean))
- `ComplementaryProducts.gapShape` ([KlebersConjecture/Paper/Gap.lean](../KlebersConjecture/Paper/Gap.lean))
- `ComplementaryProducts.rowLen_gapShape_even` ([KlebersConjecture/Paper/Gap.lean](../KlebersConjecture/Paper/Gap.lean))
- `ComplementaryProducts.rowLen_gapShape_odd` ([KlebersConjecture/Paper/Gap.lean](../KlebersConjecture/Paper/Gap.lean))
- `ComplementaryProducts.gapProjection` ([KlebersConjecture/Paper/GapProjection.lean](../KlebersConjecture/Paper/GapProjection.lean))
- `ComplementaryProducts.gapProjection_apply` ([KlebersConjecture/Paper/GapProjection.lean](../KlebersConjecture/Paper/GapProjection.lean))

### Equation (4.1) (`eq-fixed-gap-tail-sum`)

Status: **formalized**

- `ComplementaryProducts.dropRows_add_dropRows_complement` ([KlebersConjecture/Paper/GapTails.lean](../KlebersConjecture/Paper/GapTails.lean))

### Example 4.2

Status: **formalized**

- `ComplementaryProducts.GapExample.shape_le_rectangle` ([KlebersConjecture/Paper/Examples.lean](../KlebersConjecture/Paper/Examples.lean))
- `ComplementaryProducts.GapExample.rectComplement_shape` ([KlebersConjecture/Paper/Examples.lean](../KlebersConjecture/Paper/Examples.lean))
- `ComplementaryProducts.GapExample.gap_shape` ([KlebersConjecture/Paper/Examples.lean](../KlebersConjecture/Paper/Examples.lean))
- `ComplementaryProducts.GapExample.gap_complementShape` ([KlebersConjecture/Paper/Examples.lean](../KlebersConjecture/Paper/Examples.lean))
- `ComplementaryProducts.GapExample.dropRows_shape` ([KlebersConjecture/Paper/Examples.lean](../KlebersConjecture/Paper/Examples.lean))
- `ComplementaryProducts.GapExample.dropRows_complementShape` ([KlebersConjecture/Paper/Examples.lean](../KlebersConjecture/Paper/Examples.lean))
- `ComplementaryProducts.GapExample.tails_add` ([KlebersConjecture/Paper/Examples.lean](../KlebersConjecture/Paper/Examples.lean))
- `ComplementaryProducts.GapExample.gapProjection_eq` ([KlebersConjecture/Paper/Examples.lean](../KlebersConjecture/Paper/Examples.lean))
- `ComplementaryProducts.GapExample.firstRowProjection_eleven` ([KlebersConjecture/Paper/Examples.lean](../KlebersConjecture/Paper/Examples.lean))
- `ComplementaryProducts.GapExample.gapProjection_shape` ([KlebersConjecture/Paper/Examples.lean](../KlebersConjecture/Paper/Examples.lean))

### Lemma 4.3 (`lem-gap-block`)

Status: **formalized**

- `ComplementaryProducts.gapProjection_of_gap_eq` ([KlebersConjecture/Paper/GapBlocks.lean](../KlebersConjecture/Paper/GapBlocks.lean))
- `ComplementaryProducts.gapProjection_of_gap_lt` ([KlebersConjecture/Paper/GapBlocks.lean](../KlebersConjecture/Paper/GapBlocks.lean))

### Lemma 4.4 (`lem-fixed-gap-injective`)

Status: **formalized**

- `ComplementaryProducts.tailPair_injective` ([KlebersConjecture/Paper/GapTails.lean](../KlebersConjecture/Paper/GapTails.lean))

### Example 5.1

Status: **formalized**

- `ComplementaryProducts.SetPartitionExample.mem_parts_pairs` ([KlebersConjecture/Paper/Examples.lean](../KlebersConjecture/Paper/Examples.lean))
- `ComplementaryProducts.SetPartitionExample.mem_parts_singletonsAndPair` ([KlebersConjecture/Paper/Examples.lean](../KlebersConjecture/Paper/Examples.lean))
- `ComplementaryProducts.SetPartitionExample.mem_parts_twoPairs` ([KlebersConjecture/Paper/Examples.lean](../KlebersConjecture/Paper/Examples.lean))
- `ComplementaryProducts.SetPartitionExample.refines` ([KlebersConjecture/Paper/Examples.lean](../KlebersConjecture/Paper/Examples.lean))

### The Möbius function of the lattice of set partitions: $\mu(\hat0,\hat1)=(-1)^{k-1}(k-1)!$ (Section 5)

Status: **formalized**

Cited in the paper and proved here, by counting maps by their kernels and comparing the coefficients of $x$ in the falling factorial.

- `Finpartition.mu_bot_top` ([KlebersConjecture/SetPartitions/Moebius.lean](../KlebersConjecture/SetPartitions/Moebius.lean))

### Lemma 5.2 (`lem-monomial-top-p`)

Status: **formalized**

- `SymmetricFunction.monomial_eq_smul_powerSum_add` ([KlebersConjecture/SymmetricFunctions/Monomial/MonomialPowerSum.lean](../KlebersConjecture/SymmetricFunctions/Monomial/MonomialPowerSum.lean))

### Remark 5.8

Status: **formalized**

Stated for every commutative ring of characteristic 2. It follows from $m\_{(1)}^2=m\_{(2)}+2m\_{(1,1)}$, which holds over any commutative ring.

- `SymmetricFunction.powerSum_one_sq` ([KlebersConjecture/SymmetricFunctions/Families/PowerSumIdentities.lean](../KlebersConjecture/SymmetricFunctions/Families/PowerSumIdentities.lean))
- `ComplementaryProducts.monomial_singleRow_one_sq_eq_add` ([KlebersConjecture/Paper/CharacteristicTwo.lean](../KlebersConjecture/Paper/CharacteristicTwo.lean))
- `ComplementaryProducts.monomial_singleRow_one_sq_charP_two` ([KlebersConjecture/Paper/CharacteristicTwo.lean](../KlebersConjecture/Paper/CharacteristicTwo.lean))
- `ComplementaryProducts.monomialPairProduct_charP_two` ([KlebersConjecture/Paper/CharacteristicTwo.lean](../KlebersConjecture/Paper/CharacteristicTwo.lean))
- `ComplementaryProducts.not_monomial_linearIndependent_charP_two` ([KlebersConjecture/Paper/CharacteristicTwo.lean](../KlebersConjecture/Paper/CharacteristicTwo.lean))
- `ComplementaryProducts.monomial_singleRow_one_sq` ([KlebersConjecture/Paper/CharacteristicTwo.lean](../KlebersConjecture/Paper/CharacteristicTwo.lean))
- `ComplementaryProducts.monomialPairProduct_char_two` ([KlebersConjecture/Paper/CharacteristicTwo.lean](../KlebersConjecture/Paper/CharacteristicTwo.lean))
- `ComplementaryProducts.not_monomial_linearIndependent_char_two` ([KlebersConjecture/Paper/CharacteristicTwo.lean](../KlebersConjecture/Paper/CharacteristicTwo.lean))
