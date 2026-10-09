# Lean verification of *Kleber's conjecture and complementary products of symmetric functions*

This repository, `rhodges-math/klebers-conjecture` (release 2.0.0), contains a
Lean 4 formalization of *Kleber's conjecture and complementary products of
symmetric functions* (Reuven Hodges and Hanzhang Yin, 2026),
[arXiv:2607.12120](https://arxiv.org/abs/2607.12120).

All results of the paper are formalized. Over every commutative ring $R$, the
formalization proves that the products $s\_\lambda s\_{\lambda^\vee}$ indexed by
the unordered complementary pairs in an $a \times b$ rectangle are linearly
independent in $\Lambda\_R$ (Theorem 1.1, Kleber's conjecture), and that for
every partition $\theta$ the products $s\_\alpha s\_\beta$ indexed by the unordered
pairs with $\alpha+\beta=\theta$ are linearly independent (Theorem 1.2). It
proves the same independence for the products $s\_{\[\lambda\]}s\_{\[\lambda^\vee\]}$
of Koike–Terada universal characters over every field (Corollary 1.3), and for
the monomial products $m\_\lambda m\_{\lambda^\vee}$ over every field of
characteristic zero and over $\mathbb{Z}$ (Theorem 1.4). Every other statement
of the paper is formalized as well: its lemmas, corollaries, definitions,
examples, displayed equations and remark, together with the standard results
it cites, 33 entries in all, listed in [docs/STATEMENTS.md](docs/STATEMENTS.md).

These results are proved with no hypotheses beyond Lean's standard axioms. The
development uses Lean **4.35.0-rc3**, a pinned version of **Mathlib**, and the
**Tau Ceti** library. Lean 4.35.0-rc3 is a release candidate; the pin may move
to the stable Lean 4.35.0 release.

Three of its four libraries are independent of the paper and may be of use
beyond it: partitions as Young diagrams, the lattice of set partitions, and the
ring of symmetric functions over any commutative ring, with its bases and
presentations, the Jacobi–Trudi identity, the Littlewood–Richardson rule and
the symplectic universal characters; see [Libraries](#libraries).

## AI assistance and verification

**I used GPT-6.1 Sol and Claude Opus 5.5 to help construct the Lean files.** I
reviewed all definitions, hypotheses, and theorem statements to check that
they faithfully express the intended mathematics, including the results of
the paper listed below.

The development was compiled with Lean, and the axiom dependencies of every
declaration were audited: they use only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorry`-based proofs or additional unproved axioms.
The mathematical review addresses the correspondence between the formal
statements and the paper, which Lean's proof checking alone does not establish.

## Main results

The entry point is
[KlebersConjecture/Paper/Main.lean](KlebersConjecture/Paper/Main.lean),
which imports every result of the paper; [docs/STATEMENTS.md](docs/STATEMENTS.md)
lists each statement of the paper with its Lean counterparts.

```lean
import KlebersConjecture.Paper.Main

open ComplementaryProducts

#check kleber_linearIndependent
#check splitting_linearIndependent
#check symplectic_linearIndependent
#check monomial_linearIndependent
#check monomial_linearIndependent_int
```

Names below are relative to the namespace `ComplementaryProducts`, except
those beginning with `SymmetricFunction.`, `YoungDiagram.` or `Finpartition.`,
which are in the general libraries.

### Notation

The ring $\Lambda\_R$ of symmetric functions over a commutative ring $R$ is
`SymmetricFunction R`: the power series in the variables $x\_1, x\_2, \ldots$
(`MvPowerSeries.X (i - 1)` for $x\_i$) that are invariant under every
permutation of the variables and have bounded degree. The paper defines
$\Lambda\_R$ as $R \otimes\_{\mathbb{Z}} \Lambda\_{\mathbb{Z}}$;
`SymmetricFunction.baseChangeEquiv R` identifies the two, and every main result
is also stated in $R \otimes\_{\mathbb{Z}} \Lambda\_{\mathbb{Z}}$ (the
declarations ending in `_tensor`), an $R$-module through its structure of
$R$-algebra. Partitions are Mathlib's Young diagrams,
with rows numbered from 0. Linear independence is Mathlib's `LinearIndependent`,
for a family indexed by a finite set of unordered pairs, viewed as a type.

| Paper | Lean |
| --- | --- |
| $\Lambda\_R$, $R \otimes\_{\mathbb{Z}} \Lambda\_{\mathbb{Z}}$ | `SymmetricFunction R`, `R ⊗[ℤ] SymmetricFunction ℤ` |
| A partition $\lambda$; $\lambda\_i$; $\ell(\lambda)$; $\lvert\lambda\rvert$ | `μ : YoungDiagram`; `μ.rowLen (i - 1)`; `μ.colLen 0`; `μ.card` |
| $\alpha+\beta$ (componentwise), $\bar\lambda=(\lambda\_2,\lambda\_3,\ldots)$ | `α + β`, `μ.dropRows 1` |
| The rectangle $(b^a)$, $\lambda \subseteq (b^a)$, $\lambda^\vee$ | `YoungDiagram.rectangle a b`, `μ ≤ YoungDiagram.rectangle a b`, `YoungDiagram.rectComplement a b μ` |
| $m\_\lambda$, $h\_r$ ($r \in \mathbb{Z}$), $p\_r$, $s\_\lambda$ | `SymmetricFunction.monomial R μ`, `SymmetricFunction.complete R r`, `SymmetricFunction.powerSum R r`, `SymmetricFunction.schur R μ` |
| $s\_{\[\lambda\]}$ | `SymmetricFunction.symplecticCharacter R μ` |
| $c^\nu\_{\alpha,\beta}$ | `SymmetricFunction.lrCoeff α β ν` |
| $F\_{\le d}\Lambda\_R$ | `SymmetricFunction.degreeFiltration R d` |
| An unordered pair $\lbrace\alpha,\beta\rbrace$ | `s(α, β) : Sym2 YoungDiagram` (Mathlib) |
| $\mathrm{Split}(\theta)$; the complementary pairs in $(b^a)$ | `splittings θ`; `complementaryPairs a b` |
| $s\_\alpha s\_\beta$, $m\_\alpha m\_\beta$, $s\_{\[\alpha\]}s\_{\[\beta\]}$ for a pair $\lbrace\alpha,\beta\rbrace$ | `schurPairProduct R p`, `monomialPairProduct R p`, `symplecticPairProduct R p` |

The paper defines $s\_\lambda$ as the stable limit of the bialternants
$\det(x\_i^{\lambda\_j+n-j})/\det(x\_i^{n-j})$. Lean defines `SymmetricFunction.schur` by its
monomial expansion, with Tau Ceti's Kostka numbers, and proves that its
restriction to $n \ge \ell(\lambda)$ variables multiplied by the Vandermonde
determinant is the alternant $\det(x\_i^{\lambda\_j+n-j})$
(`SymmetricFunction.restrict_schur_mul_alternant`), and that this property
determines it (`SymmetricFunction.schur_eq_of_restrict_alternant`).

### Theorem 1.1: Kleber's conjecture

Let $R$ be a commutative ring, and let $a$ and $b$ be positive integers. In
$\Lambda\_R$, the products

$$
s\_\lambda s\_{\lambda^\vee}, \qquad \lambda \subseteq (b^a),
$$

indexed by unordered complementary pairs, are linearly independent over $R$.
Here $\lambda^\vee=(b-\lambda\_a,\ldots,b-\lambda\_1)$ is the complement of
$\lambda$ in the rectangle, rotated through $180^\circ$.

The index set `complementaryPairs a b` is the finite set of unordered pairs
`s(μ, YoungDiagram.rectComplement a b μ)` with `μ ≤ YoungDiagram.rectangle a b`;
a self-complementary partition gives a single pair. No hypothesis is added on
the ring. The proof follows the paper: the gap vector of $\lambda$ is unchanged
by complementation, the fixed-gap projections reduce a relation among the
products to a relation among products indexed by the splittings of one
partition, and Theorem 1.2 excludes it.

These declarations are in `ComplementaryProducts`
([RectangularIndependence.lean](KlebersConjecture/Paper/RectangularIndependence.lean),
[Gap.lean](KlebersConjecture/Paper/Gap.lean),
[GapTails.lean](KlebersConjecture/Paper/GapTails.lean),
[GapProjection.lean](KlebersConjecture/Paper/GapProjection.lean),
[GapBlocks.lean](KlebersConjecture/Paper/GapBlocks.lean),
[TensorIndependence.lean](KlebersConjecture/Paper/TensorIndependence.lean)).

| Declaration | Result |
| --- | --- |
| `kleber_linearIndependent` | All of Theorem 1.1 |
| `kleber_linearIndependent_tensor` | Theorem 1.1 in $R \otimes\_{\mathbb{Z}} \Lambda\_{\mathbb{Z}}$ |
| `gap_rectComplement` | $\mathrm{gap}(\lambda)$ is a valid gap vector, and $\mathrm{gap}(\lambda^\vee)=\mathrm{gap}(\lambda)$ |
| `dropRows_add_dropRows_complement` | Equation (4.1): the tails of a fixed-gap pair add up to $\Theta\_g$ |
| `gapProjection_of_gap_eq`, `gapProjection_of_gap_lt` | Lemma 4.3: $\Pi\_g$ on fixed-gap and on smaller-gap pairs |
| `tailPair_injective` | Lemma 4.4: for a fixed gap vector, the tails determine the pair |

### Theorem 1.2: products indexed by splittings

Let $R$ be a commutative ring, and let $\theta$ be a partition. In
$\Lambda\_R$, the products

$$
s\_\alpha s\_\beta, \qquad \lbrace\alpha,\beta\rbrace \in \mathrm{Split}(\theta),
$$

are linearly independent over $R$. Here $\mathrm{Split}(\theta)$ is the set of
unordered pairs $\lbrace\alpha,\beta\rbrace$ of partitions with
$\alpha+\beta=\theta$ componentwise.

The index set `splittings θ` is the finite set of unordered pairs `s(α, β)` with
`α + β = θ`, where `+` adds the lengths of corresponding rows. The proof follows
the paper: it differentiates a relation with respect to a complete generator
$h\_n$, through the presentation $\Lambda\_R=R\[h\_1,h\_2,\ldots\]$, which reduces
it to the ordered family of Lemma 3.3; the maximal self-pair is treated by
Lemma 3.7.

These declarations are in `ComplementaryProducts`
([SplittingIndependence.lean](KlebersConjecture/Paper/SplittingIndependence.lean),
[SplittingDerivative.lean](KlebersConjecture/Paper/SplittingDerivative.lean),
[OrientedIndependence.lean](KlebersConjecture/Paper/OrientedIndependence.lean),
[MaximalSelfPair.lean](KlebersConjecture/Paper/MaximalSelfPair.lean)) and
in the symmetric-function library.

| Declaration | Result |
| --- | --- |
| `splitting_linearIndependent` | All of Theorem 1.2 |
| `splitting_linearIndependent_tensor` | Theorem 1.2 in $R \otimes\_{\mathbb{Z}} \Lambda\_{\mathbb{Z}}$ |
| `SymmetricFunction.degreeOf_schur`, `SymmetricFunction.completeCoeff_schur`, `SymmetricFunction.completeDerivation_schur` | Lemma 2.5: $s\_\tau$ has degree one in $h\_{\tau\_1+\ell(\tau)-1}$, its coefficient is $(-1)^{\ell(\tau)-1}s\_{\partial\tau}$, and the derivatives |
| `SymmetricFunction.topRow_schur_mul_schur` | Corollary 2.3: $\mathrm{Top}(s\_\alpha s\_\beta)=\alpha\_1+\beta\_1$ |
| `SymmetricFunction.firstRowProjection_schur_mul_schur` | Lemma 3.2: $\pi\_{\mathrm{Top}}(s\_\alpha s\_\beta)=s\_{\bar\alpha}s\_{\bar\beta}$ |
| `oriented_linearIndependent` | Lemma 3.3: the products $s\_\alpha s\_{\partial\beta}$ over ordered pairs are independent |
| `coeff_eq_zero_of_maximal_self_pair` | Lemma 3.7: the coefficient of $s\_\tau^2$ vanishes |

### Corollary 1.3: universal characters

Let $\mathbb{F}$ be a field. For every rectangle $(b^a)$, the products

$$
s\_{\[\lambda\]}s\_{\[\lambda^\vee\]}, \qquad \lambda \subseteq (b^a),
$$

indexed by unordered complementary pairs, are linearly independent in
$\Lambda\_{\mathbb{F}}$. Here $s\_{\[\lambda\]}$ is the Koike–Terada universal
character.

The paper takes $s\_{\[\lambda\]}$ from Gao, Orelowitz, and Yong, who use the
symplectic universal character of Koike and Terada. Lean defines it by the
determinant $s\_{\[\lambda\]}=\det(M)$ with $M\_{i,1}=h\_{\lambda\_i-i+1}$ and
$M\_{i,j}=h\_{\lambda\_i-i+j}+h\_{\lambda\_i-i-j+2}$ for $j \ge 2$, of size
$\ell(\lambda)$. As in Theorem 1.1, the rectangle has positive side lengths.
The library proves the two facts the paper recalls: the $s\_{\[\lambda\]}$ form a
basis of $\Lambda\_R$ over every commutative ring, and the top homogeneous
component of $s\_{\[\lambda\]}$ is $s\_\lambda$.

These declarations are in `ComplementaryProducts`
([UniversalProducts.lean](KlebersConjecture/Paper/UniversalProducts.lean))
and in the symmetric-function library
([SymplecticCharacters/](KlebersConjecture/SymmetricFunctions/SymplecticCharacters)).

| Declaration | Result |
| --- | --- |
| `symplectic_linearIndependent` | All of Corollary 1.3 |
| `symplectic_linearIndependent_tensor` | Corollary 1.3 in $\mathbb{F} \otimes\_{\mathbb{Z}} \Lambda\_{\mathbb{Z}}$ |
| `SymmetricFunction.symplecticCharacter_eq_det` | The determinant formula |
| `SymmetricFunction.symplecticCharacterBasis` | The $s\_{\[\lambda\]}$ form a basis |
| `SymmetricFunction.homogeneousComponent_symplecticCharacter`, `SymmetricFunction.symplecticCharacter_sub_schur_mem` | $s\_{\[\lambda\]}-s\_\lambda \in F\_{\le \lvert\lambda\rvert-1}\Lambda\_R$ |

### Theorem 1.4: monomial products

Let $\mathbb{F}$ be a field of characteristic zero. For every rectangle
$(b^a)$, the products

$$
m\_\lambda m\_{\lambda^\vee}, \qquad \lambda \subseteq (b^a),
$$

indexed by unordered complementary pairs, are linearly independent in
$\Lambda\_{\mathbb{F}}$. The same products are $\mathbb{Z}$-linearly independent
in $\Lambda\_{\mathbb{Z}}$.

The two parts are two theorems; as in Theorem 1.1, the rectangle has positive
side lengths. The proof follows the paper: it expands $m\_\alpha$ in the
power-sum generators, with the leading coefficient computed by Möbius inversion
in the lattice of set partitions (Lemma 5.2). The integral statement follows
from the rational one, since $\Lambda\_{\mathbb{Z}} \to \Lambda\_{\mathbb{Q}}$ is
injective. Remark 5.8 is formalized over every commutative ring of
characteristic two: there $m\_{(1)}^2=m\_{(2)}+2m\_{(1,1)}=m\_{(2)}$, so the two
complementary products for the row $(2)$ coincide.

These declarations are in `ComplementaryProducts`
([MonomialIndependence.lean](KlebersConjecture/Paper/MonomialIndependence.lean),
[CharacteristicTwo.lean](KlebersConjecture/Paper/CharacteristicTwo.lean))
and in the general libraries.

| Declaration | Result |
| --- | --- |
| `monomial_linearIndependent` | Theorem 1.4 over a field of characteristic zero |
| `monomial_linearIndependent_int` | Theorem 1.4 over $\mathbb{Z}$ |
| `monomial_linearIndependent_tensor`, `monomial_linearIndependent_int_tensor` | Both parts in $R \otimes\_{\mathbb{Z}} \Lambda\_{\mathbb{Z}}$ |
| `SymmetricFunction.monomial_eq_smul_powerSum_add` | Lemma 5.2: $m\_\alpha=\kappa\_\alpha p\_d+Q\_\alpha$ with $\kappa\_\alpha \ne 0$ and $Q\_\alpha \in \mathbb{F}\[p\_1,\ldots,p\_{d-1}\]$ |
| `Finpartition.mu_bot_top` | The Möbius function of the set-partition lattice: $\mu(\hat0,\hat1)=(-1)^{k-1}(k-1)!$ |
| `monomial_singleRow_one_sq_eq_add` | $m\_{(1)}^2=m\_{(2)}+2m\_{(1,1)}$ over every commutative ring |
| `not_monomial_linearIndependent_charP_two` | Remark 5.8: the products are dependent over every commutative ring of characteristic two |

### Every other statement

The remaining lemmas, corollaries, definitions, examples, displayed equations
and the remark of the paper, and the standard results it cites, are listed with
their Lean declarations in [docs/STATEMENTS.md](docs/STATEMENTS.md).

## Libraries

The Lean library `KlebersConjecture` is divided into four parts. The first three are
general and do not import the fourth, which contains the paper.

### The Partitions library

[KlebersConjecture/Partitions/](KlebersConjecture/Partitions) (namespace `YoungDiagram`, 14
files) extends Mathlib's Young diagrams, which represent partitions:
componentwise addition of row lengths, deletion of rows and of the first row
and column, rectangles and rectangular complements, finite sets of diagrams of
bounded size, and skew diagrams with their fillings, reading words, lattice
words and Littlewood–Richardson tableaux.

| Declaration | Result |
| --- | --- |
| `YoungDiagram.rectComplement`, `YoungDiagram.rectComplement_rectComplement` | The complement $\lambda^\vee$ in $(b^a)$ is an involution |
| `YoungDiagram.card_add_rectComplement` | $\lvert\lambda\rvert+\lvert\lambda^\vee\rvert=ab$ |
| `YoungDiagram.dropRows`, `YoungDiagram.removeFirstRowCol` | $\lambda^{\downarrow r}$, and $\partial\tau$: the diagram without its first row and column |
| `YoungDiagram.LRTableau` | Littlewood–Richardson tableaux of shape $\nu/\alpha$ and content $\beta$ |

### The SetPartitions library

[KlebersConjecture/SetPartitions/](KlebersConjecture/SetPartitions) (namespace `Finpartition`,
7 files) studies the lattice of set partitions of a finite set, ordered by
refinement, through the equality patterns of maps: counting maps by their
kernels and Möbius inversion in the lattice.

| Declaration | Result |
| --- | --- |
| `Finpartition.mu_bot_top` | $\mu(\hat0,\hat1)=(-1)^{k-1}(k-1)!$ for the set partitions of $\lbrace1,\ldots,k\rbrace$ |
| `Finpartition.mu_bot_top_fintype` | The same for the set partitions of any finite type |

### The SymmetricFunctions library

[KlebersConjecture/SymmetricFunctions/](KlebersConjecture/SymmetricFunctions) (namespace
`SymmetricFunction`, 88 files) develops the ring $\Lambda\_R$ of symmetric
functions over any commutative semiring, as bounded-degree symmetric power
series: the grading, restriction to finitely many variables, change of
coefficient ring and $\Lambda\_R \cong R \otimes\_{\mathbb{Z}} \Lambda\_{\mathbb{Z}}$;
the monomial, elementary, complete, power-sum and Schur functions and their
bases; the presentations by the elementary and the complete functions and, over
$\mathbb{Q}$-algebras, by the power sums; the involution $\omega$; the
Jacobi–Trudi identity; derivations and coefficient extraction with respect to
the complete generators; Littlewood–Richardson coefficients, by alternants and
by skew tableaux, and row removal; first-row projections; and the symplectic
universal characters.

| Declaration | Result |
| --- | --- |
| `SymmetricFunction.schurBasis`, `SymmetricFunction.monomialBasis`, `SymmetricFunction.completeBasis`, `SymmetricFunction.elementaryBasis` | Bases of $\Lambda\_R$ over every commutative ring |
| `SymmetricFunction.powerSumBasis` | The power-sum basis over a $\mathbb{Q}$-algebra |
| `SymmetricFunction.completePresentation`, `SymmetricFunction.elementaryPresentation`, `SymmetricFunction.powerSumPresentation` | $\Lambda\_R=R\[h\_1,h\_2,\ldots\]=R\[e\_1,e\_2,\ldots\]$, and $=R\[p\_1,p\_2,\ldots\]$ over a $\mathbb{Q}$-algebra |
| `SymmetricFunction.baseChangeEquiv` | $R \otimes\_{\mathbb{Z}} \Lambda\_{\mathbb{Z}} \cong \Lambda\_R$ |
| `SymmetricFunction.omega` | The involution $\omega$ with $\omega(e\_r)=h\_r$ |
| `SymmetricFunction.schur_eq_det_jacobiTrudiMatrix` | Jacobi–Trudi: $s\_\lambda=\det(h\_{\lambda\_i-i+j})\_{1 \le i,j \le r}$ for $r \ge \ell(\lambda)$ |
| `SymmetricFunction.schurBasis_repr_schur_mul_schur` | $s\_\alpha s\_\beta=\sum\_\nu c^\nu\_{\alpha,\beta}s\_\nu$ |
| `SymmetricFunction.lrCoeff_eq_card_lrTableaux` | The Littlewood–Richardson rule in skew-tableau form |
| `SymmetricFunction.rowLen_zero_le_of_lrCoeff_ne_zero`, `SymmetricFunction.lrCoeff_eq_lrCoeff_dropRows` | Lemma 2.2: first-row bound and row removal |
| `SymmetricFunction.symplecticCharacterBasis` | The symplectic universal characters form a basis |

Each of the three general libraries is at version 0.1.0 and imports only
Mathlib, Tau Ceti and the libraries before it.
[LIBRARY_MANIFEST.json](LIBRARY_MANIFEST.json) records their folders and the
SHA-256 hash of every file.

### The paper

[KlebersConjecture/Paper/](KlebersConjecture/Paper) (namespace
`ComplementaryProducts`, 20 files) contains every result of the paper, as
described above: the splitting and complementary-pair families, the oriented
families of Section 3, the gap vectors and fixed-gap projections of Section 4,
the monomial argument of Section 5, and the statements in
$R \otimes\_{\mathbb{Z}} \Lambda\_{\mathbb{Z}}$.

## Build and verify

Install [Lean and Lake through elan](https://lean-lang.org/install/) and
[Python 3](https://www.python.org/downloads/). Git must also be available.
The `lean-toolchain` file selects Lean 4.35.0-rc3 automatically, and
`lake-manifest.json` pins Mathlib, Tau Ceti and their public dependencies.

From the repository directory, run:

```text
lake exe cache get
python build.py --jobs 3
lake env lean KlebersConjecture/Paper/Audit.lean
```

On Windows, `py -3` can replace `python`; a short project path is recommended.
The first setup requires internet access and space for Lean and Mathlib.
The first command downloads public dependency caches. The Python helper first
has Lake build the Tau Ceti modules used here, then recompiles all
**129 local Lean modules** in dependency order, and exits with a
nonzero status if a module fails. With three jobs the full build takes about
12 minutes on a laptop.

To resume an interrupted build, or to check that every module was compiled
from the current sources:

```text
python build.py --jobs 3 --resume
python build.py --check
```

A standard `lake build` target is also configured.

The audit prints the transitive axiom dependencies of every theorem listed in
[docs/STATEMENTS.md](docs/STATEMENTS.md). The expected axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.

Recorded checks:

- [provenance/BUILD_CHECK.json](provenance/BUILD_CHECK.json)
- [provenance/ENDPOINT_AUDIT.txt](provenance/ENDPOINT_AUDIT.txt)

To check the distributed snapshot's hashes and the local import completeness:

```text
python verify_bundle.py
```

`SHA256SUMS.json` describes this release snapshot. Intentional edits require
updating the hash inventory before that integrity check can pass again.

## Source layout

- `KlebersConjecture/Partitions/`, `KlebersConjecture/SetPartitions/`,
  `KlebersConjecture/SymmetricFunctions/`: the general libraries described above, each
  with an entry point `Main.lean`. Files in a `ForMathlib/` folder contain
  general facts about polynomials and determinants, stated in Mathlib's
  namespaces.
- `KlebersConjecture/Paper/`: the paper. `Indices` and `Products` define
  the index sets and product families; `Oriented*`, `SplittingDerivative`,
  `MaximalSelfPair` and `SplittingIndependence` prove Theorem 1.2 (Section 3);
  `Gap*` and `RectangularIndependence` prove Theorem 1.1 (Section 4);
  `UniversalProducts` proves Corollary 1.3; `MonomialIndependence` and
  `CharacteristicTwo` prove Theorem 1.4 and Remark 5.8 (Section 5);
  `Tensor*` give the statements in $R \otimes\_{\mathbb{Z}} \Lambda\_{\mathbb{Z}}$;
  `Examples` works Examples 4.2 and 5.1.
- `KlebersConjecture/Paper/Main.lean`: imports every result of the paper.
- `KlebersConjecture/Paper/Audit.lean`: the audit described above.
- `LIBRARY_MANIFEST.json`: the version, folders and file hashes of the general
  libraries.
- `docs/STATEMENTS.md`: the statements of the paper and their Lean
  counterparts.
- `provenance/`: source inventory and verification records.

## Attribution and licensing

This repository is licensed under the [Apache License 2.0](LICENSE).
Redistributions must retain the [NOTICE](NOTICE) file. If you use or adapt
this code, please cite this repository; citation metadata is in
[CITATION.cff](CITATION.cff). The repository contains no third-party source
files; Mathlib, Tau Ceti and their dependencies are downloaded by Lake and keep
their own licenses (see [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md)).
