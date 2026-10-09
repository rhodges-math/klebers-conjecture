import KlebersConjecture.Partitions.Main
import KlebersConjecture.SetPartitions.Main
import KlebersConjecture.SymmetricFunctions.Main
import KlebersConjecture.Paper.Indices
import KlebersConjecture.Paper.Products
import KlebersConjecture.Paper.Gap
import KlebersConjecture.Paper.GapTails
import KlebersConjecture.Paper.Oriented
import KlebersConjecture.Paper.OrientedIndependence
import KlebersConjecture.Paper.SplittingDerivative
import KlebersConjecture.Paper.SplittingIndependence
import KlebersConjecture.Paper.GapProjection
import KlebersConjecture.Paper.GapBlocks
import KlebersConjecture.Paper.RectangularIndependence
import KlebersConjecture.Paper.MaximalSelfPair
import KlebersConjecture.Paper.UniversalProducts
import KlebersConjecture.Paper.MonomialIndependence
import KlebersConjecture.Paper.CharacteristicTwo
import KlebersConjecture.Paper.TensorProducts
import KlebersConjecture.Paper.TensorIndependence
import KlebersConjecture.Paper.Examples

/-! # Complementary products

Products indexed by componentwise splittings and rectangular complementary pairs.

## Main results

* `splitting_linearIndependent` gives Schur independence for componentwise splittings.
* `kleber_linearIndependent` gives Schur independence for rectangular complements.
* `symplectic_linearIndependent` gives symplectic character independence over every field.
* `monomial_linearIndependent` gives monomial independence over characteristic-zero fields.
* `monomial_linearIndependent_int` gives the integral monomial result.

The corresponding `_tensor` theorems state the results in literal tensor scalar extension.
-/
