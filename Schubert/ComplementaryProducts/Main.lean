import Schubert.Partitions.Main
import Schubert.SetPartitions.Main
import Schubert.SymmetricFunctions.Main
import Schubert.ComplementaryProducts.Indices
import Schubert.ComplementaryProducts.Products
import Schubert.ComplementaryProducts.Gap
import Schubert.ComplementaryProducts.GapTails
import Schubert.ComplementaryProducts.Oriented
import Schubert.ComplementaryProducts.OrientedIndependence
import Schubert.ComplementaryProducts.SplittingDerivative
import Schubert.ComplementaryProducts.SplittingIndependence
import Schubert.ComplementaryProducts.GapProjection
import Schubert.ComplementaryProducts.GapBlocks
import Schubert.ComplementaryProducts.RectangularIndependence
import Schubert.ComplementaryProducts.MaximalSelfPair
import Schubert.ComplementaryProducts.UniversalProducts
import Schubert.ComplementaryProducts.MonomialIndependence
import Schubert.ComplementaryProducts.CharacteristicTwo
import Schubert.ComplementaryProducts.TensorProducts
import Schubert.ComplementaryProducts.TensorIndependence
import Schubert.ComplementaryProducts.Examples

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
