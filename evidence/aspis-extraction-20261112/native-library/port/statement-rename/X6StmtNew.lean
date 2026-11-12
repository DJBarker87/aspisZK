import Wide.RegularWeights
import Wide.Smooth
import Wide.HenselCombinatorics
import AspisFormal.V6PublishedTheoremInterfaces
set_option autoImplicit false
namespace AspisWide.FactorBudgets
open Polynomial
open scoped Polynomial.Bivariate
open AspisWide.Interpolation
open AspisWide.Factors
open AspisWide.Smooth
open AspisWide.LocalFactors
open AspisWide.RegularWeights
open AspisWide.HenselCombinatorics
open AspisV6PublishedTheoremInterfaces
noncomputable section
universe u
set_option pp.all true
set_option format.width 100000
#check (∀ {R : Type u} [CommRing R] (polynomial : BivariatePolynomial R) (inner outer : Nat),
    (Polynomial.Bivariate.equivMvPolynomial R polynomial).coeff
        (Finsupp.single (0 : Fin 2) inner +
          Finsupp.single (1 : Fin 2) outer) =
      (polynomial.coeff outer).coeff inner)
end
end AspisWide.FactorBudgets
