import Wide.FactorBudgets
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
#check @coeff_equivMvPolynomial
end
end AspisWide.FactorBudgets
