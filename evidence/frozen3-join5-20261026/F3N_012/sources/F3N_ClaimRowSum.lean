import F3N_OrderedSum
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_ClaimRowSum
open Aeneas Aeneas.Std
open AspisR1CurrentPreparedClaim.Concrete
open scoped BigOperators
attribute [local irreducible] HAdd.hAdd HMul.hMul HPow.hPow Finset.sum decode

theorem row (gamma : E) (xs : List (Usize × E × AspisR1CurrentPreparedClaim.aspis_core.field.QM31))
    (length : xs.length=29)
    (ordered : ∀ j (hj : j<xs.length),(xs[j]'hj).1.val=j)
    (Y : Fin 29 → AspisWideTower.WideExact)
    (values : ∀ j : Fin 29,
      AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed (xs[j.val]'(by omega)).2.2=Y j) :
    (xs.map (fun t=>decode gamma^t.1.val *
      AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed t.2.2)).sum=
      ∑ j : Fin 29,decode gamma^j.val*Y j := by
  rw [F3N_OrderedSum.sum 29 xs length]
  apply Finset.sum_congr rfl
  intro j _
  rw [ordered j.val (by omega),values j]

#print axioms row
end AspisR1.F3N_ClaimRowSum
end
