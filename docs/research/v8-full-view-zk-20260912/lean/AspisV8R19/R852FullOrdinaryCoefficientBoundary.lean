import AspisV8R19.R851FullOrdinaryMoment
import AspisV8R19.R653SourceCoefficientBoundary
import AspisV8R19.R665FullSourceP2Boundary

set_option autoImplicit false

namespace AspisV8R19.R852FullOrdinaryCoefficientBoundary

open AspisV8R19.R738JointObservationModel
open AspisV8R17 AspisR19
open scoped BigOperators

variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- The full indexed ordinary c0+c4 boundary is the ordinary source moment;
the four-coordinate top tail remains an explicit premise. -/
theorem ordinary_coefficient_boundary_of_top_zero
    (half quarter a b c kappa tau : F) (z : Fin 10 → F)
    (q : Index256 → F)
    (hTop : ∀ r : Nat, 1020 ≤ r → rawFlatten q r = 0) :
    rawRelation half quarter a b c kappa tau z q 0 +
        rawRelation half quarter a b c kappa tau z q 4 =
      quarter * (
        kappa * sourcePointFunctional (SourceStatementPoints.points z 0)
          (rawMask half a b c q) +
        kappa^2 * sourcePointFunctional (SourceStatementPoints.points z 1)
          (rawMask half a b c q) +
        kappa^3 * sourcePointFunctional (SourceStatementPoints.points z 2)
          (rawMask half a b c q)) := by
  unfold rawRelation
  rw [AspisV8R19.R653SourceCoefficientBoundary.coefficient_boundary 256 quarter q
    (fun i => rawOrdinaryWeight half a b c kappa tau z
      (4 * i.1.val + i.2.val))]
  have hpair := AspisV8R19.R665FullSourceP2Boundary.full_flatten_pairing q
    (rawOrdinaryWeight half a b c kappa tau z)
  rw [← hpair]
  rw [← rawFlatten_eq_flattenFull q]
  rw [AspisV8R19.R851FullOrdinaryMoment.ordinary_moment_of_top_zero
    half a b c kappa tau z q hTop]

#print axioms ordinary_coefficient_boundary_of_top_zero

end AspisV8R19.R852FullOrdinaryCoefficientBoundary
