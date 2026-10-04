import AspisV8R19.R683QueryCoreCoinImage
import AspisV8R19.R665FullSourceP2Boundary
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R684FullSourceMomentIdentity
open AspisR19 AspisV8R17 HighRepairInvariant
open R660FullSourceResidualCorrection R662FullIndexedMaskPreservation
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2:F)]

theorem full_source_moment_identity (half quarter a b c kappa tau : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (structured : Bool) (q : Index 256 → F) :
    fullRelation half quarter a b c kappa tau z previous structured q 0 +
      fullRelation half quarter a b c kappa tau z previous structured q 4 =
      quarter * ((kappa * (if structured then
        ∑ r : Fin 1024, TwoSwapSourceG.original (SourceGConstant.finishCoins half previous) r * indexedMask half a b c q r
        else sourcePointFunctional (SourceStatementPoints.points z 0) (indexedMask half a b c q)) +
        kappa^2*sourcePointFunctional (SourceStatementPoints.points z 1) (indexedMask half a b c q) +
        kappa^3*sourcePointFunctional (SourceStatementPoints.points z 2) (indexedMask half a b c q) +
        ∑ r ∈ TwoSwapSourceTable.inactive, indexedMask half a b c q r) +
        (if structured then tau^3 else tau)*flattenFull q 1023 +
        (if structured then tau^4 else tau^2)*(b*flattenFull q 1022-c*flattenFull q 1021)) := by
  rw [R653SourceCoefficientBoundary.coefficient_boundary]
  simp only [full_flatten_pairing]
  unfold fullWeight
  -- The remaining equality is the selected generic transported pairing.
  sorry
#print axioms full_source_moment_identity
end
end AspisV8R19.R684FullSourceMomentIdentity
