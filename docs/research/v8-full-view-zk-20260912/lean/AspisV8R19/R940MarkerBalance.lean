import AspisV8R19.R896OrdinarySourceTailBoundary

/-! Marker transpose pairing and its exact ordinary-boundary consequence.

The second theorem retains precisely the
source-image conditions supplied in its arguments; it does not replace them by
coordinatewise tail zero assumptions.
-/
set_option autoImplicit false
namespace AspisV8R19.R940MarkerBalance

open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R788OrdinaryPointDecomposition
open AspisV8R19.R793MarkerTranspose
open AspisV8R19.R896OrdinarySourceTailBoundary
open scoped BigOperators
noncomputable section

variable {F : Type*}
section Ring
variable [CommRing F]

/-- The raw ordinary marker contraction is exactly the selected inactive-mask
balance. -/
theorem marker_pairing_eq_inactive_balance
    (half a b c : F) (q : Index256 → F) :
    rangeDot 1024 (sourceChordTranspose half marker a b c) (rawFlatten q) =
      ∑ n ∈ TwoSwapSourceTable.inactive, rawMask half a b c q n := by
  have htranspose := source_chord_transpose_pairing half (rawFlatten q) marker a b c
  have hmarker :
      rangeDot 1024 marker (sourceChord half (rawFlatten q) a b c) =
        sourceChord half (rawFlatten q) a b c 1023 := by
    rw [marker_eq_unit, rangeDot_comm]
    exact rangeDot_unitVector 1024 1023 (by decide) _
  have htransport := congrFun
    (transport_inverse TwoSwapSourceTable.inactive 1023
      R788OrdinaryPointDecomposition.pivot_mem_inactive TwoSwapSourceTable.order
      (fun j : Fin 1024 => sourceChord half (rawFlatten q) a b c j.val))
    (1023 : Fin 1024)
  change transport TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
      (rawMask half a b c q) 1023 =
        sourceChord half (rawFlatten q) a b c 1023 at htransport
  rw [transport, order_1023, if_pos rfl] at htransport
  calc
    rangeDot 1024 (sourceChordTranspose half marker a b c) (rawFlatten q) =
        rangeDot 1024 marker (sourceChord half (rawFlatten q) a b c) := htranspose.symm
    _ = sourceChord half (rawFlatten q) a b c 1023 := hmarker
    _ = ∑ n ∈ TwoSwapSourceTable.inactive, rawMask half a b c q n := htransport.symm

end Ring

section FieldBoundary
variable [Field F] [NeZero (2 : F)]

/-- The ordinary `c0+c4` boundary under the exact source image conditions and
selected inactive balance.  In particular, no hypothesis sets coordinates
1020, 1021, or 1022 individually to zero. -/
theorem ordinary_boundary_of_balance_and_image_tails
    (half quarter a b c kappa tau : F) (z : Fin 10 → F) (q : Index256 → F)
    (h23 : rawFlatten q 1023 = 0)
    (himage : b * rawFlatten q 1022 - c * rawFlatten q 1021 = 0)
    (hbalance : ∑ n ∈ TwoSwapSourceTable.inactive, rawMask half a b c q n = 0) :
    rawRelation half quarter a b c kappa tau z q 0 +
        rawRelation half quarter a b c kappa tau z q 4 =
      quarter *
        (kappa * sourcePointFunctional (SourceStatementPoints.points z 0) (rawMask half a b c q) +
          kappa^2 * sourcePointFunctional (SourceStatementPoints.points z 1) (rawMask half a b c q) +
          kappa^3 * sourcePointFunctional (SourceStatementPoints.points z 2) (rawMask half a b c q)) := by
  rw [ordinary_source_boundary_of_image_tails half quarter a b c kappa tau z q h23 himage,
    marker_pairing_eq_inactive_balance half a b c q, hbalance]
  ring

#print axioms marker_pairing_eq_inactive_balance
#print axioms ordinary_boundary_of_balance_and_image_tails

end FieldBoundary
end
end AspisV8R19.R940MarkerBalance
