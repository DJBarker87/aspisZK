import AspisR1RhoInit.Types
import CuSavingsRhoZipInitialization
import AspisR1PublicPreparation.Funs

/-! The loop helper is the checked original-runtime zip/assignment composition.
Only the unchanged generic heap API remains an explicit allocation boundary.
No generated axiom template is imported. -/
set_option autoImplicit false
namespace AspisR1CuRho
open Aeneas Aeneas.Std Result

class InitAllocation where
  filled : {T : Type} → core.marker.Copy T → Usize → T →
    Result (core.result.Result (alloc.vec.Vec T) r0.Error)

abbrev r0.heap.filled [InitAllocation] := @InitAllocation.filled _
abbrev core.result.Result.map_err := @AspisR1PublicPreparation.core.result.Result.map_err
def verifier.initialize_weights
    (raw : alloc.vec.Vec (Array U64 4#usize)) (weights : Slice field.QM31) :
    Result (alloc.vec.Vec (Array U64 4#usize)) :=
  AspisR1.CuSavingsRhoZipInitialization.initializeRows raw weights

#print axioms InitAllocation
#print axioms verifier.initialize_weights
end AspisR1CuRho
