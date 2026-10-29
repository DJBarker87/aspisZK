import R1Z.PV_RunJoin_NativeActual63
import R1Z.PV_RunJoin_NativeFrontRoom62
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeBinding63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

def remaining {S F : Type} (base : ExternalTypes) (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) : @ExternalFuns (types base) :=
  @PV_RunJoin_AllocatorWorld63.selectedAt (types base) S F runtime
    (@PV_FXM_DropSelected.selected (types base) (PV_B3P_Install132.selected (types base) ops)) world

theorem residual {S F : Type} (base : ExternalTypes) (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    PV_RunJoin_NativeResidual63.residual base ops runtime world=
      PV_RunJoin_NativeResidual62.residual base (remaining base ops runtime world) := by
  rfl

theorem native {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    opsNative base heap box ops runtime world=
      PV_RunJoin_NativeResidual62.opsNative base heap box (remaining base ops runtime world) := by
  unfold opsNative PV_RunJoin_NativeResidual62.opsNative
  rw [residual]

#print axioms remaining
#print axioms residual
#print axioms native
end R1Z.PV_RunJoin_NativeBinding63
