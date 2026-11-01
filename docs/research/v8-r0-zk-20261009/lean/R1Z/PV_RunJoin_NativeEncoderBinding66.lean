import R1Z.PV_RunJoin_NativeResidual63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeEncoderBinding66
open ProverRwFull PV_RunJoin_NativeResidual63

theorem residual {S F : Type} (base : ExternalTypes) (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    @PV_DL_EncoderSelected.selected (types base)
        (PV_RunJoin_NativeResidual63.residual base ops runtime world)=
      PV_RunJoin_NativeResidual63.residual base ops runtime world := by
  rfl

#print axioms residual
end R1Z.PV_RunJoin_NativeEncoderBinding66
