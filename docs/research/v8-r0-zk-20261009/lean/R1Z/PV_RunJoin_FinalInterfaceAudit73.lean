import R1Z.PV_RunJoin_FinalBridgeAudit73
import R1Z.PV_RunJoin_FinalFrontierAudit73
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FinalInterfaceAudit73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

/-- A concrete residual dictionary witnesses the obstruction even for an
arbitrary supplied terminal. No deployed dictionary or reference is changed. -/
theorem witness {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (terminal : @PV_RunJoin_OracleBridge38.Terminal (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    ∃ candidate : @ExternalFuns (types base),
      @ExternalFuns.op227 (types base) (opsNative base heap box candidate runtime world)=terminal ∧
      ¬Nonempty (PV_RunJoin_NativeActual63.P base heap box candidate runtime world) :=
  ⟨PV_RunJoin_BridgeObstruction73.diagnostic base ops terminal,
    PV_RunJoin_BridgeObstruction73.callback base heap box ops terminal runtime world,
    PV_RunJoin_BridgeObstruction73.no_capture base heap box ops terminal runtime world⟩

-- Summary-based axiom lists, not a raw walk (ax1).
#print axioms witness
#print axioms PV_RunJoin_NativeWorkerRound73.complete
#print axioms PV_RunJoin_ExactBridgeObstruction73.complete
end R1Z.PV_RunJoin_FinalInterfaceAudit73
