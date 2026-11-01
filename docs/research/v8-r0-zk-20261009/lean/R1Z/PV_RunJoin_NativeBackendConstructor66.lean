import R1Z.PV_RunJoin_BackendConstructor66
import R1Z.PV_RunJoin_NativeCommitmentQuery64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeBackendConstructor66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (c : host_commitment.Commitment)
    (built : @PV_RunJoin_BackendConstructor66.Built (types base)
      (opsNative base heap box ops runtime world) c) :
    PV_RunJoin_QueryFillStep64.Domain c ∧
      ∃ s, c.private_salts=some s ∧ 262144≤s.length := by
  obtain ⟨hash,domain,time,messages,variant,salts,success⟩ := built
  exact PV_RunJoin_NativeCommitmentQuery64.complete base heap box ops runtime world
    hash domain time messages variant salts c success

#print axioms complete
end R1Z.PV_RunJoin_NativeBackendConstructor66
