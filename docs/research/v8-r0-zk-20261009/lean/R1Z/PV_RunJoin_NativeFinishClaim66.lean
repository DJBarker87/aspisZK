import R1Z.PV_RunJoin_NativeClaimDomain66
import R1Z.PV_RunJoin_FinishClaim63
import R1Z.PV_RunJoin_FinishFrame63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeFinishClaim66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_RunJoin_PublishSkeleton54

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world)
    (p : prover.Publication)
    (context : @PV_RunJoin_PublishContext57.QueryContext (types base) (opsNative base heap box ops runtime world)
      (@PV_RunJoin_ActualRun.runs (types base) (opsNative base heap box ops runtime world) phase.val) p) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∀ out : alloc.vec.Vec U8, out.length+(PV_RunJoin_ActualRun.plans phase.val).claim.length≤Usize.max →
      ∃ next, host_compact.compact_values (alloc.vec.Vec.deref p.y1) out=ok (.Ok (),next) ∧
        bytes next.val=bytes out.val++(PV_RunJoin_ActualRun.plans phase.val).claim := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have retained := context
  obtain ⟨prepared,salts,hp,hs,hf⟩ := context
  obtain ⟨length,high⟩ := PV_RunJoin_NativeClaimDomain66.complete base heap box ops runtime world phase prepared hp
  have frame := (PV_RunJoin_FinishFrame63.complete .S2 phase.val.hash prepared salts p hf).2.2.1
  apply PV_RunJoin_FinishClaim63.complete phase.val p retained 29
  · rw [frame];exact length
  · rw [frame];exact high

#print axioms complete
end R1Z.PV_RunJoin_NativeFinishClaim66
