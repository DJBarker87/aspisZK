import R1Z.PV_RunJoin_NativeBackendBounds66
import R1Z.PV_RunJoin_PrepareFrame66
import R1Z.PV_RunJoin_NativeWordContext66
import R1Z.PV_RunJoin_NativeSaltContext64
import R1Z.PV_RunJoin_QueryLoopTotal64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeQueryDomain66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world)
    (p : prover.Publication) (cc1 cc2 : host_commitment.Commitment)
    (hc1 : p.backend.c1=some cc1) (hc2 : p.backend.c2=some cc2)
    (context : @PV_RunJoin_PublishContext57.QueryContext (types base) (opsNative base heap box ops runtime world)
      (@PV_RunJoin_ActualRun.runs (types base) (opsNative base heap box ops runtime world) phase.val) p) :
    PV_RunJoin_QueryLoopTotal64.Domain cc1 cc2 (alloc.vec.Vec.deref p.folded_word) p.folded_salts := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨prepared,salts,hp,hs,hf⟩ := context
  have prepareFrame := PV_RunJoin_PrepareFrame66.complete .S2 phase.val.hash phase.val.backend phase.val.sem prepared hp
  have finishFrame := (PV_RunJoin_FinishFrame63.complete .S2 phase.val.hash prepared salts p hf).1
  have frame : p.backend=phase.val.backend := finishFrame.trans prepareFrame
  obtain ⟨c1,c2,h1,h2,words1,words2,salts1,salts2⟩ :=
    PV_RunJoin_NativeBackendBounds66.complete base heap box ops runtime world phase
  have same1 : c1=cc1 := Option.some.inj (h1.symm.trans (frame ▸ hc1))
  have same2 : c2=cc2 := Option.some.inj (h2.symm.trans (frame ▸ hc2))
  subst c1
  subst c2
  have wordSize := PV_RunJoin_NativeWordContext66.complete base heap box ops runtime world phase p context
  have saltSize := PV_RunJoin_NativeSaltContext64.complete base heap box ops runtime world phase p context
  exact ⟨words1,words2,salts1,salts2,wordSize,by omega⟩

#print axioms complete
end R1Z.PV_RunJoin_NativeQueryDomain66
