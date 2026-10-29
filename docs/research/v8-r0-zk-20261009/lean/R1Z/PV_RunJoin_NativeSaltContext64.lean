import R1Z.PV_RunJoin_NativeSaltSize64
import R1Z.PV_RunJoin_FinishFrame63
import R1Z.PV_RunJoin_NativeActual63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeSaltContext64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world)
    (p : prover.Publication)
    (context : @PV_RunJoin_PublishContext57.QueryContext (types base) (opsNative base heap box ops runtime world)
      (@PV_RunJoin_ActualRun.runs (types base) (opsNative base heap box ops runtime world) phase.val) p) :
    p.folded_salts.length=262144 := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨prepared,salts,hp,hs,hf⟩ := context
  obtain ⟨hbackend,hsem,hy,hi,hc,hword,hstored⟩ :=
    PV_RunJoin_FinishFrame63.complete .S2 phase.val.hash prepared salts p hf
  rw [hstored]
  exact PV_RunJoin_NativeSaltSize64.complete base heap box ops runtime world
    phase.val.salts.1 phase.val.salts.2 phase.val.hash 114#u8 salts hs

#print axioms complete
end R1Z.PV_RunJoin_NativeSaltContext64
