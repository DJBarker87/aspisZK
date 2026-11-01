import R1Z.PV_RunJoin_FoldedWordSize64
import R1Z.PV_RunJoin_FinishFrame63
import R1Z.PV_RunJoin_NativeActual63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeWordContext66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world)
    (p : prover.Publication)
    (context : @PV_RunJoin_PublishContext57.QueryContext (types base) (opsNative base heap box ops runtime world)
      (@PV_RunJoin_ActualRun.runs (types base) (opsNative base heap box ops runtime world) phase.val) p) :
    262144≤(alloc.vec.Vec.deref p.folded_word).length := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨prepared,salts,hp,hs,hf⟩ := context
  obtain ⟨hbackend,hsem,hy,hi,hc,hword,hstored⟩ :=
    PV_RunJoin_FinishFrame63.complete .S2 phase.val.hash prepared salts p hf
  obtain ⟨leaves,o,tree,root,second,cbytes,payload0,payload,alpha,next,final,fbytes,queries,tr,
    hleaves,htree,ho,hroot,hsecond,hcbytes,hpayload0,hpayload,hscalar,hfinal,hfbytes,hqueries,hpublication⟩ :=
      PV_RJQ_FinishTrace.source .S2 phase.val.hash prepared salts p hf
  rw [hword]
  exact PV_RunJoin_FoldedWordSize64.complete phase.val.hash
    (alloc.vec.Vec.deref prepared.folded_word) salts leaves hleaves

#print axioms complete
end R1Z.PV_RunJoin_NativeWordContext66
