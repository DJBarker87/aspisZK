import R1Z.PV_RunJoin_NativeSemanticDomain66
import R1Z.PV_RunJoin_SemanticAppend66
import R1Z.PV_RunJoin_PrepareTailSuccess48
import R1Z.PV_RunJoin_PrepareTailReach49
import R1Z.PV_RunJoin_ActualPlanProjection60
import R1Z.PV_RunJoin_FinishFrame63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeFinishSemantic66
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
    ∀ out : alloc.vec.Vec U8, out.length+(PV_RunJoin_ActualRun.plans phase.val).semantic.length≤Usize.max →
      ∃ next, host_compact.compact_semantic (alloc.vec.Vec.deref p.semantic_bytes) out=ok (.Ok (),next) ∧
        bytes next.val=bytes out.val++(PV_RunJoin_ActualRun.plans phase.val).semantic := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have retained := context
  obtain ⟨prepared,salts,hp,hs,hf⟩ := context
  obtain ⟨length,records,domain⟩ := PV_RunJoin_NativeSemanticDomain66.complete base heap box ops runtime world phase
  have fixed := PV_RunJoin_WeightAbsorb66.complete (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base ops runtime world)
  obtain ⟨encoded,he,append⟩ := PV_RunJoin_SemanticAppend66.complete
    (opsNative base heap box ops runtime world) fixed (alloc.vec.Vec.deref phase.val.sem.bytes) records length domain
  obtain ⟨tr0,tr1,tr2,claim,gamma,inactive,kappa,ib,q,w,hg,hk,htail⟩ :=
    PV_RunJoin_PrepareTailReach49.complete (PV_RunJoin_NativeResidual62.baseTypes base)
      heap box (residual base ops runtime world) .S2 phase.val.hash phase.val.backend phase.val.sem prepared hp
  obtain ⟨c0,cbytes,a,tr,q1,w1,folded,hr,hb,ha,hq,hw,hd,fields⟩ :=
    PV_RunJoin_PrepareTailSuccess48.complete (PV_RunJoin_NativeResidual62.baseTypes base)
      heap box (residual base ops runtime world) .S2 phase.val.hash phase.val.backend phase.val.sem
      tr2 claim gamma inactive kappa (alloc.vec.Vec.deref q) (alloc.vec.Vec.deref w) prepared htail
  have semantic : p.semantic_bytes=phase.val.sem.bytes :=
    (PV_RunJoin_FinishFrame63.complete .S2 phase.val.hash prepared salts p hf).2.1.trans
      (congrArg (fun sem => sem.bytes) fields.2.1)
  have he' : host_compact.compact_semantic (alloc.vec.Vec.deref p.semantic_bytes)
      PV_RunJoin_ActualPlanSources59.empty=ok (.Ok (),encoded) := by rw [semantic];exact he
  have plan := PV_RunJoin_ActualPlanProjection60.semantic phase.val p encoded retained he'
  intro out room
  rw [plan] at room
  obtain ⟨next,hn,hbytes⟩ := append out room
  refine ⟨next,?_,?_⟩
  · rw [semantic];exact hn
  · rw [plan];exact hbytes
#print axioms complete
end R1Z.PV_RunJoin_NativeFinishSemantic66
