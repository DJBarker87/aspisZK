import R1Z.PV_RunJoin_ActualPublication60
import R1Z.PV_RunJoin_CloneBytes43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualPlanProjection60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_PublishSkeleton54
variable [ExternalTypes] [ExternalFuns]

theorem root (phase : Phase) (p : prover.Publication)
    (h : PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_ActualRun.runs phase) p) :
    (PV_RunJoin_ActualRun.plans phase).root=bytes p.root.val := by
  obtain ⟨out,ho,hv⟩ := PV_RunJoin_CloneBytes43.complete (Array.to_slice p.root)
  change PV_RunJoin_ActualPlanSources59.publicationBytes phase _=bytes p.root.val
  have hf : (do let slice ← Aeneas.Std.lift (Array.to_slice p.root)
                alloc.slice.Slice.to_vec core.clone.CloneU8 slice)=ok out := by
    simpa only [lift,bind_tc_ok] using ho
  rw [PV_RunJoin_ActualPublication60.projection phase p h _ out hf]
  exact congrArg bytes hv

theorem semantic (phase : Phase) (p : prover.Publication) (out : alloc.vec.Vec U8)
    (h : PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_ActualRun.runs phase) p)
    (hs : host_compact.compact_semantic (alloc.vec.Vec.deref p.semantic_bytes)
      PV_RunJoin_ActualPlanSources59.empty=ok (.Ok (),out)) :
    (PV_RunJoin_ActualRun.plans phase).semantic=bytes out.val := by
  apply PV_RunJoin_ActualPublication60.projection phase p h
  simp only [PV_RunJoin_ActualPlanSources59.compactSemantic,hs,bind_tc_ok]

theorem claim (phase : Phase) (p : prover.Publication) (out : alloc.vec.Vec U8)
    (h : PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_ActualRun.runs phase) p)
    (hs : host_compact.compact_values (alloc.vec.Vec.deref p.y1)
      PV_RunJoin_ActualPlanSources59.empty=ok (.Ok (),out)) :
    (PV_RunJoin_ActualRun.plans phase).claim=bytes out.val := by
  apply PV_RunJoin_ActualPublication60.projection phase p h
  simp only [PV_RunJoin_ActualPlanSources59.compactClaim,hs,bind_tc_ok]

#print axioms root
#print axioms semantic
#print axioms claim
end R1Z.PV_RunJoin_ActualPlanProjection60
