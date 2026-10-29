import R1Z.PV_RunJoin_PublishProduced60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualPublication60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_PublishSkeleton54
variable [ExternalTypes] [ExternalFuns]

theorem returned (phase : Phase) (p : prover.Publication)
    (h : PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_ActualRun.runs phase) p) :
    PV_RunJoin_ActualRunSources59.finish phase=ok (.Ok p) := by
  obtain ⟨prepared,salts,hp,hs,hf⟩ := h
  exact PV_RunJoin_ActualRunSources59.finish_return phase prepared salts p hp hs hf

theorem unique (phase : Phase) (p q : prover.Publication)
    (hp : PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_ActualRun.runs phase) p)
    (hq : PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_ActualRun.runs phase) q) : p=q := by
  have h := Result.ok.inj ((returned phase p hp).symm.trans (returned phase q hq))
  exact core.result.Result.Ok.inj h

theorem projection (phase : Phase) (p : prover.Publication)
    (h : PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_ActualRun.runs phase) p)
    (f : prover.Publication → Result (alloc.vec.Vec U8)) (out : alloc.vec.Vec U8)
    (hf : f p=ok out) :
    PV_RunJoin_ActualPlanSources59.publicationBytes phase f=bytes out.val := by
  simp only [PV_RunJoin_ActualPlanSources59.publicationBytes,returned phase p h,hf]

#print axioms returned
#print axioms unique
#print axioms projection
end R1Z.PV_RunJoin_ActualPublication60
