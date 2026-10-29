import R1Z.PV_RunJoin_ActualPlanProjection60
import R1Z.PV_RunJoin_CompactSize39
import R1Z.PV_RunJoin_HighDomain40
import R1Z.PV_RJN_Bytes
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FinishClaim63
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_PublishSkeleton54
variable [ExternalTypes] [ExternalFuns]

/-- Primitive byte-domain producer conditions suffice for the complete claim
append. They are not installed as assumptions of the run or the endpoint. -/
theorem complete (phase : PV_RunJoin_NativeControl55.Phase) (p : prover.Publication)
    (context : PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_ActualRun.runs phase) p)
    (n : Nat) (length : p.y1.length=32*n)
    (high : PV_RunJoin_HighDomain40.HighZero p.y1.val) :
    ∀ out : alloc.vec.Vec U8,
      out.length+(PV_RunJoin_ActualRun.plans phase).claim.length≤Usize.max →
      ∃ next, host_compact.compact_values (alloc.vec.Vec.deref p.y1) out=ok (.Ok (),next) ∧
        bytes next.val=bytes out.val++(PV_RunJoin_ActualRun.plans phase).claim := by
  have cap : 16*n≤Usize.max := by have h := p.y1.property;change p.y1.length≤Usize.max at h;omega
  have reads := PV_RunJoin_HighDomain40.reads (alloc.vec.Vec.deref p.y1) high
  obtain ⟨zeroOut,hzero,vzero,lzero⟩ := PV_RunJoin_CompactSize39.encode
    (alloc.vec.Vec.deref p.y1) PV_RunJoin_ActualPlanSources59.empty n length
      (by change 0+16*n≤Usize.max;omega) reads
  have plan := PV_RunJoin_ActualPlanProjection60.claim phase p zeroOut context hzero
  have planLength : (PV_RunJoin_ActualRun.plans phase).claim.length=16*n := by
    rw [plan,PV_RJN_Bytes.length]
    change zeroOut.length=16*n
    simpa only [PV_RunJoin_ActualPlanSources59.empty,Nat.zero_add] using lzero
  intro out room
  rw [planLength] at room
  obtain ⟨next,hn,hv,hlen⟩ := PV_RunJoin_CompactSize39.encode
    (alloc.vec.Vec.deref p.y1) out n length room reads
  refine ⟨next,hn,?_⟩
  rw [hv,PV_RJN_Bytes.append,plan,vzero]
  rfl

#print axioms complete
end R1Z.PV_RunJoin_FinishClaim63
