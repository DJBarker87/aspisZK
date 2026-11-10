-- PCVS_ item (1): E32 discharged at the deployed instance (inact := NJC_ClosedCalls.inactive, mk := NHV_ReleaseOps.mark).
-- deployed_tx2_common_s / deployed_tx2_authenticated_s: the q6 theorems with the hypothesis hE removed.
import Aeneas
import PRVEq_E32_s4
import PRVEq_Tx2Deployed_q6
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVS_Tx2Deployed
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1 PCVN_Tx2Deployed PCVQ_Resumeq13 PCVQ_Tx2Deployedq5 PCVQ_Tx2Deployed6

section
variable {F CE : Type} (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
  (geo : Port3_NativeGeometryBody.Ops CE) (base : VTop_Stages.Ops)
  (finish : AspisR1Stage2.Stage2Finish.FinishOps F)

theorem e32_deployed :
    E32 (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish) := by
  intro b
  rw [slot_op2]
  apply PCVS_E32.e32_core
  have := b.property
  simpa [Array.to_slice] using this

theorem deployed_tx2_common_s
    {H : Type} (inst : aspis_core.digest.Digest32 H) (public_bytes proof checkpoint : Slice Std.U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    verifier.candidate.tx2_common (xdep (yDep reserved (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish)) (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish))
        inst public_bytes proof checkpoint hash obs =
      VTop_Stages.verifier.candidate.tx2_common (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish) inst public_bytes proof checkpoint hash obs :=
  deployed_tx2_common_q NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish (e32_deployed reserved query geo base finish) inst public_bytes proof checkpoint hash obs

theorem deployed_tx2_authenticated_s
    {H : Type} (inst : aspis_core.digest.Digest32 H) (public_bytes proof checkpoint : Slice Std.U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    verifier.candidate.tx2_authenticated (xdep (yDep reserved (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish)) (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish))
        inst public_bytes proof checkpoint hash obs =
      VTop_Stages.verifier.candidate.tx2_authenticated (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish) inst public_bytes proof checkpoint hash obs :=
  deployed_tx2_authenticated_q NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish (e32_deployed reserved query geo base finish) inst public_bytes proof checkpoint hash obs
end

#print axioms e32_deployed
#print axioms deployed_tx2_common_s
#print axioms deployed_tx2_authenticated_s
end PCVS_Tx2Deployed
