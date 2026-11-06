import NLB_EnteredTransport
set_option autoImplicit false
noncomputable section
namespace NLB_ErrorTransport
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- The actual resume and Try bind equations derive C04's complete inherited
Prepared domain. These are internal branch equations, never parent premises. -/
theorem at_branch (wr : NP6_StdModel.Reservation) {H : Type}
 (d : aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
 (reply : core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (call : NJJ_Common.resume wr d ck proof pub .S2 hash=ok reply)
 (branch : core.result.Result.Insts.CoreOpsTry.branch reply=
  ok (core.ops.control_flow.ControlFlow.Continue (p,a)))
 (passed : ¬(a.next != NHT_Constants.compact.SPLIT)=true) :
 MerkleDomain wr d ck proof pub hash proof p := by
 have returned:=NKO_Branch.continued _ reply (p,a) call branch
 exact ⟨rfl,a,returned,split_start a passed,NKE_ResumeWidth.returned wr d ck proof pub hash p a returned⟩
#print axioms at_branch
end NLB_ErrorTransport
