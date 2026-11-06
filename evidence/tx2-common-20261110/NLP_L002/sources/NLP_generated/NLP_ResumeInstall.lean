import NLB_ResumePacket
import NKU_ParentFold
import NKU_CallerScope
set_option autoImplicit false
noncomputable section
namespace NLP_ResumeInstall
open Aeneas Aeneas.Std Result VTop_Stages AspisR1
/-- Concrete CLOSED resume child, initialized with the SAME invocation frame. -/
def native : NLB_ResumePacket.Native :=
 fun r {H} d ck proof pub hash => NKU_ParentFold.G d hash
  (NKU.initial ⟨ck,proof,pub,r⟩)
theorem packet (r : NP6_StdModel.Reservation) {H : Type}
 (d : aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H) :
 NLB_ResumePacket.At native r d ck proof pub hash :=
 NKU_ParentFold.source (NJC_ResumeCalls.digest d) hash (NKU.initial ⟨ck,proof,pub,r⟩)
/-- Native scope is explicit; the broader source equation does not widen it. -/
theorem scope (r : NP6_StdModel.Reservation) (ck proof pub : Slice U8)
 (proofLength : proof.val.length=57607) (publicLength : pub.val.length≤1880) :
 NKU_CallerScope.Inputs (NKU.initial ⟨ck,proof,pub,r⟩).frame :=
 ⟨proofLength,publicLength⟩
theorem action (r : NP6_StdModel.Reservation) {H : Type}
 (d : aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H) :
 NLB_ResumePacket.action native r d ck proof pub hash=
 NJJ_Common.resume r d ck proof pub .S2 hash :=
 NLB_ResumePacket.projection native r d ck proof pub hash (packet r d ck proof pub hash)
#print native
#print packet
#print scope
#print action
#print axioms packet
#print axioms scope
#print axioms action
end NLP_ResumeInstall
